//! Polytope preprocessing for the tube algorithm.
//!
//! This module computes:
//! - Vertex enumeration (4D vertex enumeration for H-rep polytopes)
//! - 2-face enumeration and adjacency
//! - Trivialization data for each non-Lagrangian 2-face

use nalgebra::Vector4;

use crate::constants::{EPS, EPS_LAGRANGIAN, MIN_POLYGON_AREA};
use crate::geometry::sort_ccw;
use crate::quaternion::{reeb_vector, symplectic_form};
use crate::trivialization::{
    compute_entry_basis, compute_exit_basis, compute_transition_matrix_basis,
    rotation_number_from_trace, trivialize,
};
use crate::types::{
    validate_for_tube, Polygon2D, PolytopeHRep, ThreeFacetData, TubeError, TwoFaceData,
    TwoFaceLookup,
};

/// Preprocessed polytope data for the tube algorithm.
#[derive(Debug, Clone)]
pub struct PolytopeData {
    /// Number of facets.
    pub num_facets: usize,
    /// Unit outward normals.
    pub normals: Vec<Vector4<f64>>,
    /// Heights (distance from origin to facet).
    pub heights: Vec<f64>,
    /// Reeb vectors: R_i = (2/h_i) * J * n_i.
    pub reeb_vectors: Vec<Vector4<f64>>,
    /// 4D vertices of the polytope.
    pub vertices: Vec<Vector4<f64>>,

    /// Whether the polytope has any Lagrangian 2-faces.
    has_lagrangian: bool,

    /// 2-face data indexed by 2-face index.
    pub two_face_data: Vec<TwoFaceData>,
    /// Transition data indexed by transition index.
    pub transitions: Vec<ThreeFacetData>,
    /// Lookup tables for index conversion and adjacency.
    pub lookup: TwoFaceLookup,
}

impl PolytopeData {
    /// Get the Reeb vector for facet i.
    #[inline]
    pub fn reeb_vector(&self, i: usize) -> &Vector4<f64> {
        &self.reeb_vectors[i]
    }

    /// Get the normal for facet i.
    #[inline]
    pub fn normal(&self, i: usize) -> &Vector4<f64> {
        &self.normals[i]
    }

    /// Get the height for facet i.
    #[inline]
    pub fn height(&self, i: usize) -> f64 {
        self.heights[i]
    }

    /// Check if the polytope has any Lagrangian 2-faces.
    #[inline]
    pub fn has_lagrangian_two_faces(&self) -> bool {
        self.has_lagrangian
    }

    /// Get 2-face data by index.
    #[inline]
    pub fn get_two_face(&self, k: usize) -> &TwoFaceData {
        &self.two_face_data[k]
    }

    /// Get transition data by index.
    #[inline]
    pub fn get_transition(&self, m: usize) -> &ThreeFacetData {
        &self.transitions[m]
    }

    /// Get 2-face index for facet pair (i, j).
    #[inline]
    pub fn two_face_index(&self, i: usize, j: usize) -> Option<usize> {
        self.lookup.get_two_face(i, j)
    }

    /// Get transitions starting from 2-face k.
    #[inline]
    pub fn transitions_from(&self, k: usize) -> &[usize] {
        self.lookup.transitions_from(k)
    }
}

/// Preprocess a polytope for the tube algorithm.
///
/// Computes vertices, 2-faces, and trivialization data.
pub fn preprocess(hrep: &PolytopeHRep) -> Result<PolytopeData, TubeError> {
    validate_for_tube(hrep)?;

    let num_facets = hrep.num_facets();
    let normals = hrep.normals.clone();
    let heights = hrep.heights.clone();

    // Compute Reeb vectors
    let reeb_vectors: Vec<Vector4<f64>> = normals
        .iter()
        .zip(&heights)
        .map(|(n, &h)| reeb_vector(n, h))
        .collect();

    // Vertex enumeration (simplified: find vertices as intersections of 4 facets)
    let vertices = enumerate_vertices_4d(hrep)?;

    // Find all 2-faces and check for Lagrangian ones
    let (raw_two_faces, has_lagrangian) = enumerate_two_faces_raw(hrep, &vertices);

    // Build TwoFaceData for non-Lagrangian 2-faces
    let (two_face_data, mut lookup) =
        build_two_face_data_direct(&raw_two_faces, &normals, &vertices, num_facets)?;

    // Build transitions
    let transitions = build_transitions(&two_face_data, &mut lookup, &reeb_vectors, &heights);

    Ok(PolytopeData {
        num_facets,
        normals,
        heights,
        reeb_vectors,
        vertices,
        has_lagrangian,
        two_face_data,
        transitions,
        lookup,
    })
}

/// Enumerate vertices of a 4D polytope in H-representation.
///
/// A vertex is the intersection of exactly 4 facets (for simple polytopes).
/// We check all 4-subsets of facets and solve the linear system.
fn enumerate_vertices_4d(hrep: &PolytopeHRep) -> Result<Vec<Vector4<f64>>, TubeError> {
    use nalgebra::Matrix4;

    let n = hrep.num_facets();
    let mut vertices = Vec::new();

    // Check all 4-subsets of facets
    for i in 0..n {
        for j in (i + 1)..n {
            for k in (j + 1)..n {
                for l in (k + 1)..n {
                    // Build system: [n_i; n_j; n_k; n_l] * x = [h_i; h_j; h_k; h_l]
                    let m = Matrix4::from_rows(&[
                        hrep.normals[i].transpose(),
                        hrep.normals[j].transpose(),
                        hrep.normals[k].transpose(),
                        hrep.normals[l].transpose(),
                    ]);

                    if let Some(m_inv) = m.try_inverse() {
                        let h = Vector4::new(
                            hrep.heights[i],
                            hrep.heights[j],
                            hrep.heights[k],
                            hrep.heights[l],
                        );
                        let candidate = m_inv * h;

                        // Check if candidate satisfies all constraints
                        let is_valid = hrep
                            .normals
                            .iter()
                            .zip(&hrep.heights)
                            .all(|(n, &h)| n.dot(&candidate) <= h + EPS);

                        if is_valid {
                            // Check it's not a duplicate
                            let is_dup = vertices
                                .iter()
                                .any(|v: &Vector4<f64>| (v - candidate).norm() < EPS);
                            if !is_dup {
                                vertices.push(candidate);
                            }
                        }
                    }
                }
            }
        }
    }

    if vertices.is_empty() {
        return Err(TubeError::InvalidPolytope(
            "No vertices found (polytope may be unbounded or empty)".to_string(),
        ));
    }

    Ok(vertices)
}

/// Raw 2-face data before trivialization.
struct RawTwoFace {
    i: usize,
    j: usize,
    vertex_indices: Vec<usize>,
    omega_ij: f64,
}

/// Enumerate all 2-faces (intersections of adjacent facet pairs).
/// Returns (raw 2-faces, has_lagrangian).
fn enumerate_two_faces_raw(
    hrep: &PolytopeHRep,
    vertices: &[Vector4<f64>],
) -> (Vec<RawTwoFace>, bool) {
    let n = hrep.num_facets();
    let mut two_faces = Vec::new();
    let mut has_lagrangian = false;

    for i in 0..n {
        for j in (i + 1)..n {
            // Find vertices on both facets
            let vertex_indices: Vec<usize> = vertices
                .iter()
                .enumerate()
                .filter(|(_, v)| {
                    let on_i = (hrep.normals[i].dot(v) - hrep.heights[i]).abs() < EPS;
                    let on_j = (hrep.normals[j].dot(v) - hrep.heights[j]).abs() < EPS;
                    on_i && on_j
                })
                .map(|(idx, _)| idx)
                .collect();

            // A 2-face needs at least 3 vertices
            if vertex_indices.len() >= 3 {
                let omega_ij = symplectic_form(&hrep.normals[i], &hrep.normals[j]);

                if omega_ij.abs() < EPS_LAGRANGIAN {
                    has_lagrangian = true;
                }

                two_faces.push(RawTwoFace {
                    i,
                    j,
                    vertex_indices,
                    omega_ij,
                });
            }
        }
    }

    (two_faces, has_lagrangian)
}

/// Build TwoFaceData list directly from raw 2-faces.
fn build_two_face_data_direct(
    raw_two_faces: &[RawTwoFace],
    normals: &[Vector4<f64>],
    vertices: &[Vector4<f64>],
    num_facets: usize,
) -> Result<(Vec<TwoFaceData>, TwoFaceLookup), TubeError> {
    let mut data = Vec::new();
    let mut lookup = TwoFaceLookup::new(num_facets);

    for tf in raw_two_faces {
        // Skip Lagrangian 2-faces
        if tf.omega_ij.abs() < EPS_LAGRANGIAN {
            continue;
        }

        // Determine entry and exit facets based on flow direction (sign of omega)
        let (entry_facet, exit_facet, entry_normal, exit_normal) = if tf.omega_ij > 0.0 {
            // ItoJ: flow from i to j
            (tf.i, tf.j, normals[tf.i], normals[tf.j])
        } else {
            // JtoI: flow from j to i
            (tf.j, tf.i, normals[tf.j], normals[tf.i])
        };

        // Compute basis vectors
        let basis_exit = compute_exit_basis(&entry_normal, &exit_normal)
            .map_err(|e| TubeError::NumericalInstability(e.to_string()))?;
        let basis_entry = compute_entry_basis(&entry_normal, &exit_normal)
            .map_err(|e| TubeError::NumericalInstability(e.to_string()))?;

        // Compute rotation number from transition matrix trace
        let transition_matrix = compute_transition_matrix_basis(&basis_entry, &exit_normal);
        let rotation = rotation_number_from_trace(transition_matrix.trace());

        // Get 4D vertices and compute centroid
        let vertices_4d: Vec<Vector4<f64>> =
            tf.vertex_indices.iter().map(|&i| vertices[i]).collect();
        let centroid_4d: Vector4<f64> =
            vertices_4d.iter().sum::<Vector4<f64>>() / vertices_4d.len() as f64;

        // Trivialize vertices using exit normal (CH2021 convention)
        let polygon_2d_verts: Vec<nalgebra::Vector2<f64>> = vertices_4d
            .iter()
            .map(|v| trivialize(&exit_normal, &(v - centroid_4d)))
            .collect();

        // Sort CCW
        let polygon = Polygon2D::new(sort_ccw(polygon_2d_verts));

        let k = data.len();
        let two_face_data = TwoFaceData {
            entry_facet,
            exit_facet,
            omega: tf.omega_ij.abs(),
            rotation,
            polygon,
            centroid_4d,
            basis_exit,
            entry_normal,
            exit_normal,
        };

        // Validate TwoFaceData invariants in debug builds
        debug_assert!(
            two_face_data.entry_facet != two_face_data.exit_facet,
            "2-face {}: entry_facet ({}) == exit_facet ({})",
            k,
            two_face_data.entry_facet,
            two_face_data.exit_facet
        );
        debug_assert!(
            two_face_data.polygon.vertices.len() >= 3,
            "2-face {}: polygon has {} vertices (need >= 3)",
            k,
            two_face_data.polygon.vertices.len()
        );
        debug_assert!(
            two_face_data.polygon.area() >= MIN_POLYGON_AREA,
            "2-face {}: polygon area {:.2e} < MIN_POLYGON_AREA ({:.2e})",
            k,
            two_face_data.polygon.area(),
            MIN_POLYGON_AREA
        );
        // Validate that each 2D polygon vertex reconstructs to a 4D point on both facets
        #[cfg(debug_assertions)]
        for (v_idx, v_2d) in two_face_data.polygon.vertices.iter().enumerate() {
            let p_4d = two_face_data.centroid_4d
                + v_2d[0] * two_face_data.basis_exit[0]
                + v_2d[1] * two_face_data.basis_exit[1];
            let entry_residual =
                (two_face_data.entry_normal.dot(&p_4d) - vertices[tf.vertex_indices[0]].dot(&entry_normal)).abs();
            let exit_residual =
                (two_face_data.exit_normal.dot(&p_4d) - vertices[tf.vertex_indices[0]].dot(&exit_normal)).abs();
            debug_assert!(
                entry_residual < EPS,
                "2-face {} vertex {}: reconstructed point not on entry facet (residual = {:.2e})",
                k,
                v_idx,
                entry_residual
            );
            debug_assert!(
                exit_residual < EPS,
                "2-face {} vertex {}: reconstructed point not on exit facet (residual = {:.2e})",
                k,
                v_idx,
                exit_residual
            );
        }

        data.push(two_face_data);

        lookup.register_two_face(tf.i, tf.j, k);
    }

    // Initialize transitions_from with empty vecs
    lookup.transitions_from = vec![Vec::new(); data.len()];

    Ok((data, lookup))
}

/// Build ThreeFacetData list for all valid transitions.
///
/// A transition (i, j, k) is valid if:
/// - (i, j) and (j, k) are both non-Lagrangian 2-faces
/// - Flow goes from i → j on (i, j) and from j → k on (j, k)
fn build_transitions(
    two_faces: &[TwoFaceData],
    lookup: &mut TwoFaceLookup,
    reeb_vectors: &[Vector4<f64>],
    heights: &[f64],
) -> Vec<ThreeFacetData> {
    use crate::quaternion::{apply_quat_j, apply_quat_k};
    use nalgebra::{Matrix2, Vector2};

    let mut transitions = Vec::new();

    for (k_entry, tf_entry) in two_faces.iter().enumerate() {
        // Find all 2-faces that have tf_entry.exit_facet as their entry facet
        for (k_exit, tf_exit) in two_faces.iter().enumerate() {
            if tf_exit.entry_facet == tf_entry.exit_facet {
                // Valid transition found
                let facet_mid = tf_entry.exit_facet;

                // Compute the affine flow map for this transition
                let r_mid = &reeb_vectors[facet_mid];
                let n_next = &tf_exit.exit_normal;
                let h_next = heights[tf_exit.exit_facet];

                let b_entry = &tf_entry.basis_exit;
                let c_entry = tf_entry.centroid_4d;
                let c_exit = tf_exit.centroid_4d;

                // Trivialization vectors for exit 2-face
                let jn_exit = apply_quat_j(n_next);
                let kn_exit = apply_quat_k(n_next);

                // Denominator: ⟨R_mid, n_next⟩
                let r_dot_n = r_mid.dot(n_next);

                // Time function: t(p) = t_const + ⟨t_grad, p⟩
                let t_const = (h_next - c_entry.dot(n_next)) / r_dot_n;
                let t_grad = Vector2::new(
                    -b_entry[0].dot(n_next) / r_dot_n,
                    -b_entry[1].dot(n_next) / r_dot_n,
                );

                // Transition matrix ψ: trivialize entry basis in exit coordinates
                let psi = Matrix2::new(
                    b_entry[0].dot(&jn_exit),
                    b_entry[1].dot(&jn_exit),
                    b_entry[0].dot(&kn_exit),
                    b_entry[1].dot(&kn_exit),
                );

                // Reeb vector in exit-trivialized coordinates
                let r_triv = Vector2::new(r_mid.dot(&jn_exit), r_mid.dot(&kn_exit));

                // Full flow matrix: A = ψ + r_triv ⊗ t_grad
                let flow_matrix = psi + r_triv * t_grad.transpose();

                // Flow offset: b = τ_exit(c_entry - c_exit + t_const * R_mid)
                let delta_c = c_entry - c_exit + r_mid * t_const;
                let flow_offset = Vector2::new(delta_c.dot(&jn_exit), delta_c.dot(&kn_exit));

                let trans_idx = transitions.len();
                transitions.push(ThreeFacetData {
                    two_face_entry: k_entry,
                    two_face_exit: k_exit,
                    facet_mid,
                    flow_matrix,
                    flow_offset,
                    time_gradient: t_grad,
                    time_constant: t_const,
                });

                lookup.transitions_from[k_entry].push(trans_idx);
            }
        }
    }

    transitions
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixtures::{random_hrep, unit_cross_polytope, unit_tesseract};
    use proptest::prelude::*;

    // =========================================================================
    // Fixture-based tests for specific polytopes (cross-polytope, tesseract)
    // =========================================================================

    #[test]
    fn test_preprocess_cross_polytope() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        // Cross-polytope has 16 facets
        assert_eq!(data.num_facets, 16);

        // Cross-polytope has 8 vertices
        assert_eq!(data.vertices.len(), 8);

        // Check vertices are at +/-e_i
        for v in &data.vertices {
            // Exactly one coordinate should be +/-1, rest should be 0
            let non_zero_count = (0..4).filter(|&i| v[i].abs() > 0.5).count();
            assert_eq!(
                non_zero_count, 1,
                "Vertex {:?} should have one non-zero coordinate",
                v
            );
        }
    }

    /// T1: Each vertex lies on at least 4 facets (4D polytope property).
    ///
    /// In 4D, a vertex is the intersection of at least 4 half-spaces.
    /// Simple polytopes have exactly 4, but non-simple polytopes (like the
    /// cross-polytope) can have more.
    #[test]
    fn test_vertex_facet_incidence_fixtures() {
        // Tesseract: simple polytope, exactly 4 facets per vertex
        let tesseract = unit_tesseract();
        let vertices = enumerate_vertices_4d(&tesseract).unwrap();

        for (v_idx, v) in vertices.iter().enumerate() {
            let mut incident_facets = 0;
            for (n, &h) in tesseract.normals.iter().zip(&tesseract.heights) {
                if (n.dot(v) - h).abs() < EPS {
                    incident_facets += 1;
                }
            }
            assert_eq!(
                incident_facets, 4,
                "tesseract: vertex {} lies on {} facets (expected 4 for simple polytope)",
                v_idx, incident_facets
            );
        }

        // Cross-polytope: non-simple, 8 facets per vertex
        let cross = unit_cross_polytope();
        let vertices = enumerate_vertices_4d(&cross).unwrap();

        for (v_idx, v) in vertices.iter().enumerate() {
            let mut incident_facets = 0;
            for (n, &h) in cross.normals.iter().zip(&cross.heights) {
                if (n.dot(v) - h).abs() < EPS {
                    incident_facets += 1;
                }
            }
            assert!(
                incident_facets >= 4,
                "cross_polytope: vertex {} lies on {} facets (need >= 4)",
                v_idx,
                incident_facets
            );
            // Cross-polytope specifically has 8 facets per vertex
            assert_eq!(
                incident_facets, 8,
                "cross_polytope: vertex {} lies on {} facets (expected 8)",
                v_idx, incident_facets
            );
        }
    }

    /// T2 (fixture): Cross-polytope 2-faces are triangles (3 vertices each).
    #[test]
    fn test_cross_polytope_two_face_triangles() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        for (k, tf) in data.two_face_data.iter().enumerate() {
            assert_eq!(
                tf.polygon.vertices.len(),
                3,
                "Cross-polytope 2-face {} should be a triangle, got {} vertices",
                k,
                tf.polygon.vertices.len()
            );
        }
    }

    // =========================================================================
    // Property-based tests with random polytopes
    // =========================================================================

    /// Minimum omega for random polytopes (safety margin for numerical stability).
    const MIN_OMEGA: f64 = 0.01;

    proptest! {
        /// All 2-faces should have positive omega (non-Lagrangian).
        #[test]
        fn prop_two_faces_positive_omega(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for tf in &data.two_face_data {
                    prop_assert!(
                        tf.omega > EPS_LAGRANGIAN,
                        "2-face ({} -> {}) has omega = {:.2e} (should be positive)",
                        tf.entry_facet, tf.exit_facet, tf.omega
                    );
                }
            }
        }

        /// Rotation should be in (0, 0.5) for all 2-faces.
        #[test]
        fn prop_rotation_in_valid_range(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for tf in &data.two_face_data {
                    prop_assert!(
                        tf.rotation > 0.0 && tf.rotation < 0.5,
                        "Rotation {} not in (0, 0.5)",
                        tf.rotation
                    );
                    prop_assert!(!tf.polygon.is_empty(), "Polygon should not be empty");
                }
            }
        }

        /// Lookup tables should correctly find all 2-faces.
        #[test]
        fn prop_lookup_consistency(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for (k, tf) in data.two_face_data.iter().enumerate() {
                    let found = data.lookup.get_two_face(tf.entry_facet, tf.exit_facet);
                    prop_assert_eq!(found, Some(k), "Lookup should find 2-face {}", k);

                    // Reverse lookup should also work
                    let found_rev = data.lookup.get_two_face(tf.exit_facet, tf.entry_facet);
                    prop_assert_eq!(found_rev, Some(k));
                }
            }
        }

        /// Transitions should connect 2-faces correctly.
        #[test]
        fn prop_transitions_valid(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for trans in &data.transitions {
                    // Entry and exit 2-faces should be valid indices
                    prop_assert!(trans.two_face_entry < data.two_face_data.len());
                    prop_assert!(trans.two_face_exit < data.two_face_data.len());

                    // Exit facet of entry 2-face should equal entry facet of exit 2-face
                    let tf_entry = &data.two_face_data[trans.two_face_entry];
                    let tf_exit = &data.two_face_data[trans.two_face_exit];
                    prop_assert_eq!(
                        tf_entry.exit_facet, tf_exit.entry_facet,
                        "Transition should connect at shared facet"
                    );
                    prop_assert_eq!(tf_entry.exit_facet, trans.facet_mid);
                }

                // Check adjacency structure
                for k in 0..data.two_face_data.len() {
                    let trans_indices = data.lookup.transitions_from(k);
                    for &trans_idx in trans_indices {
                        prop_assert_eq!(data.transitions[trans_idx].two_face_entry, k);
                    }
                }
            }
        }

        /// Flow matrices should be symplectic (det = 1).
        #[test]
        fn prop_flow_matrices_symplectic(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for trans in &data.transitions {
                    let det = trans.flow_matrix.determinant();
                    prop_assert!(
                        (det - 1.0).abs() < 0.01,
                        "Transition {} -> {}: det = {} (expected 1.0)",
                        trans.two_face_entry, trans.two_face_exit, det
                    );
                }
            }
        }

        /// T1: Each vertex lies on at least 4 facets (4D polytope property).
        #[test]
        fn prop_vertex_facet_incidence(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for (v_idx, v) in data.vertices.iter().enumerate() {
                    let mut incident_facets = 0;
                    for (n, &h) in hrep.normals.iter().zip(&hrep.heights) {
                        if (n.dot(v) - h).abs() < EPS {
                            incident_facets += 1;
                        }
                    }
                    prop_assert!(
                        incident_facets >= 4,
                        "vertex {} lies on {} facets (need >= 4 for 4D polytope)",
                        v_idx, incident_facets
                    );
                }
            }
        }

        /// T2: Each 2-face polygon should have >= 3 vertices.
        #[test]
        fn prop_two_face_vertex_count(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for (k, tf) in data.two_face_data.iter().enumerate() {
                    let n_verts = tf.polygon.vertices.len();
                    prop_assert!(
                        n_verts >= 3,
                        "2-face {} has {} vertices (need >= 3 for polygon)",
                        k, n_verts
                    );
                }
            }
        }

        /// T3: Transition graph is connected (all non-Lagrangian 2-faces reachable).
        #[test]
        fn prop_transition_graph_connected(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                if data.two_face_data.is_empty() {
                    return Ok(()); // Vacuously true
                }

                // BFS from first 2-face
                let n_two_faces = data.two_face_data.len();
                let mut visited = vec![false; n_two_faces];
                let mut queue = std::collections::VecDeque::new();
                queue.push_back(0);
                visited[0] = true;

                while let Some(k) = queue.pop_front() {
                    for &trans_idx in data.lookup.transitions_from(k) {
                        let exit_k = data.transitions[trans_idx].two_face_exit;
                        if !visited[exit_k] {
                            visited[exit_k] = true;
                            queue.push_back(exit_k);
                        }
                    }
                }

                let reachable_count = visited.iter().filter(|&&v| v).count();
                prop_assert_eq!(
                    reachable_count, n_two_faces,
                    "Only {} of {} 2-faces reachable from 2-face 0 (graph not connected)",
                    reachable_count, n_two_faces
                );
            }
        }

        /// T4: Transition composition along closed facet path has det = 1.
        #[test]
        fn prop_transition_composition_det_1(seed in 0u64..5000) {
            use nalgebra::Matrix2;

            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                // Find a closed path starting from some 2-face
                for start_k in 0..data.two_face_data.len().min(5) {
                    let mut composed = Matrix2::identity();
                    let mut current_k = start_k;
                    let mut path_len = 0;
                    let max_path_len = 20;

                    while path_len < max_path_len {
                        let trans_indices = data.lookup.transitions_from(current_k);
                        if trans_indices.is_empty() {
                            break;
                        }

                        // Take first available transition
                        let trans = &data.transitions[trans_indices[0]];
                        composed = trans.flow_matrix * composed;
                        current_k = trans.two_face_exit;
                        path_len += 1;

                        if current_k == start_k && path_len > 0 {
                            // Found a cycle
                            let det = composed.determinant();
                            prop_assert!(
                                (det - 1.0).abs() < 0.01,
                                "Cycle from 2-face {} (len {}) has det = {} (expected 1.0)",
                                start_k, path_len, det
                            );
                            break;
                        }
                    }
                }
            }
        }

        /// T5: Flow map preserves containment (centroid maps near exit polygon).
        #[test]
        fn prop_flow_map_preserves_containment(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for trans in &data.transitions {
                    let entry_tf = &data.two_face_data[trans.two_face_entry];
                    let exit_tf = &data.two_face_data[trans.two_face_exit];

                    let entry_centroid = entry_tf.polygon.centroid();
                    let mapped = trans.flow_matrix * entry_centroid + trans.flow_offset;

                    let exit_centroid = exit_tf.polygon.centroid();
                    let dist = (mapped - exit_centroid).norm();

                    let exit_diameter: f64 = exit_tf
                        .polygon
                        .vertices
                        .iter()
                        .map(|v| (v - exit_centroid).norm())
                        .fold(0.0, f64::max)
                        * 2.0;

                    prop_assert!(
                        dist < exit_diameter * 5.0,
                        "Transition {} -> {}: mapped centroid too far from exit polygon \
                         (dist = {:.4}, diameter = {:.4})",
                        trans.two_face_entry, trans.two_face_exit, dist, exit_diameter
                    );
                }
            }
        }

        /// T6: Basis vectors are perpendicular to both entry and exit normals.
        #[test]
        fn prop_basis_in_tangent_space(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for (k, tf) in data.two_face_data.iter().enumerate() {
                    let b1 = &tf.basis_exit[0];
                    let b2 = &tf.basis_exit[1];
                    let n_entry = &tf.entry_normal;
                    let n_exit = &tf.exit_normal;

                    prop_assert!(
                        b1.dot(n_entry).abs() < EPS,
                        "2-face {}: basis[0] not perpendicular to entry normal (dot = {:.2e})",
                        k, b1.dot(n_entry)
                    );
                    prop_assert!(
                        b1.dot(n_exit).abs() < EPS,
                        "2-face {}: basis[0] not perpendicular to exit normal (dot = {:.2e})",
                        k, b1.dot(n_exit)
                    );
                    prop_assert!(
                        b2.dot(n_entry).abs() < EPS,
                        "2-face {}: basis[1] not perpendicular to entry normal (dot = {:.2e})",
                        k, b2.dot(n_entry)
                    );
                    prop_assert!(
                        b2.dot(n_exit).abs() < EPS,
                        "2-face {}: basis[1] not perpendicular to exit normal (dot = {:.2e})",
                        k, b2.dot(n_exit)
                    );
                }
            }
        }

        /// T7: Polygon vertices can be reconstructed to 4D and lie on the 2-face.
        #[test]
        fn prop_polygon_vertices_on_2face(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for (k, tf) in data.two_face_data.iter().enumerate() {
                    for (v_idx, v_2d) in tf.polygon.vertices.iter().enumerate() {
                        let p_4d = tf.centroid_4d
                            + v_2d[0] * tf.basis_exit[0]
                            + v_2d[1] * tf.basis_exit[1];

                        let entry_val = tf.entry_normal.dot(&p_4d);
                        let h_entry = hrep.heights[tf.entry_facet];
                        prop_assert!(
                            (entry_val - h_entry).abs() < 1e-6,
                            "2-face {} vertex {}: not on entry facet (val = {:.6}, h = {:.6})",
                            k, v_idx, entry_val, h_entry
                        );

                        let exit_val = tf.exit_normal.dot(&p_4d);
                        let h_exit = hrep.heights[tf.exit_facet];
                        prop_assert!(
                            (exit_val - h_exit).abs() < 1e-6,
                            "2-face {} vertex {}: not on exit facet (val = {:.6}, h = {:.6})",
                            k, v_idx, exit_val, h_exit
                        );
                    }
                }
            }
        }

        /// T8: Time function is positive at all entry polygon vertices.
        #[test]
        fn prop_time_function_positive(seed in 0u64..5000) {
            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for trans in &data.transitions {
                    let entry_tf = &data.two_face_data[trans.two_face_entry];

                    for (v_idx, v) in entry_tf.polygon.vertices.iter().enumerate() {
                        let t = trans.time_constant + trans.time_gradient.dot(v);
                        prop_assert!(
                            t > -EPS,
                            "Transition {} -> {}: time at vertex {} is negative (t = {:.6})",
                            trans.two_face_entry, trans.two_face_exit, v_idx, t
                        );
                    }
                }
            }
        }

        /// T9: Symplectic form sign matches flow direction.
        #[test]
        fn prop_omega_sign_matches_flow_direction(seed in 0u64..5000) {
            use crate::quaternion::symplectic_form;

            if let Some(hrep) = random_hrep(8, MIN_OMEGA, seed) {
                let data = preprocess(&hrep).unwrap();
                prop_assume!(!data.has_lagrangian_two_faces());

                for (k, tf) in data.two_face_data.iter().enumerate() {
                    let omega = symplectic_form(&tf.entry_normal, &tf.exit_normal);
                    prop_assert!(
                        omega > 0.0,
                        "2-face {}: omega(n_entry, n_exit) = {:.6} should be positive for entry->exit flow",
                        k, omega
                    );

                    prop_assert!(
                        (tf.omega - omega.abs()).abs() < EPS,
                        "2-face {}: stored omega {:.6} doesn't match computed {:.6}",
                        k, tf.omega, omega.abs()
                    );
                }
            }
        }
    }
}
