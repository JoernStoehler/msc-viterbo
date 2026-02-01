//! Polytope preprocessing for the tube algorithm.
//!
//! This module computes:
//! - Vertex enumeration (4D vertex enumeration for H-rep polytopes)
//! - 2-face enumeration and adjacency
//! - Trivialization data for each non-Lagrangian 2-face

use nalgebra::Vector4;

use crate::constants::{EPS, EPS_LAGRANGIAN};
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
        data.push(TwoFaceData {
            entry_facet,
            exit_facet,
            omega: tf.omega_ij.abs(),
            rotation,
            polygon,
            centroid_4d,
            basis_exit,
            entry_normal,
            exit_normal,
        });

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
    use crate::fixtures::unit_cross_polytope;
    use approx::assert_relative_eq;

    #[test]
    fn test_preprocess_cross_polytope() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        // Cross-polytope has 16 facets
        assert_eq!(data.num_facets, 16);

        // Cross-polytope has 8 vertices
        assert_eq!(data.vertices.len(), 8);

        // Check vertices are at ±e_i
        for v in &data.vertices {
            // Exactly one coordinate should be ±1, rest should be 0
            let non_zero_count = (0..4).filter(|&i| v[i].abs() > 0.5).count();
            assert_eq!(
                non_zero_count, 1,
                "Vertex {:?} should have one non-zero coordinate",
                v
            );
        }
    }

    #[test]
    fn test_cross_polytope_no_lagrangian_2faces() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        // Cross-polytope should have no Lagrangian 2-faces
        assert!(!data.has_lagrangian_two_faces());

        // All 2-faces should have positive omega
        for tf in &data.two_face_data {
            assert!(
                tf.omega > EPS_LAGRANGIAN,
                "2-face ({} -> {}) has ω = {:.2e} (should be positive)",
                tf.entry_facet,
                tf.exit_facet,
                tf.omega
            );
        }
    }

    #[test]
    fn test_two_face_properties() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        for tf in &data.two_face_data {
            // Rotation should be in (0, 0.5)
            assert!(
                tf.rotation > 0.0 && tf.rotation < 0.5,
                "Rotation {} not in (0, 0.5)",
                tf.rotation
            );

            // Polygon should be non-empty
            assert!(!tf.polygon.is_empty());
        }
    }

    #[test]
    fn test_structures_consistency() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        // Lookup should find all 2-faces
        for (k, tf) in data.two_face_data.iter().enumerate() {
            let found = data.lookup.get_two_face(tf.entry_facet, tf.exit_facet);
            assert_eq!(found, Some(k), "Lookup should find 2-face {}", k);

            // Reverse lookup should also work
            let found_rev = data.lookup.get_two_face(tf.exit_facet, tf.entry_facet);
            assert_eq!(found_rev, Some(k));
        }

        // Check transitions
        for trans in &data.transitions {
            // Entry and exit 2-faces should be valid indices
            assert!(trans.two_face_entry < data.two_face_data.len());
            assert!(trans.two_face_exit < data.two_face_data.len());

            // Exit facet of entry 2-face should equal entry facet of exit 2-face
            let tf_entry = &data.two_face_data[trans.two_face_entry];
            let tf_exit = &data.two_face_data[trans.two_face_exit];
            assert_eq!(
                tf_entry.exit_facet, tf_exit.entry_facet,
                "Transition should connect at shared facet"
            );
            assert_eq!(tf_entry.exit_facet, trans.facet_mid);
        }

        // Check adjacency structure
        for k in 0..data.two_face_data.len() {
            let trans_indices = data.lookup.transitions_from(k);

            // Each transition should have this 2-face as entry
            for &trans_idx in trans_indices {
                assert_eq!(data.transitions[trans_idx].two_face_entry, k);
            }
        }

        // Check precomputed flow maps are symplectic (det = 1)
        for trans in &data.transitions {
            let det = trans.flow_matrix.determinant();
            assert_relative_eq!(det, 1.0, epsilon = 0.01);
        }
    }
}
