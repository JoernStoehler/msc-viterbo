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
    validate_for_tube, FlowDirection, Polygon2D, PolytopeHRep, TubeError, TwoFace, TwoFaceEnriched,
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
    /// Basic 2-face data (all adjacent facet pairs).
    pub two_faces: Vec<TwoFace>,
    /// Enriched 2-faces (non-Lagrangian only, with trivialization data).
    pub two_faces_enriched: Vec<TwoFaceEnriched>,
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
    pub fn has_lagrangian_two_faces(&self) -> bool {
        self.two_faces
            .iter()
            .any(|f| f.is_lagrangian(EPS_LAGRANGIAN))
    }

    /// Get the enriched TwoFaceEnriched for facets i and j.
    /// Returns the one where the flow direction matches (entry=i, exit=j or vice versa).
    pub fn get_two_face_enriched(&self, entry: usize, exit: usize) -> Option<&TwoFaceEnriched> {
        self.two_faces_enriched.iter().find(|f| {
            let (a, b) = if f.i < f.j { (f.i, f.j) } else { (f.j, f.i) };
            let (e, x) = if entry < exit {
                (entry, exit)
            } else {
                (exit, entry)
            };
            a == e && b == x
        })
    }

    /// Get facets that are adjacent to the given facet.
    /// A facet j is adjacent to i if they share a non-Lagrangian 2-face
    /// AND the flow goes from i to j.
    pub fn adjacent_facets_forward(&self, i: usize) -> Vec<usize> {
        self.two_faces_enriched
            .iter()
            .filter_map(|f| {
                // Check if facet i is the entry facet for this 2-face
                if f.flow_direction == Some(FlowDirection::ItoJ) && f.i == i {
                    Some(f.j)
                } else if f.flow_direction == Some(FlowDirection::JtoI) && f.j == i {
                    Some(f.i)
                } else {
                    None
                }
            })
            .collect()
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

    // Find all 2-faces
    let two_faces = enumerate_two_faces(hrep, &vertices);

    // Enrich non-Lagrangian 2-faces
    let two_faces_enriched = enrich_two_faces(&two_faces, &normals, &vertices)?;

    Ok(PolytopeData {
        num_facets,
        normals,
        heights,
        reeb_vectors,
        vertices,
        two_faces,
        two_faces_enriched,
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

/// Enumerate all 2-faces (intersections of adjacent facet pairs).
fn enumerate_two_faces(hrep: &PolytopeHRep, vertices: &[Vector4<f64>]) -> Vec<TwoFace> {
    let n = hrep.num_facets();
    let mut two_faces = Vec::new();

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
                two_faces.push(TwoFace {
                    i,
                    j,
                    vertex_indices,
                    omega_ij,
                });
            }
        }
    }

    two_faces
}

/// Enrich 2-faces with trivialization data.
fn enrich_two_faces(
    two_faces: &[TwoFace],
    normals: &[Vector4<f64>],
    vertices: &[Vector4<f64>],
) -> Result<Vec<TwoFaceEnriched>, TubeError> {
    let mut enriched = Vec::new();

    for tf in two_faces {
        // Skip Lagrangian 2-faces (trivialization doesn't work)
        if tf.is_lagrangian(EPS_LAGRANGIAN) {
            continue;
        }

        let flow_dir = tf.flow_direction(EPS_LAGRANGIAN).unwrap();

        // Determine entry and exit normals based on flow direction
        let (entry_normal, exit_normal) = match flow_dir {
            FlowDirection::ItoJ => (normals[tf.i], normals[tf.j]),
            FlowDirection::JtoI => (normals[tf.j], normals[tf.i]),
        };

        // Compute basis vectors
        let basis_exit = compute_exit_basis(&entry_normal, &exit_normal)
            .map_err(|e| TubeError::NumericalInstability(e.to_string()))?;
        let basis_entry = compute_entry_basis(&entry_normal, &exit_normal)
            .map_err(|e| TubeError::NumericalInstability(e.to_string()))?;

        // Compute transition matrix
        let transition_matrix = compute_transition_matrix_basis(&basis_entry, &exit_normal);

        // Compute rotation number
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
        let polygon_2d = Polygon2D::new(sort_ccw(polygon_2d_verts));

        enriched.push(TwoFaceEnriched {
            i: tf.i,
            j: tf.j,
            omega_ij: tf.omega_ij,
            is_lagrangian: false,
            flow_direction: Some(flow_dir),
            entry_normal,
            exit_normal,
            transition_matrix,
            rotation,
            polygon_2d,
            vertices_4d,
            centroid_4d,
            basis_exit,
            basis_entry,
        });
    }

    Ok(enriched)
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
        for tf in &data.two_faces {
            assert!(
                tf.omega_ij.abs() > EPS_LAGRANGIAN,
                "2-face F_{},{} has ω = {:.2e} (Lagrangian)",
                tf.i,
                tf.j,
                tf.omega_ij
            );
        }

        assert!(!data.has_lagrangian_two_faces());
    }

    #[test]
    fn test_enriched_2face_properties() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        for tfe in &data.two_faces_enriched {
            // Transition matrix should be symplectic
            assert_relative_eq!(tfe.transition_matrix.determinant(), 1.0, epsilon = EPS);

            // Rotation should be in (0, 0.5)
            assert!(
                tfe.rotation > 0.0 && tfe.rotation < 0.5,
                "Rotation {} not in (0, 0.5)",
                tfe.rotation
            );

            // Polygon should be non-empty
            assert!(!tfe.polygon_2d.is_empty());
        }
    }
}
