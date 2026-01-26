//! Polytope data structures and preprocessing.
//!
//! This module provides:
//! - `PolytopeHRep`: H-representation (half-space intersection)
//! - `TwoFace`: A 2-face (intersection of two facets)
//! - `TwoFaceEnriched`: 2-face with trivialization data
//! - `PolytopeData`: Preprocessed polytope data for the tube algorithm

use nalgebra::{Matrix2, Matrix4, Vector2, Vector4};

use crate::consts::{EPS, EPS_LAGRANGIAN, EPS_UNIT, TAU};
use crate::error::{TubeError, TubeResult};
use crate::polygon::Polygon2D;
use crate::symplectic::{apply_j, apply_k, reeb_vector, symplectic_form};
use crate::trivialization::{compute_entry_basis, compute_exit_basis, trivialize};

/// H-representation of a convex polytope K = {x : ⟨nᵢ, x⟩ ≤ hᵢ for all i}.
#[derive(Debug, Clone)]
pub struct PolytopeHRep {
    /// Unit outward normals to each facet.
    pub normals: Vec<Vector4<f64>>,
    /// Signed distance from origin to each facet (must be > 0 for 0 ∈ int(K)).
    pub heights: Vec<f64>,
}

impl PolytopeHRep {
    /// Create a new polytope from normals and heights.
    pub fn new(normals: Vec<Vector4<f64>>, heights: Vec<f64>) -> Self {
        Self { normals, heights }
    }

    /// Number of facets.
    pub fn num_facets(&self) -> usize {
        self.normals.len()
    }

    /// Validate the H-representation.
    pub fn validate(&self) -> TubeResult<()> {
        // Check lengths match
        if self.normals.len() != self.heights.len() {
            return Err(TubeError::InvalidPolytope(format!(
                "normals length ({}) != heights length ({})",
                self.normals.len(),
                self.heights.len()
            )));
        }

        // Need at least 5 facets for a valid 4D polytope
        if self.normals.len() < 5 {
            return Err(TubeError::InvalidPolytope(format!(
                "need at least 5 facets for 4D polytope, got {}",
                self.normals.len()
            )));
        }

        // Check normals are unit vectors
        for (i, n) in self.normals.iter().enumerate() {
            let norm = n.norm();
            if (norm - 1.0).abs() > EPS_UNIT {
                return Err(TubeError::InvalidPolytope(format!(
                    "normal[{}] is not unit: norm = {:.15} (expected 1.0)",
                    i, norm
                )));
            }
        }

        // Check heights are positive (origin in interior)
        for (i, &h) in self.heights.iter().enumerate() {
            if h <= 0.0 {
                return Err(TubeError::InvalidPolytope(format!(
                    "height[{}] = {:.15} is not positive (origin not in interior)",
                    i, h
                )));
            }
        }

        Ok(())
    }
}

/// Flow direction on a 2-face.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlowDirection {
    /// Flow from facet i to facet j (ω(nᵢ, nⱼ) > 0).
    ItoJ,
    /// Flow from facet j to facet i (ω(nᵢ, nⱼ) < 0).
    JtoI,
}

/// A 2-face (intersection of two facets).
#[derive(Debug, Clone)]
pub struct TwoFace {
    /// First facet index (i < j by convention).
    pub i: usize,
    /// Second facet index.
    pub j: usize,
    /// ω(nᵢ, nⱼ).
    pub omega_ij: f64,
    /// Whether this is a Lagrangian 2-face.
    pub is_lagrangian: bool,
    /// Flow direction (None for Lagrangian).
    pub flow_direction: Option<FlowDirection>,
}

impl TwoFace {
    /// Create a new 2-face.
    pub fn new(i: usize, j: usize, n_i: &Vector4<f64>, n_j: &Vector4<f64>) -> Self {
        let omega_ij = symplectic_form(n_i, n_j);
        let is_lagrangian = omega_ij.abs() < EPS_LAGRANGIAN;

        let flow_direction = if is_lagrangian {
            None
        } else if omega_ij > 0.0 {
            Some(FlowDirection::ItoJ)
        } else {
            Some(FlowDirection::JtoI)
        };

        Self {
            i,
            j,
            omega_ij,
            is_lagrangian,
            flow_direction,
        }
    }
}

/// Enriched 2-face with trivialization and transition data.
///
/// All fields are **flow-direction-aware**: entry_normal and exit_normal
/// are computed based on actual flow direction, not the i < j convention.
#[derive(Debug, Clone)]
pub struct TwoFaceEnriched {
    // Basic identification
    /// First facet index (i < j by convention).
    pub i: usize,
    /// Second facet index.
    pub j: usize,
    /// ω(nᵢ, nⱼ).
    pub omega_ij: f64,
    /// Whether this is Lagrangian.
    pub is_lagrangian: bool,
    /// Flow direction.
    pub flow_direction: Option<FlowDirection>,

    // Flow-aware normals
    /// Normal of the entry facet (where flow comes from).
    pub entry_normal: Vector4<f64>,
    /// Normal of the exit facet (where flow goes to).
    pub exit_normal: Vector4<f64>,
    /// Entry facet index.
    pub entry_facet: usize,
    /// Exit facet index.
    pub exit_facet: usize,

    // Trivialization data
    /// Transition matrix ψ = τ_{exit} ∘ τ_{entry}⁻¹ ∈ Sp(2).
    pub transition_matrix: Matrix2<f64>,
    /// Rotation number ρ ∈ (0, 0.5).
    pub rotation: f64,

    // Basis vectors for reconstruction (§1.10.1)
    /// Exit basis: vectors in TF with τ_{exit}(b) = (1,0) and (0,1).
    pub basis_exit: [Vector4<f64>; 2],
    /// Entry basis: vectors in TF with τ_{entry}(b) = (1,0) and (0,1).
    pub basis_entry: [Vector4<f64>; 2],

    // Trivialized polygon
    /// 2-face polygon in exit-normal trivialized coordinates.
    pub polygon_2d: Polygon2D,
    /// Original 4D vertices.
    pub vertices_4d: Vec<Vector4<f64>>,
    /// Centroid for reconstruction.
    pub centroid_4d: Vector4<f64>,
}

impl TwoFaceEnriched {
    /// Create an enriched 2-face from a basic 2-face.
    pub fn from_two_face(
        two_face: &TwoFace,
        n_i: &Vector4<f64>,
        n_j: &Vector4<f64>,
        vertices_4d: Vec<Vector4<f64>>,
    ) -> TubeResult<Self> {
        if two_face.is_lagrangian {
            return Err(TubeError::DegenerateTwoFace {
                i: two_face.i,
                j: two_face.j,
                message: "Cannot enrich Lagrangian 2-face".to_string(),
            });
        }

        // Determine flow-aware normals
        let (entry_normal, exit_normal, entry_facet, exit_facet) =
            match two_face.flow_direction.unwrap() {
                FlowDirection::ItoJ => (*n_i, *n_j, two_face.i, two_face.j),
                FlowDirection::JtoI => (*n_j, *n_i, two_face.j, two_face.i),
            };

        // Compute basis vectors
        let basis_exit = compute_exit_basis(&entry_normal, &exit_normal)?;
        let basis_entry = compute_entry_basis(&entry_normal, &exit_normal)?;

        // Compute transition matrix using basis method
        let transition_matrix = compute_transition_matrix_basis(&basis_entry, &exit_normal);

        // Compute rotation number
        let rotation = compute_rotation_number(&transition_matrix);

        // Trivialize vertices using exit normal
        let centroid_4d: Vector4<f64> =
            vertices_4d.iter().sum::<Vector4<f64>>() / vertices_4d.len() as f64;

        let polygon_vertices: Vec<Vector2<f64>> = vertices_4d
            .iter()
            .map(|v| trivialize(&exit_normal, &(v - centroid_4d)))
            .collect();

        let polygon_2d = Polygon2D::from_unsorted(polygon_vertices);

        Ok(Self {
            i: two_face.i,
            j: two_face.j,
            omega_ij: two_face.omega_ij,
            is_lagrangian: two_face.is_lagrangian,
            flow_direction: two_face.flow_direction,
            entry_normal,
            exit_normal,
            entry_facet,
            exit_facet,
            transition_matrix,
            rotation,
            basis_exit,
            basis_entry,
            polygon_2d,
            vertices_4d,
            centroid_4d,
        })
    }
}

/// Compute transition matrix using explicit basis vectors.
///
/// ψ[k, l] = ⟨b_entry[l], (Jn_exit or Kn_exit)⟩
fn compute_transition_matrix_basis(
    b_entry: &[Vector4<f64>; 2],
    n_exit: &Vector4<f64>,
) -> Matrix2<f64> {
    let jn_exit = apply_j(n_exit);
    let kn_exit = apply_k(n_exit);

    Matrix2::new(
        b_entry[0].dot(&jn_exit),
        b_entry[1].dot(&jn_exit),
        b_entry[0].dot(&kn_exit),
        b_entry[1].dot(&kn_exit),
    )
}

/// Compute rotation number from transition matrix.
///
/// ρ = arccos(tr(ψ)/2) / 2π
fn compute_rotation_number(psi: &Matrix2<f64>) -> f64 {
    let trace = psi.trace();
    // Clamp for numerical stability
    let half_trace = (0.5 * trace).clamp(-1.0 + EPS, 1.0 - EPS);
    half_trace.acos() / TAU
}

/// Preprocessed polytope data for the tube algorithm.
#[derive(Debug)]
pub struct PolytopeData {
    /// Number of facets.
    pub num_facets: usize,
    /// Unit outward normals.
    pub normals: Vec<Vector4<f64>>,
    /// Heights.
    pub heights: Vec<f64>,
    /// Reeb vectors: Rᵢ = (2/hᵢ) * I * nᵢ.
    pub reeb_vectors: Vec<Vector4<f64>>,
    /// All 2-faces (basic data).
    pub two_faces: Vec<TwoFace>,
    /// Enriched 2-faces (non-Lagrangian only).
    pub two_faces_enriched: Vec<TwoFaceEnriched>,
    /// 2-face lookup: two_face_index[i][j] = index into two_faces_enriched (or None).
    pub two_face_index: Vec<Vec<Option<usize>>>,
}

impl PolytopeData {
    /// Preprocess a polytope for the tube algorithm.
    pub fn from_hrep(hrep: &PolytopeHRep) -> TubeResult<Self> {
        hrep.validate()?;

        let num_facets = hrep.num_facets();
        let normals = hrep.normals.clone();
        let heights = hrep.heights.clone();

        // Compute Reeb vectors
        let reeb_vectors: Vec<Vector4<f64>> = normals
            .iter()
            .zip(&heights)
            .map(|(n, &h)| reeb_vector(n, h))
            .collect();

        // Find all 2-faces
        let mut two_faces = Vec::new();
        let mut two_face_index: Vec<Vec<Option<usize>>> =
            vec![vec![None; num_facets]; num_facets];

        // We need to determine which pairs of facets form 2-faces.
        // For a general polytope, we'd need vertex enumeration.
        // For now, we check adjacency by looking at normal directions.
        // Two facets form a 2-face if their normals are not parallel.
        for i in 0..num_facets {
            for j in (i + 1)..num_facets {
                // Check if facets are adjacent (non-parallel normals, form a 2D intersection)
                // For the tube algorithm, we need non-Lagrangian 2-faces.
                let n_i = &normals[i];
                let n_j = &normals[j];

                // Check if normals are not parallel
                let cross_norm = (n_i - n_j).norm();
                if cross_norm < EPS {
                    continue; // Parallel, no 2-face
                }

                let two_face = TwoFace::new(i, j, n_i, n_j);
                two_faces.push(two_face);
            }
        }

        // Enrich non-Lagrangian 2-faces
        let mut two_faces_enriched = Vec::new();

        for tf in two_faces.iter() {
            if !tf.is_lagrangian {
                // For enrichment, we need 4D vertices of the 2-face.
                // Without full vertex enumeration, we'll compute placeholder vertices.
                // In a full implementation, this would come from vertex enumeration.
                let vertices_4d = compute_2face_vertices(tf, &normals, &heights)?;

                match TwoFaceEnriched::from_two_face(tf, &normals[tf.i], &normals[tf.j], vertices_4d)
                {
                    Ok(enriched) => {
                        let enriched_idx = two_faces_enriched.len();
                        two_face_index[tf.i][tf.j] = Some(enriched_idx);
                        two_face_index[tf.j][tf.i] = Some(enriched_idx);
                        two_faces_enriched.push(enriched);
                    }
                    Err(e) => {
                        // Log and skip this 2-face
                        eprintln!("Warning: Could not enrich 2-face ({}, {}): {}", tf.i, tf.j, e);
                    }
                }
            }
        }

        Ok(Self {
            num_facets,
            normals,
            heights,
            reeb_vectors,
            two_faces,
            two_faces_enriched,
            two_face_index,
        })
    }

    /// Check if the polytope has any Lagrangian 2-faces.
    pub fn has_lagrangian_two_faces(&self) -> bool {
        self.two_faces.iter().any(|tf| tf.is_lagrangian)
    }

    /// Get the Lagrangian 2-face indices.
    pub fn lagrangian_two_face_indices(&self) -> Vec<(usize, usize)> {
        self.two_faces
            .iter()
            .filter(|tf| tf.is_lagrangian)
            .map(|tf| (tf.i, tf.j))
            .collect()
    }

    /// Get an enriched 2-face by facet indices.
    pub fn get_two_face_enriched(&self, i: usize, j: usize) -> Option<&TwoFaceEnriched> {
        let (a, b) = if i < j { (i, j) } else { (j, i) };
        self.two_face_index[a][b].map(|idx| &self.two_faces_enriched[idx])
    }

    /// Get the Reeb vector for a facet.
    pub fn reeb(&self, facet: usize) -> &Vector4<f64> {
        &self.reeb_vectors[facet]
    }

    /// Get the normal for a facet.
    pub fn normal(&self, facet: usize) -> &Vector4<f64> {
        &self.normals[facet]
    }

    /// Get the height for a facet.
    pub fn height(&self, facet: usize) -> f64 {
        self.heights[facet]
    }
}

/// Compute vertices of a 2-face.
///
/// For a 2-face F_{ij}, we need to find points that satisfy:
/// ⟨n_i, x⟩ = h_i and ⟨n_j, x⟩ = h_j and ⟨n_k, x⟩ ≤ h_k for all k.
///
/// This is a simplified implementation that constructs 4 vertices
/// by finding basis vectors for the 2-face tangent space.
fn compute_2face_vertices(
    two_face: &TwoFace,
    normals: &[Vector4<f64>],
    heights: &[f64],
) -> TubeResult<Vec<Vector4<f64>>> {
    let n_i = &normals[two_face.i];
    let n_j = &normals[two_face.j];
    let h_i = heights[two_face.i];
    let h_j = heights[two_face.j];

    // Find a point on the 2-face (satisfying both equality constraints)
    // We solve: n_i · x = h_i and n_j · x = h_j
    // We need two more equations to fully determine x.

    // Use basis vectors Jn and Kn to complete the system
    let jn_i = apply_j(n_i);
    let kn_i = apply_k(n_i);

    // Find a centroid point by solving a least-squares problem
    // We want x such that n_i · x ≈ h_i and n_j · x ≈ h_j
    // Use pseudo-inverse approach

    let m = Matrix4::from_rows(&[
        n_i.transpose(),
        n_j.transpose(),
        jn_i.transpose(),
        kn_i.transpose(),
    ]);

    let b = Vector4::new(h_i, h_j, 0.0, 0.0);

    let m_inv = m.try_inverse().ok_or_else(|| TubeError::DegenerateTwoFace {
        i: two_face.i,
        j: two_face.j,
        message: "Cannot invert matrix for 2-face centroid".to_string(),
    })?;

    let centroid = m_inv * b;

    // Construct vertices by moving along the 2-face tangent space
    // The tangent space is perpendicular to both n_i and n_j

    // Find two orthogonal vectors in the tangent space
    let basis = compute_exit_basis(n_i, n_j)?;

    // Create a small square of vertices
    let scale = 0.5; // Arbitrary scale for visualization
    let vertices = vec![
        centroid + scale * (basis[0] + basis[1]),
        centroid + scale * (basis[0] - basis[1]),
        centroid + scale * (-basis[0] - basis[1]),
        centroid + scale * (-basis[0] + basis[1]),
    ];

    Ok(vertices)
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    fn unit_tesseract() -> PolytopeHRep {
        PolytopeHRep::new(
            vec![
                Vector4::new(1.0, 0.0, 0.0, 0.0),
                Vector4::new(-1.0, 0.0, 0.0, 0.0),
                Vector4::new(0.0, 1.0, 0.0, 0.0),
                Vector4::new(0.0, -1.0, 0.0, 0.0),
                Vector4::new(0.0, 0.0, 1.0, 0.0),
                Vector4::new(0.0, 0.0, -1.0, 0.0),
                Vector4::new(0.0, 0.0, 0.0, 1.0),
                Vector4::new(0.0, 0.0, 0.0, -1.0),
            ],
            vec![1.0; 8],
        )
    }

    #[test]
    fn test_polytope_validation() {
        let tesseract = unit_tesseract();
        assert!(tesseract.validate().is_ok());
    }

    #[test]
    fn test_polytope_validation_non_unit_normal() {
        let bad = PolytopeHRep::new(
            vec![
                Vector4::new(2.0, 0.0, 0.0, 0.0), // Not unit
                Vector4::new(-1.0, 0.0, 0.0, 0.0),
                Vector4::new(0.0, 1.0, 0.0, 0.0),
                Vector4::new(0.0, -1.0, 0.0, 0.0),
                Vector4::new(0.0, 0.0, 1.0, 0.0),
            ],
            vec![1.0; 5],
        );
        assert!(bad.validate().is_err());
    }

    #[test]
    fn test_two_face_flow_direction() {
        let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);

        // ω(e1, e3) = 1 > 0, so flow is ItoJ
        let tf = TwoFace::new(0, 1, &e1, &e3);
        assert!(!tf.is_lagrangian);
        assert_eq!(tf.flow_direction, Some(FlowDirection::ItoJ));

        // ω(e3, e1) = -1 < 0, so flow is JtoI
        let tf2 = TwoFace::new(0, 1, &e3, &e1);
        assert_eq!(tf2.flow_direction, Some(FlowDirection::JtoI));
    }

    #[test]
    fn test_two_face_lagrangian() {
        let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let e2 = Vector4::new(0.0, 1.0, 0.0, 0.0);

        // ω(e1, e2) = 0, so Lagrangian
        let tf = TwoFace::new(0, 1, &e1, &e2);
        assert!(tf.is_lagrangian);
        assert_eq!(tf.flow_direction, None);
    }

    #[test]
    fn test_tesseract_has_lagrangian_2faces() {
        let tesseract = unit_tesseract();
        let data = PolytopeData::from_hrep(&tesseract).unwrap();

        // Tesseract is a Lagrangian product, all 2-faces should be Lagrangian
        assert!(data.has_lagrangian_two_faces());
    }

    #[test]
    fn test_reeb_vector_properties() {
        let tesseract = unit_tesseract();
        let data = PolytopeData::from_hrep(&tesseract).unwrap();

        for i in 0..data.num_facets {
            let r = data.reeb(i);
            let n = data.normal(i);

            // Reeb vector perpendicular to normal
            assert_relative_eq!(r.dot(n), 0.0, epsilon = 1e-14);

            // Reeb vector magnitude = 2/h
            let expected_norm = 2.0 / data.height(i);
            assert_relative_eq!(r.norm(), expected_norm, epsilon = 1e-14);
        }
    }
}
