//! Polytope data structures and preprocessing.

use nalgebra::{Matrix2, Vector2, Vector4};
use std::collections::HashMap;

use crate::geom::{sort_ccw, symplectic_form, Polygon2D, J_MATRIX};
use crate::tol::{EPS, EPS_LAGRANGIAN, EPS_UNIT};
use crate::trivialization::{
    compute_rotation_number, compute_transition_matrix, is_symplectic, trivialize,
};

// ============================================================================
// PolytopeHRep
// ============================================================================

/// H-representation of a polytope: K = ∩_i { x : ⟨n_i, x⟩ ≤ h_i }
#[derive(Debug, Clone)]
pub struct PolytopeHRep {
    /// Unit outward normals.
    pub normals: Vec<Vector4<f64>>,
    /// Heights (h_i > 0 since 0 ∈ int(K)).
    pub heights: Vec<f64>,
}

impl PolytopeHRep {
    /// Validate the H-rep.
    pub fn validate(&self) -> Result<(), PolytopeError> {
        if self.normals.len() != self.heights.len() {
            return Err(PolytopeError::Validation(
                "normals and heights must have same length".into(),
            ));
        }

        // Check normals are unit vectors
        for (i, n) in self.normals.iter().enumerate() {
            if (n.norm() - 1.0).abs() > EPS_UNIT {
                return Err(PolytopeError::Validation(format!(
                    "normal {} has norm {} ≠ 1",
                    i,
                    n.norm()
                )));
            }
        }

        // Check heights are positive (0 in interior)
        for (i, &h) in self.heights.iter().enumerate() {
            if h <= 0.0 {
                return Err(PolytopeError::Validation(format!(
                    "height {} = {} ≤ 0 (origin not in interior)",
                    i, h
                )));
            }
        }

        // Check for duplicate half-spaces
        for i in 0..self.normals.len() {
            for j in (i + 1)..self.normals.len() {
                let n_diff = (&self.normals[i] - &self.normals[j]).norm();
                let h_diff = (self.heights[i] - self.heights[j]).abs();
                if n_diff < EPS && h_diff < EPS {
                    return Err(PolytopeError::Validation(format!(
                        "half-spaces {} and {} are duplicates",
                        i, j
                    )));
                }
            }
        }

        Ok(())
    }

    pub fn num_facets(&self) -> usize {
        self.normals.len()
    }

    /// Compute the Reeb vector on facet i: R_i = (2/h_i) * J * n_i
    pub fn reeb_vector(&self, i: usize) -> Vector4<f64> {
        (J_MATRIX * self.normals[i]) * (2.0 / self.heights[i])
    }
}

// ============================================================================
// FlowDirection
// ============================================================================

/// Direction of Reeb flow across a non-Lagrangian 2-face.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FlowDirection {
    /// Flow crosses from facet i to facet j (ω(n_i, n_j) > 0)
    ItoJ,
    /// Flow crosses from facet j to facet i (ω(n_i, n_j) < 0)
    JtoI,
}

// ============================================================================
// TwoFace
// ============================================================================

/// A 2-face F_{ij} = F_i ∩ F_j (basic, unenriched).
#[derive(Debug, Clone)]
pub struct TwoFace {
    /// First facet index (i < j by convention).
    pub i: usize,
    /// Second facet index.
    pub j: usize,
    /// Indices of vertices on this 2-face.
    pub vertices: Vec<usize>,
    /// Symplectic form ω(n_i, n_j).
    pub omega_ij: f64,
}

impl TwoFace {
    pub fn is_lagrangian(&self) -> bool {
        self.omega_ij.abs() < EPS_LAGRANGIAN
    }

    pub fn flow_direction(&self) -> Option<FlowDirection> {
        if self.is_lagrangian() {
            None
        } else if self.omega_ij > 0.0 {
            Some(FlowDirection::ItoJ)
        } else {
            Some(FlowDirection::JtoI)
        }
    }
}

// ============================================================================
// TwoFaceEnriched
// ============================================================================

/// Enriched 2-face with all data needed for the tube algorithm.
///
/// Fields are **flow-direction-aware**: entry_normal, exit_normal, and
/// transition_matrix are computed based on actual flow direction, not the i < j convention.
#[derive(Debug, Clone)]
pub struct TwoFaceEnriched {
    /// First facet index (i < j).
    pub i: usize,
    /// Second facet index.
    pub j: usize,
    /// Vertex indices.
    pub vertices: Vec<usize>,
    /// ω(n_i, n_j)
    pub omega_ij: f64,
    /// Whether this is a Lagrangian 2-face.
    pub is_lagrangian: bool,
    /// Flow direction (None for Lagrangian).
    pub flow_direction: Option<FlowDirection>,
    /// Transition matrix (entry → exit).
    pub transition_matrix: Matrix2<f64>,
    /// Rotation number ρ ∈ (0, 0.5).
    pub rotation: f64,
    /// Normal of facet we entered from.
    pub entry_normal: Vector4<f64>,
    /// Normal of facet we exit to (used for trivialization per CH2021).
    pub exit_normal: Vector4<f64>,
    /// 2D polygon in τ_{exit_normal} coordinates.
    pub polygon_2d: Polygon2D,
    /// 4D vertex positions.
    pub vertices_4d: Vec<Vector4<f64>>,
    /// Centroid for reconstruction.
    pub centroid_4d: Vector4<f64>,
}

impl TwoFaceEnriched {
    pub fn rotation_number(&self) -> f64 {
        self.rotation
    }
}

// ============================================================================
// PolytopeData
// ============================================================================

/// Preprocessed polytope data for the tube algorithm.
#[derive(Debug)]
pub struct PolytopeData {
    pub hrep: PolytopeHRep,
    /// 4D vertices (computed via vertex enumeration).
    pub vertices: Vec<Vector4<f64>>,
    /// Basic 2-faces.
    pub two_faces: Vec<TwoFace>,
    /// Enriched 2-faces, indexed by (i, j) with i < j.
    pub two_faces_enriched: HashMap<(usize, usize), TwoFaceEnriched>,
    /// Pre-computed Reeb vectors.
    pub reeb_vectors: Vec<Vector4<f64>>,
    /// Adjacency: adjacent[i] = list of facets j adjacent to facet i.
    pub adjacency: Vec<Vec<usize>>,
}

impl PolytopeData {
    /// Preprocess a polytope for the tube algorithm.
    pub fn preprocess(hrep: PolytopeHRep) -> Result<Self, PolytopeError> {
        hrep.validate()?;

        // Compute vertices via simple enumeration (intersection of 4 hyperplanes)
        let vertices = enumerate_vertices(&hrep)?;

        // Compute Reeb vectors
        let reeb_vectors: Vec<_> = (0..hrep.num_facets())
            .map(|i| hrep.reeb_vector(i))
            .collect();

        // Enumerate 2-faces
        let two_faces = enumerate_two_faces(&hrep, &vertices);

        // Build adjacency
        let mut adjacency = vec![vec![]; hrep.num_facets()];
        for tf in &two_faces {
            adjacency[tf.i].push(tf.j);
            adjacency[tf.j].push(tf.i);
        }

        // Enrich 2-faces
        let two_faces_enriched = enrich_two_faces(&two_faces, &vertices, &hrep)?;

        Ok(PolytopeData {
            hrep,
            vertices,
            two_faces,
            two_faces_enriched,
            reeb_vectors,
            adjacency,
        })
    }

    pub fn has_lagrangian_two_faces(&self) -> bool {
        self.two_faces.iter().any(|tf| tf.is_lagrangian())
    }

    pub fn normal(&self, i: usize) -> &Vector4<f64> {
        &self.hrep.normals[i]
    }

    pub fn height(&self, i: usize) -> f64 {
        self.hrep.heights[i]
    }

    pub fn reeb_vector(&self, i: usize) -> &Vector4<f64> {
        &self.reeb_vectors[i]
    }

    /// Get 2-face by (i, j) where i < j.
    pub fn get_two_face(&self, i: usize, j: usize) -> Option<&TwoFace> {
        let (a, b) = if i < j { (i, j) } else { (j, i) };
        self.two_faces.iter().find(|tf| tf.i == a && tf.j == b)
    }

    /// Get enriched 2-face by (i, j) where i < j.
    pub fn get_two_face_enriched(&self, i: usize, j: usize) -> Option<&TwoFaceEnriched> {
        let (a, b) = if i < j { (i, j) } else { (j, i) };
        self.two_faces_enriched.get(&(a, b))
    }

    /// Get adjacent facets that flow can reach from the given facet.
    pub fn adjacent_facets(&self, i: usize) -> &[usize] {
        &self.adjacency[i]
    }
}

// ============================================================================
// Vertex Enumeration
// ============================================================================

/// Enumerate vertices by finding intersections of 4 hyperplanes.
fn enumerate_vertices(hrep: &PolytopeHRep) -> Result<Vec<Vector4<f64>>, PolytopeError> {
    let n = hrep.num_facets();
    let mut vertices = Vec::new();

    // Try all combinations of 4 facets
    for i1 in 0..n {
        for i2 in (i1 + 1)..n {
            for i3 in (i2 + 1)..n {
                for i4 in (i3 + 1)..n {
                    if let Some(v) = solve_4_hyperplanes(hrep, i1, i2, i3, i4) {
                        // Check if v satisfies all constraints
                        if is_feasible(&v, hrep) {
                            // Check for duplicates
                            if !vertices.iter().any(|u: &Vector4<f64>| (u - &v).norm() < EPS) {
                                vertices.push(v);
                            }
                        }
                    }
                }
            }
        }
    }

    if vertices.len() < 5 {
        return Err(PolytopeError::Validation(format!(
            "Only {} vertices found (need ≥5 for 4D polytope)",
            vertices.len()
        )));
    }

    Ok(vertices)
}

/// Solve for intersection of 4 hyperplanes.
fn solve_4_hyperplanes(
    hrep: &PolytopeHRep,
    i1: usize,
    i2: usize,
    i3: usize,
    i4: usize,
) -> Option<Vector4<f64>> {
    use nalgebra::Matrix4;

    // Build matrix A where rows are normals
    let a = Matrix4::from_rows(&[
        hrep.normals[i1].transpose(),
        hrep.normals[i2].transpose(),
        hrep.normals[i3].transpose(),
        hrep.normals[i4].transpose(),
    ]);

    // Build RHS vector
    let b = Vector4::new(
        hrep.heights[i1],
        hrep.heights[i2],
        hrep.heights[i3],
        hrep.heights[i4],
    );

    // Solve Ax = b
    a.try_inverse().map(|a_inv| a_inv * b)
}

/// Check if vertex satisfies all half-space constraints.
fn is_feasible(v: &Vector4<f64>, hrep: &PolytopeHRep) -> bool {
    for (n, &h) in hrep.normals.iter().zip(&hrep.heights) {
        if n.dot(v) > h + EPS {
            return false;
        }
    }
    true
}

// ============================================================================
// 2-Face Enumeration
// ============================================================================

fn enumerate_two_faces(hrep: &PolytopeHRep, vertices: &[Vector4<f64>]) -> Vec<TwoFace> {
    let n = hrep.num_facets();
    let mut faces = Vec::new();

    for i in 0..n {
        for j in (i + 1)..n {
            // Find vertices on both facets
            let verts: Vec<usize> = (0..vertices.len())
                .filter(|&k| {
                    let v = &vertices[k];
                    let on_i = (hrep.normals[i].dot(v) - hrep.heights[i]).abs() < EPS;
                    let on_j = (hrep.normals[j].dot(v) - hrep.heights[j]).abs() < EPS;
                    on_i && on_j
                })
                .collect();

            // 2-face needs at least 3 vertices
            if verts.len() >= 3 {
                let omega_ij = symplectic_form(&hrep.normals[i], &hrep.normals[j]);
                faces.push(TwoFace {
                    i,
                    j,
                    vertices: verts,
                    omega_ij,
                });
            }
        }
    }

    faces
}

// ============================================================================
// 2-Face Enrichment
// ============================================================================

fn enrich_two_faces(
    two_faces: &[TwoFace],
    vertices: &[Vector4<f64>],
    hrep: &PolytopeHRep,
) -> Result<HashMap<(usize, usize), TwoFaceEnriched>, PolytopeError> {
    let mut enriched = HashMap::new();

    for tf in two_faces {
        let n_i = &hrep.normals[tf.i];
        let n_j = &hrep.normals[tf.j];

        // Determine flow direction
        let (entry_normal, exit_normal) = match tf.flow_direction() {
            Some(FlowDirection::ItoJ) => (n_i.clone(), n_j.clone()),
            Some(FlowDirection::JtoI) => (n_j.clone(), n_i.clone()),
            None => {
                // Lagrangian: use canonical ordering
                (n_i.clone(), n_j.clone())
            }
        };

        // Transition matrix
        let transition_matrix = compute_transition_matrix(&entry_normal, &exit_normal);
        debug_assert!(
            is_symplectic(&transition_matrix),
            "Transition matrix not symplectic"
        );

        // Rotation number
        let rotation = if tf.is_lagrangian() {
            0.0
        } else {
            compute_rotation_number(&transition_matrix)
        };

        // Get 4D vertices
        let verts_4d: Vec<Vector4<f64>> = tf.vertices.iter().map(|&k| vertices[k]).collect();

        // Centroid
        let centroid: Vector4<f64> =
            verts_4d.iter().copied().sum::<Vector4<f64>>() / verts_4d.len() as f64;

        // Trivialize to 2D using exit normal (CH2021 convention)
        let polygon_2d_verts: Vec<Vector2<f64>> = verts_4d
            .iter()
            .map(|v| trivialize(&exit_normal, &(v - centroid)))
            .collect();
        let polygon_2d = Polygon2D::new(sort_ccw(polygon_2d_verts));

        let tfe = TwoFaceEnriched {
            i: tf.i,
            j: tf.j,
            vertices: tf.vertices.clone(),
            omega_ij: tf.omega_ij,
            is_lagrangian: tf.is_lagrangian(),
            flow_direction: tf.flow_direction(),
            transition_matrix,
            rotation,
            entry_normal,
            exit_normal,
            polygon_2d,
            vertices_4d: verts_4d,
            centroid_4d: centroid,
        };

        enriched.insert((tf.i, tf.j), tfe);
    }

    Ok(enriched)
}

// ============================================================================
// Errors
// ============================================================================

#[derive(Debug)]
pub enum PolytopeError {
    Validation(String),
    LagrangianTwoFaces,
}

impl std::fmt::Display for PolytopeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PolytopeError::Validation(msg) => write!(f, "Polytope validation error: {}", msg),
            PolytopeError::LagrangianTwoFaces => {
                write!(f, "Polytope has Lagrangian 2-faces; tube algorithm inapplicable")
            }
        }
    }
}

impl std::error::Error for PolytopeError {}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    fn tesseract() -> PolytopeHRep {
        PolytopeHRep {
            normals: vec![
                Vector4::new(1.0, 0.0, 0.0, 0.0),
                Vector4::new(-1.0, 0.0, 0.0, 0.0),
                Vector4::new(0.0, 1.0, 0.0, 0.0),
                Vector4::new(0.0, -1.0, 0.0, 0.0),
                Vector4::new(0.0, 0.0, 1.0, 0.0),
                Vector4::new(0.0, 0.0, -1.0, 0.0),
                Vector4::new(0.0, 0.0, 0.0, 1.0),
                Vector4::new(0.0, 0.0, 0.0, -1.0),
            ],
            heights: vec![1.0; 8],
        }
    }

    fn cross_polytope() -> PolytopeHRep {
        // Cross-polytope = conv{±e₁, ±e₂, ±e₃, ±e₄}
        // Has 16 facets with normals (±1,±1,±1,±1)/2
        let mut normals = Vec::new();
        let mut heights = Vec::new();

        for s1 in [-1.0, 1.0] {
            for s2 in [-1.0, 1.0] {
                for s3 in [-1.0, 1.0] {
                    for s4 in [-1.0, 1.0] {
                        let n = Vector4::new(s1, s2, s3, s4) / 2.0;
                        normals.push(n);
                        heights.push(1.0);
                    }
                }
            }
        }

        PolytopeHRep { normals, heights }
    }

    #[test]
    fn test_tesseract_validation() {
        let hrep = tesseract();
        assert!(hrep.validate().is_ok());
    }

    #[test]
    fn test_cross_polytope_validation() {
        let hrep = cross_polytope();
        assert!(hrep.validate().is_ok());
    }

    #[test]
    fn test_tesseract_vertices() {
        let hrep = tesseract();
        let vertices = enumerate_vertices(&hrep).unwrap();
        // Tesseract has 16 vertices
        assert_eq!(vertices.len(), 16);
    }

    #[test]
    fn test_cross_polytope_vertices() {
        let hrep = cross_polytope();
        let vertices = enumerate_vertices(&hrep).unwrap();
        // Cross-polytope has 8 vertices (±e_i)
        assert_eq!(vertices.len(), 8);
    }

    #[test]
    fn test_tesseract_is_lagrangian_product() {
        // Tesseract = [-1,1]² × [-1,1]² is a Lagrangian product
        let hrep = tesseract();
        let data = PolytopeData::preprocess(hrep).unwrap();
        assert!(data.has_lagrangian_two_faces());
    }

    #[test]
    fn test_cross_polytope_no_lagrangian_faces() {
        // Cross-polytope should have NO Lagrangian 2-faces
        let hrep = cross_polytope();
        let data = PolytopeData::preprocess(hrep).unwrap();

        // Check that all 2-faces are non-Lagrangian
        for tf in &data.two_faces {
            assert!(
                !tf.is_lagrangian(),
                "Found Lagrangian 2-face ({}, {}) with ω = {}",
                tf.i,
                tf.j,
                tf.omega_ij
            );
        }

        assert!(!data.has_lagrangian_two_faces());
    }

    #[test]
    fn test_reeb_vector_properties() {
        let hrep = tesseract();

        for i in 0..hrep.num_facets() {
            let r = hrep.reeb_vector(i);
            let n = &hrep.normals[i];
            let h = hrep.heights[i];

            // R perpendicular to n
            assert!(r.dot(n).abs() < EPS, "Reeb not perpendicular to normal");

            // |R| = 2/h
            let expected_norm = 2.0 / h;
            assert!(
                (r.norm() - expected_norm).abs() < EPS,
                "Reeb norm incorrect"
            );
        }
    }
}
