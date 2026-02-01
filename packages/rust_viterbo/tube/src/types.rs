//! Core data types for the tube algorithm.
//!
//! This module defines:
//! - PolytopeHRep: H-representation of a 4D polytope (re-exported from geom)
//! - Polygon2D: 2D convex polygon (trivialized 2-face)
//! - AffineMap2D: Affine transformation in 2D
//! - AffineFunc: Affine function ℝ² → ℝ
//! - TwoFaceData: Per-2-face trivialization data
//! - ThreeFacetData: Per-transition precomputed flow data
//! - TwoFaceLookup: Index conversion and adjacency tables
//! - Tube: Partial Reeb trajectory with fixed combinatorial class
//! - ClosedReebOrbit: Complete closed Reeb orbit

use nalgebra::{Matrix2, Vector2, Vector4};

#[cfg(test)]
use crate::constants::EPS;

// Re-export the shared polytope type from geom crate.
pub use geom::PolytopeHRep;

/// Validate polytope for tube algorithm.
///
/// This adds tube-specific checks on top of the base validation:
/// - At least 5 facets (minimum for a 4D polytope)
pub fn validate_for_tube(polytope: &PolytopeHRep) -> Result<(), TubeError> {
    // Base validation from geom
    polytope
        .validate()
        .map_err(|e| TubeError::InvalidPolytope(e.to_string()))?;

    // Tube-specific: need at least 5 facets for a 4D polytope
    if polytope.num_facets() < 5 {
        return Err(TubeError::InvalidPolytope(format!(
            "need at least 5 facets for a 4D polytope, got {}",
            polytope.num_facets()
        )));
    }

    Ok(())
}

/// 2D convex polygon represented by CCW-ordered vertices.
#[derive(Debug, Clone)]
pub struct Polygon2D {
    /// Vertices in counter-clockwise order.
    pub vertices: Vec<Vector2<f64>>,
}

impl Polygon2D {
    /// Create a polygon from vertices (assumed CCW).
    pub fn new(vertices: Vec<Vector2<f64>>) -> Self {
        Self { vertices }
    }

    /// Create an empty polygon.
    pub fn empty() -> Self {
        Self { vertices: vec![] }
    }

    /// Check if the polygon is empty (no vertices or degenerate).
    pub fn is_empty(&self) -> bool {
        self.vertices.len() < 3
    }

    /// Compute the area of the polygon using the shoelace formula.
    pub fn area(&self) -> f64 {
        if self.vertices.len() < 3 {
            return 0.0;
        }

        let mut area = 0.0;
        let n = self.vertices.len();
        for i in 0..n {
            let j = (i + 1) % n;
            area += self.vertices[i][0] * self.vertices[j][1];
            area -= self.vertices[j][0] * self.vertices[i][1];
        }
        (area / 2.0).abs()
    }

    /// Compute the centroid of the polygon.
    pub fn centroid(&self) -> Vector2<f64> {
        if self.vertices.is_empty() {
            return Vector2::zeros();
        }
        let sum: Vector2<f64> = self.vertices.iter().sum();
        sum / self.vertices.len() as f64
    }
}

/// Affine transformation in 2D: f(x) = Ax + b.
#[derive(Debug, Clone)]
pub struct AffineMap2D {
    /// Linear part (2×2 matrix).
    pub matrix: Matrix2<f64>,
    /// Translation offset.
    pub offset: Vector2<f64>,
}

impl AffineMap2D {
    /// Create the identity transformation.
    pub fn identity() -> Self {
        Self {
            matrix: Matrix2::identity(),
            offset: Vector2::zeros(),
        }
    }

    /// Apply the transformation to a point.
    #[inline]
    pub fn apply(&self, x: &Vector2<f64>) -> Vector2<f64> {
        self.matrix * x + self.offset
    }

    /// Compose two affine maps: (f ∘ g)(x) = f(g(x)).
    /// f ∘ g = (A_f * A_g, A_f * b_g + b_f)
    pub fn compose(&self, other: &AffineMap2D) -> AffineMap2D {
        AffineMap2D {
            matrix: self.matrix * other.matrix,
            offset: self.matrix * other.offset + self.offset,
        }
    }

    /// Compute the inverse affine map, if it exists.
    ///
    /// For f(x) = Ax + b, the inverse is f⁻¹(y) = A⁻¹(y - b) = A⁻¹y - A⁻¹b.
    pub fn try_inverse(&self) -> Option<AffineMap2D> {
        let inv_matrix = self.matrix.try_inverse()?;
        Some(AffineMap2D {
            matrix: inv_matrix,
            offset: -(inv_matrix * self.offset),
        })
    }
}

/// Affine function ℝ² → ℝ: f(x) = ⟨g, x⟩ + c.
#[derive(Debug, Clone)]
pub struct AffineFunc {
    /// Gradient vector.
    pub gradient: Vector2<f64>,
    /// Constant term.
    pub constant: f64,
}

impl AffineFunc {
    /// Create the zero function.
    pub fn zero() -> Self {
        Self {
            gradient: Vector2::zeros(),
            constant: 0.0,
        }
    }

    /// Evaluate the function at a point.
    #[inline]
    pub fn eval(&self, x: &Vector2<f64>) -> f64 {
        self.gradient.dot(x) + self.constant
    }

    /// Add two affine functions.
    pub fn add(&self, other: &AffineFunc) -> AffineFunc {
        AffineFunc {
            gradient: self.gradient + other.gradient,
            constant: self.constant + other.constant,
        }
    }

    /// Compose affine function with affine map: f(g(x)) where g(x) = Ax + b.
    /// Result: ⟨grad, Ax + b⟩ + c = ⟨Aᵀgrad, x⟩ + (grad·b + c)
    pub fn compose_with_map(&self, map: &AffineMap2D) -> AffineFunc {
        AffineFunc {
            gradient: map.matrix.transpose() * self.gradient,
            constant: self.gradient.dot(&map.offset) + self.constant,
        }
    }
}

// ============================================================================
// 2-Face and Transition Data
// ============================================================================

/// Data for a single non-Lagrangian 2-face.
///
/// A 2-face is the intersection of two adjacent facets F_entry ∩ F_exit.
/// Non-Lagrangian means ω(n_entry, n_exit) ≠ 0, so Reeb flow crosses it.
/// The flow direction is entry → exit (determined by the sign of ω).
#[derive(Debug, Clone)]
pub struct TwoFaceData {
    /// Entry facet index (the facet we came from).
    pub entry_facet: usize,
    /// Exit facet index (the facet we flow into).
    pub exit_facet: usize,

    /// Symplectic form: ω(n_entry, n_exit) > 0.
    pub omega: f64,
    /// Rotation number ρ ∈ (0, 0.5).
    pub rotation: f64,

    /// 2-face polygon in exit-trivialized coordinates (CCW).
    pub polygon: Polygon2D,
    /// Centroid in 4D (for orbit reconstruction).
    pub centroid_4d: Vector4<f64>,
    /// Basis vectors for exit trivialization: {b₁, b₂} ∈ TF.
    pub basis_exit: [Vector4<f64>; 2],
    /// Entry facet normal.
    pub entry_normal: Vector4<f64>,
    /// Exit facet normal.
    pub exit_normal: Vector4<f64>,
}

/// Data for a 3-facet transition (i, j, k).
///
/// Represents a tube step: flow on F_j from 2-face (F_i, F_j) to (F_j, F_k).
/// Precomputes the affine flow map and time function for this transition.
#[derive(Debug, Clone)]
pub struct ThreeFacetData {
    /// Index of entry 2-face (F_i, F_j) in the TwoFaceData list.
    pub two_face_entry: usize,
    /// Index of exit 2-face (F_j, F_k) in the TwoFaceData list.
    pub two_face_exit: usize,
    /// Middle facet index (the facet we flow along).
    pub facet_mid: usize,

    /// Flow map matrix: A = ψ + r_triv ⊗ t_grad.
    /// Maps trivialized coordinates from entry 2-face to exit 2-face.
    pub flow_matrix: Matrix2<f64>,
    /// Flow map offset: b = τ_exit(c_entry - c_exit + t_const * r_mid).
    pub flow_offset: Vector2<f64>,
    /// Time gradient: ∇t where t(p) = ⟨t_grad, p⟩ + t_const.
    pub time_gradient: Vector2<f64>,
    /// Time constant.
    pub time_constant: f64,
}

/// Lookup tables for index conversion and adjacency.
///
/// Provides O(1) access from facet pairs to 2-face indices,
/// and adjacency information for the search tree.
#[derive(Debug, Clone)]
pub struct TwoFaceLookup {
    /// Dense matrix for (i, j) → 2-face index lookup.
    /// Access: two_face[i * num_facets + j] for i < j.
    two_face: Vec<Option<usize>>,
    /// For each 2-face k, list of transition indices that start from k.
    pub transitions_from: Vec<Vec<usize>>,
    /// Number of facets.
    num_facets: usize,
}

impl TwoFaceLookup {
    /// Create empty lookup with given number of facets.
    pub fn new(num_facets: usize) -> Self {
        Self {
            two_face: vec![None; num_facets * num_facets],
            transitions_from: Vec::new(),
            num_facets,
        }
    }

    /// Register a 2-face at given index.
    pub fn register_two_face(&mut self, i: usize, j: usize, index: usize) {
        let (a, b) = if i < j { (i, j) } else { (j, i) };
        self.two_face[a * self.num_facets + b] = Some(index);
    }

    /// Get 2-face index for facet pair (i, j), or None if not a 2-face.
    #[inline]
    pub fn get_two_face(&self, i: usize, j: usize) -> Option<usize> {
        let (a, b) = if i < j { (i, j) } else { (j, i) };
        self.two_face
            .get(a * self.num_facets + b)
            .copied()
            .flatten()
    }

    /// Get transitions from 2-face k (indices into ThreeFacetData list).
    #[inline]
    pub fn transitions_from(&self, k: usize) -> &[usize] {
        &self.transitions_from[k]
    }
}

// ============================================================================
// Tube and Orbit Types
// ============================================================================

/// A tube represents all Reeb trajectories with a fixed combinatorial class.
#[derive(Debug, Clone)]
pub struct Tube {
    /// Facet sequence [i₀, i₁, ..., iₖ, iₖ₊₁].
    /// The tube starts on 2-face F_{i₀,i₁} and ends on 2-face F_{iₖ,iₖ₊₁}.
    pub facet_sequence: Vec<usize>,

    /// Set of valid starting points (in start 2-face coordinates).
    pub p_start: Polygon2D,

    /// Set of valid ending points (in end 2-face coordinates).
    pub p_end: Polygon2D,

    /// Flow map: maps start point → end point.
    pub flow_map: AffineMap2D,

    /// Action as a function of start point.
    pub action_func: AffineFunc,

    /// Accumulated rotation (in turns).
    pub rotation: f64,
}

impl Tube {
    /// Compute the lower bound on action over all valid starting points.
    /// Minimum of affine function over convex polygon = minimum over vertices.
    pub fn action_lower_bound(&self) -> f64 {
        if self.p_start.is_empty() {
            return f64::INFINITY;
        }
        self.p_start
            .vertices
            .iter()
            .map(|v| self.action_func.eval(v))
            .fold(f64::INFINITY, f64::min)
    }

    /// Get the start 2-face indices.
    pub fn start_two_face(&self) -> (usize, usize) {
        (self.facet_sequence[0], self.facet_sequence[1])
    }

    /// Get the end 2-face indices.
    pub fn end_two_face(&self) -> (usize, usize) {
        let n = self.facet_sequence.len();
        (self.facet_sequence[n - 2], self.facet_sequence[n - 1])
    }

    /// Check if this is a closed tube (start 2-face == end 2-face).
    pub fn is_closed(&self) -> bool {
        self.start_two_face() == self.end_two_face()
    }
}

/// A closed Reeb orbit on the polytope boundary.
#[derive(Debug, Clone)]
pub struct ClosedReebOrbit {
    /// Period (= action for Reeb flow).
    pub period: f64,
    /// Breakpoints in 4D (first and last should be equal).
    pub breakpoints: Vec<Vector4<f64>>,
    /// Facet index for each segment.
    pub segment_facets: Vec<usize>,
    /// Time spent on each segment.
    pub segment_times: Vec<f64>,
}

/// Error types for the tube algorithm.
#[derive(Debug, thiserror::Error)]
pub enum TubeError {
    /// The input polytope is invalid.
    #[error("Invalid polytope: {0}")]
    InvalidPolytope(String),

    /// The polytope has Lagrangian 2-faces (tube algorithm inapplicable).
    #[error(
        "Polytope has Lagrangian 2-faces (tube algorithm requires all 2-faces non-Lagrangian)"
    )]
    HasLagrangianTwoFaces,

    /// Numerical computation failed.
    #[error("Numerical instability: {0}")]
    NumericalInstability(String),

    /// Near-singular flow map in tube closure.
    #[error("Near-singular flow map: det(A - I) = {det:.2e}")]
    NearSingularFlowMap { det: f64 },

    /// No closed orbits found.
    #[error("No closed orbits found")]
    NoClosedOrbits,
}

/// Result of the tube capacity computation.
#[derive(Debug, Clone)]
pub struct TubeResult {
    /// The computed EHZ capacity.
    pub capacity: f64,
    /// The optimal closed orbit achieving minimum action.
    pub optimal_orbit: ClosedReebOrbit,
    /// Number of tubes explored.
    pub tubes_explored: usize,
    /// Number of tubes pruned.
    pub tubes_pruned: usize,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_polygon_area_triangle() {
        let p = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(0.0, 1.0),
        ]);
        assert!((p.area() - 0.5).abs() < EPS);
    }

    #[test]
    fn test_polygon_area_unit_square() {
        let p = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);
        assert!((p.area() - 1.0).abs() < EPS);
    }

    #[test]
    fn test_affine_map_compose() {
        let f = AffineMap2D {
            matrix: Matrix2::new(2.0, 0.0, 0.0, 2.0),
            offset: Vector2::new(1.0, 0.0),
        };
        let g = AffineMap2D {
            matrix: Matrix2::new(1.0, 1.0, 0.0, 1.0),
            offset: Vector2::new(0.0, 1.0),
        };

        let fg = f.compose(&g);
        let x = Vector2::new(1.0, 2.0);

        // (f ∘ g)(x) should equal f(g(x))
        let expected = f.apply(&g.apply(&x));
        let actual = fg.apply(&x);
        assert!((expected - actual).norm() < EPS);
    }

    #[test]
    fn test_affine_func_compose_with_map() {
        let func = AffineFunc {
            gradient: Vector2::new(1.0, 2.0),
            constant: 3.0,
        };
        let map = AffineMap2D {
            matrix: Matrix2::new(2.0, 0.0, 0.0, 1.0),
            offset: Vector2::new(1.0, -1.0),
        };

        let composed = func.compose_with_map(&map);
        let x = Vector2::new(0.5, 0.5);

        // f(g(x)) should equal composed(x)
        let expected = func.eval(&map.apply(&x));
        let actual = composed.eval(&x);
        assert!((expected - actual).abs() < EPS);
    }

    #[test]
    fn test_tube_action_lower_bound() {
        let tube = Tube {
            facet_sequence: vec![0, 1],
            p_start: Polygon2D::new(vec![
                Vector2::new(0.0, 0.0),
                Vector2::new(1.0, 0.0),
                Vector2::new(0.5, 1.0),
            ]),
            p_end: Polygon2D::empty(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc {
                gradient: Vector2::new(1.0, 0.0), // action = x₁
                constant: 0.0,
            },
            rotation: 0.0,
        };

        // Minimum of x₁ over the triangle is at (0,0)
        assert!((tube.action_lower_bound() - 0.0).abs() < EPS);
    }
}
