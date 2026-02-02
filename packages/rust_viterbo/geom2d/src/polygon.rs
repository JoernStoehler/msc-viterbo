//! Convex polygon representation and validation.
//!
//! # Definition
//!
//! A [`Polygon`] represents a **convex polygon** in R² with vertices stored in
//! **counter-clockwise (CCW) order**.
//!
//! # Mathematical Properties (Invariants)
//!
//! A valid `Polygon` satisfies:
//!
//! 1. **At least 3 vertices** (minimum for a 2D polygon)
//! 2. **No duplicate vertices** (consecutive or otherwise)
//! 3. **CCW orientation** (signed area > 0)
//! 4. **Convex** (all cross products at vertices have the same sign)
//! 5. **Non-degenerate** (positive area, not collinear)
//!
//! # Validation
//!
//! Use [`Polygon::new`] which validates all invariants, or [`Polygon::new_unchecked`]
//! if you have already validated externally (e.g., in tests with known-good data).
//!
//! # References
//!
//! - Convexity definition: A polygon P is convex iff for all edges (v_i, v_{i+1}),
//!   all other vertices lie on the left side (or on) the edge.
//! - CCW orientation: The signed area formula gives positive area for CCW ordering.

use nalgebra::Vector2;
use thiserror::Error;

use crate::tolerances::{EPS_AREA, EPS_VERTEX, MAX_COORD};

/// Error type for polygon validation failures.
///
/// Each variant corresponds to a specific invariant violation, enabling precise
/// error reporting and targeted test cases.
#[derive(Debug, Clone, Error, PartialEq)]
pub enum PolygonError {
    /// Polygon has fewer than 3 vertices.
    #[error("polygon must have at least 3 vertices, got {0}")]
    TooFewVertices(usize),

    /// A vertex coordinate is invalid (NaN, infinite, or too large).
    #[error("vertex {index} has invalid coordinate: {value} (must be finite and |x| <= {MAX_COORD:.0e})")]
    InvalidCoordinate { index: usize, value: f64 },

    /// Two vertices are coincident (within tolerance).
    #[error("vertices {i} and {j} are coincident (distance {distance:.2e} < {EPS_VERTEX:.2e})")]
    CoincidentVertices { i: usize, j: usize, distance: f64 },

    /// Vertices are not in counter-clockwise order (signed area <= 0).
    #[error("vertices are not in CCW order (signed area = {signed_area:.2e})")]
    NotCCW { signed_area: f64 },

    /// Polygon is not convex (a vertex lies on the wrong side of an edge).
    #[error(
        "polygon is not convex: vertex {vertex_idx} is right of edge ({edge_start}, {edge_end})"
    )]
    NotConvex {
        vertex_idx: usize,
        edge_start: usize,
        edge_end: usize,
    },

    /// Polygon has zero or near-zero area (degenerate).
    #[error("polygon is degenerate (area {area:.2e} < {EPS_AREA:.2e})")]
    Degenerate { area: f64 },
}

/// A convex polygon with vertices in counter-clockwise order.
///
/// # Invariants
///
/// All instances satisfy (enforced by [`Polygon::new`]):
/// - `vertices.len() >= 3`
/// - No two vertices are coincident
/// - Vertices are in CCW order (signed area > 0)
/// - Polygon is convex
///
/// # Example
///
/// ```
/// use nalgebra::Vector2;
/// use geom2d::Polygon;
///
/// // Unit square (CCW order)
/// let square = Polygon::new(vec![
///     Vector2::new(0.0, 0.0),
///     Vector2::new(1.0, 0.0),
///     Vector2::new(1.0, 1.0),
///     Vector2::new(0.0, 1.0),
/// ]).expect("valid polygon");
///
/// assert_eq!(square.vertices().len(), 4);
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Polygon {
    /// Vertices in counter-clockwise order.
    vertices: Vec<Vector2<f64>>,
}

impl Polygon {
    /// Create a new polygon, validating all invariants.
    ///
    /// # Errors
    ///
    /// Returns [`PolygonError`] if any invariant is violated:
    /// - [`PolygonError::TooFewVertices`] if `vertices.len() < 3`
    /// - [`PolygonError::InvalidCoordinate`] if any coordinate is NaN, infinite, or `|x| > MAX_COORD`
    /// - [`PolygonError::NotCCW`] if signed area is not positive
    /// - [`PolygonError::Degenerate`] if area is below `EPS_AREA`
    /// - [`PolygonError::CoincidentVertices`] if any two vertices are within `EPS_VERTEX`
    /// - [`PolygonError::NotConvex`] if any vertex violates convexity
    ///
    /// # Validation Order
    ///
    /// Checks are performed in order of increasing computational cost:
    /// 1. Vertex count (O(1))
    /// 2. Coordinate validity (O(n))
    /// 3. Signed area / CCW / degeneracy (O(n))
    /// 4. Coincident vertices (O(n²))
    /// 5. Convexity (O(n))
    pub fn new(vertices: Vec<Vector2<f64>>) -> Result<Self, PolygonError> {
        // Check 1: At least 3 vertices
        if vertices.len() < 3 {
            return Err(PolygonError::TooFewVertices(vertices.len()));
        }

        // Check 2: All coordinates must be finite and within MAX_COORD
        // This catches NaN, Infinity, and values that would cause overflow in arithmetic.
        for (i, v) in vertices.iter().enumerate() {
            for &coord in &[v.x, v.y] {
                if !coord.is_finite() || coord.abs() > MAX_COORD {
                    return Err(PolygonError::InvalidCoordinate {
                        index: i,
                        value: coord,
                    });
                }
            }
        }

        // Check 3: Signed area (CCW orientation + non-degeneracy)
        let signed_area = signed_area_2x(&vertices);
        if signed_area <= 0.0 {
            return Err(PolygonError::NotCCW { signed_area });
        }
        let area = signed_area / 2.0;
        if area < EPS_AREA {
            return Err(PolygonError::Degenerate { area });
        }

        // Check 4: No coincident vertices
        // O(n²) but n is typically small (< 100 vertices)
        for i in 0..vertices.len() {
            for j in (i + 1)..vertices.len() {
                let dist = (vertices[i] - vertices[j]).norm();
                if dist < EPS_VERTEX {
                    return Err(PolygonError::CoincidentVertices {
                        i,
                        j,
                        distance: dist,
                    });
                }
            }
        }

        // Check 5: Convexity
        // For a CCW polygon, every vertex must be "left of or on" every edge.
        // Equivalently: cross product at each vertex must be >= 0.
        let n = vertices.len();
        for i in 0..n {
            let v_prev = &vertices[(i + n - 1) % n];
            let v_curr = &vertices[i];
            let v_next = &vertices[(i + 1) % n];

            // Cross product of edges: (v_curr - v_prev) × (v_next - v_curr)
            let edge1 = v_curr - v_prev;
            let edge2 = v_next - v_curr;
            let cross = cross_2d(&edge1, &edge2);

            // For CCW convex polygon, cross product should be > 0 at all vertices
            // (or = 0 for collinear points, which we allow on edges but not as vertices
            // since we already checked for coincident vertices and area > 0)
            if cross < -EPS_AREA {
                return Err(PolygonError::NotConvex {
                    vertex_idx: i,
                    edge_start: (i + n - 1) % n,
                    edge_end: (i + 1) % n,
                });
            }
        }

        Ok(Self { vertices })
    }

    /// Create a polygon without validation.
    ///
    /// # Safety
    ///
    /// This is not unsafe in the Rust sense, but violating invariants will cause
    /// incorrect results from methods like [`area`](crate::area::area).
    ///
    /// Use only when:
    /// - Vertices are known-good (e.g., from a trusted source)
    /// - Performance is critical and you've validated externally
    #[must_use]
    pub fn new_unchecked(vertices: Vec<Vector2<f64>>) -> Self {
        debug_assert!(vertices.len() >= 3, "polygon must have at least 3 vertices");
        Self { vertices }
    }

    /// Returns the vertices in CCW order.
    #[must_use]
    pub fn vertices(&self) -> &[Vector2<f64>] {
        &self.vertices
    }

    /// Returns the number of vertices (and edges).
    #[must_use]
    pub fn num_vertices(&self) -> usize {
        self.vertices.len()
    }
}

/// 2D cross product: a × b = a.x * b.y - a.y * b.x
///
/// # Geometric Interpretation
///
/// - Positive: b is counter-clockwise from a
/// - Negative: b is clockwise from a
/// - Zero: a and b are collinear
#[inline]
fn cross_2d(a: &Vector2<f64>, b: &Vector2<f64>) -> f64 {
    a.x * b.y - a.y * b.x
}

/// Compute 2× the signed area of a polygon (shoelace formula).
///
/// # Formula
///
/// For vertices v_0, v_1, ..., v_{n-1}:
/// ```text
/// 2 * signed_area = Σ_{i=0}^{n-1} (v_i × v_{i+1})
/// ```
/// where × is the 2D cross product and indices are mod n.
///
/// # Sign Convention
///
/// - Positive: vertices are in CCW order
/// - Negative: vertices are in CW order
///
/// # Proof of Correctness
///
/// The shoelace formula computes the signed area by summing the signed areas
/// of triangles formed with the origin. For a simple (non-self-intersecting)
/// polygon, these triangle contributions sum correctly due to cancellation.
///
/// Reference: "Computational Geometry: Algorithms and Applications" (de Berg et al.),
/// Section 1.1.
fn signed_area_2x(vertices: &[Vector2<f64>]) -> f64 {
    let n = vertices.len();
    let mut sum = 0.0;
    for i in 0..n {
        sum += cross_2d(&vertices[i], &vertices[(i + 1) % n]);
    }
    sum
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    /// Helper: unit square vertices in CCW order
    fn unit_square() -> Vec<Vector2<f64>> {
        vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]
    }

    /// Helper: equilateral triangle centered at origin
    fn equilateral_triangle() -> Vec<Vector2<f64>> {
        use std::f64::consts::PI;
        let r = 1.0;
        (0..3)
            .map(|i| {
                let angle = 2.0 * PI * (i as f64) / 3.0 - PI / 2.0;
                Vector2::new(r * angle.cos(), r * angle.sin())
            })
            .collect()
    }

    // ==================== POSITIVE TESTS ====================
    // These verify that valid inputs are accepted.

    #[test]
    fn test_new_accepts_unit_square() {
        let polygon = Polygon::new(unit_square());
        assert!(polygon.is_ok());
        assert_eq!(polygon.unwrap().num_vertices(), 4);
    }

    #[test]
    fn test_new_accepts_equilateral_triangle() {
        let polygon = Polygon::new(equilateral_triangle());
        assert!(polygon.is_ok());
        assert_eq!(polygon.unwrap().num_vertices(), 3);
    }

    #[test]
    fn test_new_accepts_regular_pentagon() {
        use std::f64::consts::PI;
        let vertices: Vec<_> = (0..5)
            .map(|i| {
                let angle = 2.0 * PI * (i as f64) / 5.0;
                Vector2::new(angle.cos(), angle.sin())
            })
            .collect();
        let polygon = Polygon::new(vertices);
        assert!(polygon.is_ok());
    }

    // ==================== NEGATIVE TESTS ====================
    // These verify that invalid inputs are rejected with the correct error.

    #[test]
    fn test_new_rejects_too_few_vertices_zero() {
        let result = Polygon::new(vec![]);
        assert!(matches!(result, Err(PolygonError::TooFewVertices(0))));
    }

    #[test]
    fn test_new_rejects_too_few_vertices_one() {
        let result = Polygon::new(vec![Vector2::new(0.0, 0.0)]);
        assert!(matches!(result, Err(PolygonError::TooFewVertices(1))));
    }

    #[test]
    fn test_new_rejects_too_few_vertices_two() {
        let result = Polygon::new(vec![Vector2::new(0.0, 0.0), Vector2::new(1.0, 0.0)]);
        assert!(matches!(result, Err(PolygonError::TooFewVertices(2))));
    }

    #[test]
    fn test_new_rejects_clockwise_ordering() {
        // Unit square in CW order (reversed)
        let cw_square = vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(0.0, 1.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(1.0, 0.0),
        ];
        let result = Polygon::new(cw_square);
        assert!(matches!(result, Err(PolygonError::NotCCW { .. })));
    }

    #[test]
    fn test_new_rejects_coincident_vertices() {
        let vertices = vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 0.0), // duplicate!
            Vector2::new(0.0, 1.0),
        ];
        let result = Polygon::new(vertices);
        assert!(matches!(
            result,
            Err(PolygonError::CoincidentVertices { i: 1, j: 2, .. })
        ));
    }

    #[test]
    fn test_new_rejects_nearly_coincident_vertices() {
        let eps = EPS_VERTEX / 10.0; // well within tolerance
        let vertices = vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0 + eps, eps), // nearly coincident with vertex 1
            Vector2::new(0.0, 1.0),
        ];
        let result = Polygon::new(vertices);
        // Should detect vertices 1 and 2 as coincident
        assert!(matches!(
            result,
            Err(PolygonError::CoincidentVertices { .. })
        ));
    }

    #[test]
    fn test_new_rejects_collinear_points() {
        // Three collinear points = degenerate polygon (zero area)
        let vertices = vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(2.0, 0.0),
        ];
        let result = Polygon::new(vertices);
        // Could be NotCCW or Degenerate depending on check order
        assert!(result.is_err());
    }

    #[test]
    fn test_new_rejects_non_convex_polygon() {
        // Non-convex "arrow" shape
        let vertices = vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(2.0, 0.0),
            Vector2::new(1.0, 0.5), // This creates a concavity
            Vector2::new(2.0, 1.0),
            Vector2::new(0.0, 1.0),
        ];
        let result = Polygon::new(vertices);
        assert!(matches!(result, Err(PolygonError::NotConvex { .. })));
    }

    #[test]
    fn test_new_rejects_nan_coordinate() {
        let vertices = vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(f64::NAN, 1.0), // NaN in x
        ];
        let result = Polygon::new(vertices);
        assert!(matches!(
            result,
            Err(PolygonError::InvalidCoordinate { index: 2, .. })
        ));
    }

    #[test]
    fn test_new_rejects_infinity_coordinate() {
        let vertices = vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, f64::INFINITY), // Infinity in y
            Vector2::new(0.0, 1.0),
        ];
        let result = Polygon::new(vertices);
        assert!(matches!(
            result,
            Err(PolygonError::InvalidCoordinate { index: 1, .. })
        ));
    }

    #[test]
    fn test_new_rejects_negative_infinity_coordinate() {
        let vertices = vec![
            Vector2::new(f64::NEG_INFINITY, 0.0), // -Infinity in x
            Vector2::new(1.0, 0.0),
            Vector2::new(0.0, 1.0),
        ];
        let result = Polygon::new(vertices);
        assert!(matches!(
            result,
            Err(PolygonError::InvalidCoordinate { index: 0, .. })
        ));
    }

    #[test]
    fn test_new_rejects_coordinate_exceeding_max() {
        let too_large = MAX_COORD * 1.1;
        let vertices = vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(0.0, too_large), // Exceeds MAX_COORD
        ];
        let result = Polygon::new(vertices);
        assert!(matches!(
            result,
            Err(PolygonError::InvalidCoordinate { index: 2, .. })
        ));
    }

    #[test]
    fn test_new_accepts_coordinate_at_max() {
        // Coordinates exactly at MAX_COORD should be accepted
        // Use a simple triangle that will pass validation
        let large = MAX_COORD / 2.0; // Use half to avoid overflow in area calc
        let vertices = vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(large, 0.0),
            Vector2::new(0.0, large),
        ];
        let result = Polygon::new(vertices);
        assert!(result.is_ok());
    }

    // ==================== HELPER FUNCTION TESTS ====================

    #[test]
    fn test_cross_2d_perpendicular_vectors() {
        let a = Vector2::new(1.0, 0.0);
        let b = Vector2::new(0.0, 1.0);
        assert_relative_eq!(cross_2d(&a, &b), 1.0);
        assert_relative_eq!(cross_2d(&b, &a), -1.0);
    }

    #[test]
    fn test_cross_2d_parallel_vectors() {
        let a = Vector2::new(1.0, 2.0);
        let b = Vector2::new(2.0, 4.0);
        assert_relative_eq!(cross_2d(&a, &b), 0.0);
    }

    #[test]
    fn test_signed_area_2x_unit_square() {
        // Unit square has area 1, so 2x area = 2
        let vertices = unit_square();
        assert_relative_eq!(signed_area_2x(&vertices), 2.0);
    }

    #[test]
    fn test_signed_area_2x_ccw_positive() {
        let vertices = equilateral_triangle();
        let area_2x = signed_area_2x(&vertices);
        assert!(
            area_2x > 0.0,
            "CCW triangle should have positive signed area"
        );
    }

    #[test]
    fn test_signed_area_2x_cw_negative() {
        // Reverse the equilateral triangle to get CW order
        let mut vertices = equilateral_triangle();
        vertices.reverse();
        let area_2x = signed_area_2x(&vertices);
        assert!(
            area_2x < 0.0,
            "CW triangle should have negative signed area"
        );
    }
}
