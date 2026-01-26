//! Geometry utilities: symplectic form, quaternion matrices, 2D polygon operations.
//!
//! See spec §1.3-1.4 for symplectic form, §1.9 for quaternion structure,
//! §1.17 for polygon operations.

use nalgebra::{Matrix4, Vector2, Vector4};

use crate::consts::EPS;

// =============================================================================
// Symplectic Structure (§1.4)
// =============================================================================

/// The standard complex structure J as a 4×4 matrix.
///
/// J(q₁, q₂, p₁, p₂) = (-p₁, -p₂, q₁, q₂)
///
/// In matrix form (acting on column vectors):
/// ```text
/// J = | 0  0 -1  0 |
///     | 0  0  0 -1 |
///     | 1  0  0  0 |
///     | 0  1  0  0 |
/// ```
#[rustfmt::skip]
pub const J_MATRIX: Matrix4<f64> = Matrix4::new(
    0.0,  0.0, -1.0,  0.0,
    0.0,  0.0,  0.0, -1.0,
    1.0,  0.0,  0.0,  0.0,
    0.0,  1.0,  0.0,  0.0,
);

/// The quaternion K matrix (§1.9).
///
/// K = | 0 -1  0  0 |
///     | 1  0  0  0 |
///     | 0  0  0  1 |
///     | 0  0 -1  0 |
#[rustfmt::skip]
pub const K_MATRIX: Matrix4<f64> = Matrix4::new(
    0.0, -1.0,  0.0,  0.0,
    1.0,  0.0,  0.0,  0.0,
    0.0,  0.0,  0.0,  1.0,
    0.0,  0.0, -1.0,  0.0,
);

/// Compute the symplectic form ω(x, y) in R⁴.
///
/// ω(x, y) = ⟨Jx, y⟩ = q₁p₁' + q₂p₂' - p₁q₁' - p₂q₂'
///
/// where x = (q₁, q₂, p₁, p₂) and y = (q₁', q₂', p₁', p₂').
#[inline]
pub fn symplectic_form(x: &Vector4<f64>, y: &Vector4<f64>) -> f64 {
    (J_MATRIX * x).dot(y)
}

/// Compute the standard 2D symplectic form ω_std(x, y) = x₁y₂ - x₂y₁.
#[inline]
pub fn symplectic_form_2d(x: &Vector2<f64>, y: &Vector2<f64>) -> f64 {
    x[0] * y[1] - x[1] * y[0]
}

// =============================================================================
// 2D Polygon Operations (§1.17)
// =============================================================================

/// A 2D convex polygon represented by its vertices in CCW order.
#[derive(Debug, Clone, Default)]
pub struct Polygon2D {
    pub vertices: Vec<Vector2<f64>>,
}

impl Polygon2D {
    /// Create a new polygon from vertices (must be in CCW order).
    pub fn new(vertices: Vec<Vector2<f64>>) -> Self {
        Self { vertices }
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
}

/// Sort 2D points in counter-clockwise order around their centroid.
///
/// Precondition: points form a convex polygon (no collinearity checks).
pub fn sort_ccw(mut points: Vec<Vector2<f64>>) -> Vec<Vector2<f64>> {
    if points.len() < 3 {
        return points;
    }

    // Compute centroid
    let sum: Vector2<f64> = points.iter().copied().sum();
    let centroid = sum / points.len() as f64;

    // Sort by angle from centroid
    points.sort_by(|a, b| {
        let angle_a = (a[1] - centroid[1]).atan2(a[0] - centroid[0]);
        let angle_b = (b[1] - centroid[1]).atan2(b[0] - centroid[0]);
        angle_a.partial_cmp(&angle_b).unwrap()
    });

    points
}

/// Test if point p is on the left side of the directed edge e1 -> e2.
///
/// Uses cross product: (e2 - e1) × (p - e1) >= 0 means left or on edge.
#[inline]
fn is_left_of_edge(p: &Vector2<f64>, e1: &Vector2<f64>, e2: &Vector2<f64>) -> bool {
    let cross = (e2[0] - e1[0]) * (p[1] - e1[1]) - (e2[1] - e1[1]) * (p[0] - e1[0]);
    cross >= -EPS // Include points on the edge
}

/// Compute the intersection point of two lines (a1->a2) and (b1->b2).
fn line_intersection(
    a1: &Vector2<f64>,
    a2: &Vector2<f64>,
    b1: &Vector2<f64>,
    b2: &Vector2<f64>,
) -> Vector2<f64> {
    let d1 = a2 - a1;
    let d2 = b2 - b1;
    let cross = d1[0] * d2[1] - d1[1] * d2[0];

    if cross.abs() < EPS {
        // Lines are parallel; return midpoint as fallback
        return (a1 + b1) / 2.0;
    }

    let t = ((b1[0] - a1[0]) * d2[1] - (b1[1] - a1[1]) * d2[0]) / cross;
    a1 + d1 * t
}

/// Clip a polygon by the half-plane to the left of directed edge (p1 -> p2).
///
/// Uses Sutherland-Hodgman clipping for one edge.
fn clip_polygon_by_halfplane(
    polygon: &[Vector2<f64>],
    p1: &Vector2<f64>,
    p2: &Vector2<f64>,
) -> Vec<Vector2<f64>> {
    let mut output = Vec::new();

    for i in 0..polygon.len() {
        let j = (i + 1) % polygon.len();
        let curr = &polygon[i];
        let next = &polygon[j];

        let curr_inside = is_left_of_edge(curr, p1, p2);
        let next_inside = is_left_of_edge(next, p1, p2);

        if curr_inside {
            output.push(*curr);
            if !next_inside {
                output.push(line_intersection(curr, next, p1, p2));
            }
        } else if next_inside {
            output.push(line_intersection(curr, next, p1, p2));
        }
    }

    output
}

/// Compute the intersection of two convex polygons using Sutherland-Hodgman.
///
/// Returns an empty polygon if the intersection is empty.
pub fn intersect_polygons(p1: &Polygon2D, p2: &Polygon2D) -> Polygon2D {
    if p1.is_empty() || p2.is_empty() {
        return Polygon2D::default();
    }

    let mut result = p1.vertices.clone();

    for i in 0..p2.vertices.len() {
        if result.is_empty() {
            break;
        }
        let j = (i + 1) % p2.vertices.len();
        let edge_start = &p2.vertices[i];
        let edge_end = &p2.vertices[j];

        result = clip_polygon_by_halfplane(&result, edge_start, edge_end);
    }

    Polygon2D::new(result)
}

/// Test if a point is inside a convex polygon (CCW vertices).
///
/// For convex polygons: point is inside iff it's on the left of all edges.
pub fn point_in_polygon(p: &Vector2<f64>, polygon: &Polygon2D) -> bool {
    if polygon.vertices.len() < 3 {
        return false;
    }

    for i in 0..polygon.vertices.len() {
        let j = (i + 1) % polygon.vertices.len();
        if !is_left_of_edge(p, &polygon.vertices[i], &polygon.vertices[j]) {
            return false;
        }
    }
    true
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    #[test]
    fn test_j_matrix_squared_is_minus_identity() {
        let j_squared = J_MATRIX * J_MATRIX;
        assert_relative_eq!(j_squared, -Matrix4::identity(), epsilon = EPS);
    }

    #[test]
    fn test_k_matrix_squared_is_minus_identity() {
        let k_squared = K_MATRIX * K_MATRIX;
        assert_relative_eq!(k_squared, -Matrix4::identity(), epsilon = EPS);
    }

    #[test]
    fn test_jk_anticommute() {
        let jk = J_MATRIX * K_MATRIX;
        let kj = K_MATRIX * J_MATRIX;
        assert_relative_eq!(jk, -kj, epsilon = EPS);
    }

    #[test]
    fn test_symplectic_form_standard_basis() {
        let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let e2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
        let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
        let e4 = Vector4::new(0.0, 0.0, 0.0, 1.0);

        // Symplectic pairs
        assert_relative_eq!(symplectic_form(&e1, &e3), 1.0, epsilon = EPS);
        assert_relative_eq!(symplectic_form(&e2, &e4), 1.0, epsilon = EPS);

        // Lagrangian pairs
        assert_relative_eq!(symplectic_form(&e1, &e2), 0.0, epsilon = EPS);
        assert_relative_eq!(symplectic_form(&e3, &e4), 0.0, epsilon = EPS);

        // Antisymmetry
        assert_relative_eq!(symplectic_form(&e3, &e1), -1.0, epsilon = EPS);
    }

    #[test]
    fn test_symplectic_form_antisymmetric() {
        let x = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let y = Vector4::new(5.0, 6.0, 7.0, 8.0);

        assert_relative_eq!(
            symplectic_form(&x, &y),
            -symplectic_form(&y, &x),
            epsilon = EPS
        );
    }

    #[test]
    fn test_sort_ccw_square() {
        // Square vertices in random order
        let points = vec![
            Vector2::new(1.0, 1.0),
            Vector2::new(-1.0, -1.0),
            Vector2::new(1.0, -1.0),
            Vector2::new(-1.0, 1.0),
        ];

        let sorted = sort_ccw(points);

        // Check that angles are increasing
        let centroid = Vector2::new(0.0, 0.0);
        for i in 0..sorted.len() {
            let j = (i + 1) % sorted.len();
            let angle_i = (sorted[i][1] - centroid[1]).atan2(sorted[i][0] - centroid[0]);
            let mut angle_j = (sorted[j][1] - centroid[1]).atan2(sorted[j][0] - centroid[0]);
            if j == 0 {
                angle_j += 2.0 * std::f64::consts::PI;
            }
            assert!(angle_i < angle_j);
        }
    }

    #[test]
    fn test_polygon_area_unit_square() {
        let square = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);
        assert_relative_eq!(square.area(), 1.0, epsilon = EPS);
    }

    #[test]
    fn test_intersect_polygons_full_overlap() {
        let square = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);
        let intersection = intersect_polygons(&square, &square);
        assert_relative_eq!(intersection.area(), 1.0, epsilon = EPS);
    }

    #[test]
    fn test_intersect_polygons_partial_overlap() {
        let square1 = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);
        let square2 = Polygon2D::new(vec![
            Vector2::new(0.5, 0.0),
            Vector2::new(1.5, 0.0),
            Vector2::new(1.5, 1.0),
            Vector2::new(0.5, 1.0),
        ]);
        let intersection = intersect_polygons(&square1, &square2);
        assert_relative_eq!(intersection.area(), 0.5, epsilon = EPS);
    }

    #[test]
    fn test_intersect_polygons_no_overlap() {
        let square1 = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);
        let square2 = Polygon2D::new(vec![
            Vector2::new(2.0, 0.0),
            Vector2::new(3.0, 0.0),
            Vector2::new(3.0, 1.0),
            Vector2::new(2.0, 1.0),
        ]);
        let intersection = intersect_polygons(&square1, &square2);
        assert!(intersection.is_empty() || intersection.area() < EPS);
    }

    #[test]
    fn test_point_in_polygon() {
        let square = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);

        assert!(point_in_polygon(&Vector2::new(0.5, 0.5), &square));
        assert!(!point_in_polygon(&Vector2::new(2.0, 0.5), &square));
    }
}
