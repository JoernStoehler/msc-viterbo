//! Geometry primitives: symplectic form, quaternion matrices, affine maps/functions, polygons.

use nalgebra::{Matrix2, Matrix4, Vector2, Vector4};

use crate::tol::EPS;

// ============================================================================
// Quaternion Matrices (J, K) and Symplectic Form
// ============================================================================

/// The standard complex structure J: (q₁, q₂, p₁, p₂) ↦ (-p₁, -p₂, q₁, q₂)
#[rustfmt::skip]
pub const J_MATRIX: Matrix4<f64> = Matrix4::new(
    0.0,  0.0, -1.0,  0.0,
    0.0,  0.0,  0.0, -1.0,
    1.0,  0.0,  0.0,  0.0,
    0.0,  1.0,  0.0,  0.0,
);

/// The quaternion K matrix.
#[rustfmt::skip]
pub const K_MATRIX: Matrix4<f64> = Matrix4::new(
    0.0, -1.0,  0.0,  0.0,
    1.0,  0.0,  0.0,  0.0,
    0.0,  0.0,  0.0,  1.0,
    0.0,  0.0, -1.0,  0.0,
);

/// Symplectic form in R⁴: ω(x, y) = ⟨Jx, y⟩
pub fn symplectic_form(x: &Vector4<f64>, y: &Vector4<f64>) -> f64 {
    (J_MATRIX * x).dot(y)
}

/// Standard 2D symplectic form: ω(x, y) = x₁y₂ - x₂y₁
pub fn symplectic_form_2d(x: &Vector2<f64>, y: &Vector2<f64>) -> f64 {
    x[0] * y[1] - x[1] * y[0]
}

// ============================================================================
// Polygon2D
// ============================================================================

/// A 2D convex polygon represented by its vertices in CCW order.
#[derive(Debug, Clone)]
pub struct Polygon2D {
    pub vertices: Vec<Vector2<f64>>,
}

impl Polygon2D {
    pub fn new(vertices: Vec<Vector2<f64>>) -> Self {
        Polygon2D { vertices }
    }

    pub fn is_empty(&self) -> bool {
        self.vertices.len() < 3 || self.area() < EPS
    }

    /// Shoelace formula for polygon area.
    pub fn area(&self) -> f64 {
        if self.vertices.len() < 3 {
            return 0.0;
        }
        let mut area = 0.0;
        for i in 0..self.vertices.len() {
            let j = (i + 1) % self.vertices.len();
            area += self.vertices[i][0] * self.vertices[j][1];
            area -= self.vertices[j][0] * self.vertices[i][1];
        }
        (area / 2.0).abs()
    }
}

/// Sort 2D points in counter-clockwise order around their centroid.
pub fn sort_ccw(mut points: Vec<Vector2<f64>>) -> Vec<Vector2<f64>> {
    if points.len() < 3 {
        return points;
    }

    let centroid: Vector2<f64> =
        points.iter().copied().sum::<Vector2<f64>>() / points.len() as f64;

    points.sort_by(|a, b| {
        let angle_a = (a[1] - centroid[1]).atan2(a[0] - centroid[0]);
        let angle_b = (b[1] - centroid[1]).atan2(b[0] - centroid[0]);
        angle_a.partial_cmp(&angle_b).unwrap()
    });

    points
}

/// Test if point p is on the left side (or on) the directed edge e1 -> e2.
fn is_left_of_edge(p: &Vector2<f64>, e1: &Vector2<f64>, e2: &Vector2<f64>) -> bool {
    let cross = (e2[0] - e1[0]) * (p[1] - e1[1]) - (e2[1] - e1[1]) * (p[0] - e1[0]);
    cross >= -EPS
}

/// Line-line intersection.
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
        // Parallel lines; return midpoint as fallback
        return (a1 + b1) / 2.0;
    }

    let t = ((b1[0] - a1[0]) * d2[1] - (b1[1] - a1[1]) * d2[0]) / cross;
    a1 + d1 * t
}

/// Clip polygon by half-plane defined by edge (p1 -> p2).
/// Keeps points on the left side of the directed edge.
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

/// Compute intersection of two convex polygons using Sutherland-Hodgman.
pub fn intersect_polygons(p1: &Polygon2D, p2: &Polygon2D) -> Polygon2D {
    if p1.vertices.len() < 3 || p2.vertices.len() < 3 {
        return Polygon2D::new(vec![]);
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

/// Test if point is inside a convex polygon (CCW vertices).
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

// ============================================================================
// AffineMap2D
// ============================================================================

/// An affine map f(x) = Ax + b in 2D.
#[derive(Debug, Clone)]
pub struct AffineMap2D {
    pub matrix: Matrix2<f64>,
    pub offset: Vector2<f64>,
}

impl AffineMap2D {
    pub fn identity() -> Self {
        AffineMap2D {
            matrix: Matrix2::identity(),
            offset: Vector2::zeros(),
        }
    }

    pub fn apply(&self, x: &Vector2<f64>) -> Vector2<f64> {
        self.matrix * x + self.offset
    }
}

/// Compose f ∘ g: (Ax + b) ∘ (Cx + d) = (AC)x + (Ad + b)
pub fn compose_affine(f: &AffineMap2D, g: &AffineMap2D) -> AffineMap2D {
    AffineMap2D {
        matrix: f.matrix * g.matrix,
        offset: f.matrix * g.offset + f.offset,
    }
}

/// Apply affine map to all vertices of a polygon.
pub fn apply_affine_map(f: &AffineMap2D, polygon: &Polygon2D) -> Polygon2D {
    Polygon2D::new(polygon.vertices.iter().map(|v| f.apply(v)).collect())
}

// ============================================================================
// AffineFunc
// ============================================================================

/// An affine function f(x) = ⟨g, x⟩ + c.
#[derive(Debug, Clone)]
pub struct AffineFunc {
    pub gradient: Vector2<f64>,
    pub constant: f64,
}

impl AffineFunc {
    pub fn zero() -> Self {
        AffineFunc {
            gradient: Vector2::zeros(),
            constant: 0.0,
        }
    }

    pub fn eval(&self, x: &Vector2<f64>) -> f64 {
        self.gradient.dot(x) + self.constant
    }
}

/// Add two affine functions.
pub fn add_affine_funcs(f: &AffineFunc, g: &AffineFunc) -> AffineFunc {
    AffineFunc {
        gradient: f.gradient + g.gradient,
        constant: f.constant + g.constant,
    }
}

/// Compose affine function with affine map: f(Ax + b) where f(y) = g·y + c
/// Result: g·(Ax + b) + c = (Aᵀg)·x + (g·b + c)
pub fn compose_with_map(f: &AffineFunc, map: &AffineMap2D) -> AffineFunc {
    AffineFunc {
        gradient: map.matrix.transpose() * f.gradient,
        constant: f.gradient.dot(&map.offset) + f.constant,
    }
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    #[test]
    fn test_quaternion_relations() {
        let i4 = Matrix4::identity();

        // J² = -I
        assert_relative_eq!((J_MATRIX * J_MATRIX), -i4, epsilon = 1e-10);

        // K² = -I
        assert_relative_eq!((K_MATRIX * K_MATRIX), -i4, epsilon = 1e-10);

        // JK = -KJ
        assert_relative_eq!(J_MATRIX * K_MATRIX, -(K_MATRIX * J_MATRIX), epsilon = 1e-10);
    }

    #[test]
    fn test_symplectic_form_basis() {
        let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let e2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
        let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
        let e4 = Vector4::new(0.0, 0.0, 0.0, 1.0);

        assert_relative_eq!(symplectic_form(&e1, &e3), 1.0, epsilon = 1e-10);
        assert_relative_eq!(symplectic_form(&e2, &e4), 1.0, epsilon = 1e-10);
        assert_relative_eq!(symplectic_form(&e1, &e2), 0.0, epsilon = 1e-10);
        assert_relative_eq!(symplectic_form(&e3, &e4), 0.0, epsilon = 1e-10);

        // Antisymmetry
        assert_relative_eq!(symplectic_form(&e3, &e1), -1.0, epsilon = 1e-10);
    }

    #[test]
    fn test_polygon_area() {
        // Unit square
        let square = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);
        assert_relative_eq!(square.area(), 1.0, epsilon = 1e-10);
    }

    #[test]
    fn test_affine_composition() {
        // f(x) = 2x + [1, 0]
        let f = AffineMap2D {
            matrix: Matrix2::new(2.0, 0.0, 0.0, 2.0),
            offset: Vector2::new(1.0, 0.0),
        };
        // g(x) = x + [0, 1]
        let g = AffineMap2D {
            matrix: Matrix2::identity(),
            offset: Vector2::new(0.0, 1.0),
        };

        // f∘g(x) = 2(x + [0,1]) + [1,0] = 2x + [1, 2]
        let fg = compose_affine(&f, &g);

        let x = Vector2::new(1.0, 1.0);
        let expected = Vector2::new(3.0, 4.0);
        assert_relative_eq!(fg.apply(&x), expected, epsilon = 1e-10);
    }

    #[test]
    fn test_point_in_polygon() {
        let triangle = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(2.0, 0.0),
            Vector2::new(1.0, 2.0),
        ]);

        assert!(point_in_polygon(&Vector2::new(1.0, 0.5), &triangle));
        assert!(!point_in_polygon(&Vector2::new(0.0, 2.0), &triangle));
    }
}
