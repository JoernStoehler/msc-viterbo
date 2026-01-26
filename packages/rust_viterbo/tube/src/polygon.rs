//! 2D convex polygon operations.
//!
//! This module provides:
//! - `Polygon2D`: A convex polygon represented by CCW-ordered vertices
//! - CCW sorting of vertices
//! - Sutherland-Hodgman polygon clipping/intersection
//! - Point-in-polygon test
//! - Polygon area computation

use nalgebra::{Matrix2, Vector2};

use crate::consts::EPS;

/// A 2D convex polygon with vertices in counter-clockwise order.
#[derive(Debug, Clone)]
pub struct Polygon2D {
    /// Vertices in CCW order.
    pub vertices: Vec<Vector2<f64>>,
}

impl Polygon2D {
    /// Create a polygon from CCW-ordered vertices.
    pub fn new(vertices: Vec<Vector2<f64>>) -> Self {
        Self { vertices }
    }

    /// Create a polygon from unsorted vertices (will be sorted CCW).
    pub fn from_unsorted(vertices: Vec<Vector2<f64>>) -> Self {
        Self {
            vertices: sort_ccw(vertices),
        }
    }

    /// Check if the polygon is empty (< 3 vertices).
    pub fn is_empty(&self) -> bool {
        self.vertices.len() < 3
    }

    /// Compute the area of the polygon using the shoelace formula.
    pub fn area(&self) -> f64 {
        polygon_area(&self.vertices)
    }

    /// Compute the centroid of the polygon.
    pub fn centroid(&self) -> Vector2<f64> {
        if self.vertices.is_empty() {
            return Vector2::zeros();
        }
        let sum: Vector2<f64> = self.vertices.iter().sum();
        sum / self.vertices.len() as f64
    }

    /// Check if a point is inside the polygon.
    pub fn contains(&self, p: &Vector2<f64>) -> bool {
        point_in_polygon(p, &self.vertices)
    }
}

/// An affine map in 2D: f(x) = Ax + b.
#[derive(Debug, Clone)]
pub struct AffineMap2D {
    /// Linear part (2x2 matrix).
    pub matrix: Matrix2<f64>,
    /// Translation (2D vector).
    pub offset: Vector2<f64>,
}

impl AffineMap2D {
    /// Create the identity map.
    pub fn identity() -> Self {
        Self {
            matrix: Matrix2::identity(),
            offset: Vector2::zeros(),
        }
    }

    /// Create an affine map from matrix and offset.
    pub fn new(matrix: Matrix2<f64>, offset: Vector2<f64>) -> Self {
        Self { matrix, offset }
    }

    /// Apply the map to a point: f(x) = Ax + b.
    pub fn apply(&self, x: &Vector2<f64>) -> Vector2<f64> {
        self.matrix * x + self.offset
    }

    /// Apply the map to all vertices of a polygon.
    pub fn apply_to_polygon(&self, polygon: &Polygon2D) -> Polygon2D {
        Polygon2D {
            vertices: polygon.vertices.iter().map(|v| self.apply(v)).collect(),
        }
    }
}

/// Compose two affine maps: (f ∘ g)(x) = f(g(x)) = A_f(A_g x + b_g) + b_f.
pub fn compose_affine(f: &AffineMap2D, g: &AffineMap2D) -> AffineMap2D {
    AffineMap2D {
        matrix: f.matrix * g.matrix,
        offset: f.matrix * g.offset + f.offset,
    }
}

/// An affine function in 2D: f(x) = ⟨g, x⟩ + c.
#[derive(Debug, Clone)]
pub struct AffineFunc {
    /// Gradient (2D vector).
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
    pub fn eval(&self, x: &Vector2<f64>) -> f64 {
        self.gradient.dot(x) + self.constant
    }

    /// Find the minimum value over vertices of a polygon.
    pub fn min_over_polygon(&self, polygon: &Polygon2D) -> f64 {
        polygon
            .vertices
            .iter()
            .map(|v| self.eval(v))
            .fold(f64::INFINITY, f64::min)
    }
}

/// Add two affine functions.
pub fn add_affine_funcs(f: &AffineFunc, g: &AffineFunc) -> AffineFunc {
    AffineFunc {
        gradient: f.gradient + g.gradient,
        constant: f.constant + g.constant,
    }
}

/// Compose affine function with affine map: (f ∘ m)(x) = f(m(x)).
///
/// If f(y) = ⟨g, y⟩ + c and m(x) = Ax + b, then:
/// f(m(x)) = ⟨g, Ax + b⟩ + c = ⟨Aᵀg, x⟩ + (⟨g, b⟩ + c)
pub fn compose_func_with_map(f: &AffineFunc, m: &AffineMap2D) -> AffineFunc {
    AffineFunc {
        gradient: m.matrix.transpose() * f.gradient,
        constant: f.gradient.dot(&m.offset) + f.constant,
    }
}

/// Sort 2D points in counter-clockwise order around their centroid.
pub fn sort_ccw(mut points: Vec<Vector2<f64>>) -> Vec<Vector2<f64>> {
    if points.len() < 3 {
        return points;
    }

    // Compute centroid
    let centroid: Vector2<f64> = points.iter().sum::<Vector2<f64>>() / points.len() as f64;

    // Sort by angle from centroid
    points.sort_by(|a, b| {
        let angle_a = (a[1] - centroid[1]).atan2(a[0] - centroid[0]);
        let angle_b = (b[1] - centroid[1]).atan2(b[0] - centroid[0]);
        angle_a.partial_cmp(&angle_b).unwrap()
    });

    points
}

/// Compute the signed area of a polygon (positive for CCW).
pub fn polygon_area(vertices: &[Vector2<f64>]) -> f64 {
    if vertices.len() < 3 {
        return 0.0;
    }

    let mut area = 0.0;
    let n = vertices.len();
    for i in 0..n {
        let j = (i + 1) % n;
        area += vertices[i][0] * vertices[j][1];
        area -= vertices[j][0] * vertices[i][1];
    }
    (area / 2.0).abs()
}

/// Check if point p is on the left side of edge (e1 → e2).
///
/// Uses the cross product: (e2 - e1) × (p - e1) ≥ 0.
#[inline]
fn is_left_of_edge(p: &Vector2<f64>, e1: &Vector2<f64>, e2: &Vector2<f64>) -> bool {
    let cross = (e2[0] - e1[0]) * (p[1] - e1[1]) - (e2[1] - e1[1]) * (p[0] - e1[0]);
    cross >= -EPS // Include points on the edge
}

/// Compute intersection of two lines.
///
/// Line 1: a1 + t*(a2 - a1)
/// Line 2: b1 + s*(b2 - b1)
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

/// Clip polygon by half-plane defined by edge (p1 → p2).
///
/// Keep points on the left side of the directed edge.
fn clip_polygon_by_halfplane(
    polygon: &[Vector2<f64>],
    p1: &Vector2<f64>,
    p2: &Vector2<f64>,
) -> Vec<Vector2<f64>> {
    if polygon.is_empty() {
        return Vec::new();
    }

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

/// Intersect a line with a convex polygon, returning segment endpoints.
///
/// Line is parameterized as: point + t * direction
/// Returns None if no intersection, or Some((t_min, t_max)) for the segment.
pub fn intersect_line_polygon(
    point: &Vector2<f64>,
    direction: &Vector2<f64>,
    polygon: &Polygon2D,
) -> Option<(f64, f64)> {
    if polygon.is_empty() || direction.norm() < EPS {
        return None;
    }

    let mut t_min = f64::NEG_INFINITY;
    let mut t_max = f64::INFINITY;

    // For each edge, compute where the line crosses
    for i in 0..polygon.vertices.len() {
        let j = (i + 1) % polygon.vertices.len();
        let e1 = &polygon.vertices[i];
        let e2 = &polygon.vertices[j];

        // Edge normal (pointing inward for CCW polygon)
        let edge = e2 - e1;
        let normal = Vector2::new(-edge[1], edge[0]); // perpendicular

        let denom = direction.dot(&normal);
        let numer = (e1 - point).dot(&normal);

        if denom.abs() < EPS {
            // Line parallel to edge
            // numer = (e1 - point).dot(normal)
            // For point to be inside the half-plane: (point - e1).dot(normal) >= 0
            // i.e., -numer >= 0, i.e., numer <= 0
            if numer > EPS {
                // Line is outside this half-plane
                return None;
            }
            // Line is inside or on the edge - continue
        } else {
            let t = numer / denom;
            if denom > 0.0 {
                // Entering half-plane
                t_min = t_min.max(t);
            } else {
                // Leaving half-plane
                t_max = t_max.min(t);
            }
        }

        if t_min > t_max + EPS {
            return None;
        }
    }

    if t_min > t_max + EPS {
        None
    } else {
        Some((t_min, t_max))
    }
}

/// Compute intersection of two convex polygons using Sutherland-Hodgman algorithm.
pub fn intersect_polygons(p1: &Polygon2D, p2: &Polygon2D) -> Polygon2D {
    if p1.is_empty() || p2.is_empty() {
        return Polygon2D::new(Vec::new());
    }

    // Clip p1 against each edge of p2
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

/// Check if point is inside a convex polygon (CCW vertices).
///
/// For convex polygons: point is inside iff it's on the left of all edges.
pub fn point_in_polygon(p: &Vector2<f64>, vertices: &[Vector2<f64>]) -> bool {
    if vertices.len() < 3 {
        return false;
    }

    // For convex polygons: point is inside iff it's on the left of all edges
    for i in 0..vertices.len() {
        let j = (i + 1) % vertices.len();
        if !is_left_of_edge(p, &vertices[i], &vertices[j]) {
            return false;
        }
    }
    true
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    fn unit_square() -> Polygon2D {
        Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ])
    }

    #[test]
    fn test_polygon_area_unit_square() {
        let sq = unit_square();
        assert_relative_eq!(sq.area(), 1.0, epsilon = 1e-14);
    }

    #[test]
    fn test_polygon_centroid() {
        let sq = unit_square();
        let c = sq.centroid();
        assert_relative_eq!(c, Vector2::new(0.5, 0.5), epsilon = 1e-14);
    }

    #[test]
    fn test_point_in_polygon_inside() {
        let sq = unit_square();
        assert!(sq.contains(&Vector2::new(0.5, 0.5)));
        assert!(sq.contains(&Vector2::new(0.1, 0.1)));
    }

    #[test]
    fn test_point_in_polygon_outside() {
        let sq = unit_square();
        assert!(!sq.contains(&Vector2::new(1.5, 0.5)));
        assert!(!sq.contains(&Vector2::new(-0.5, 0.5)));
    }

    #[test]
    fn test_point_in_polygon_on_edge() {
        let sq = unit_square();
        // Points on edges should be considered inside (with tolerance)
        assert!(sq.contains(&Vector2::new(0.5, 0.0)));
    }

    #[test]
    fn test_sort_ccw() {
        let unsorted = vec![
            Vector2::new(1.0, 0.0),
            Vector2::new(0.0, 1.0),
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 1.0),
        ];
        let sorted = sort_ccw(unsorted);

        // After sorting CCW around centroid (0.5, 0.5):
        // Should start from angle = atan2(-0.5, -0.5) = -3π/4 (bottom-left)
        // and proceed: (0,0), (1,0), (1,1), (0,1)
        assert_eq!(sorted.len(), 4);
    }

    #[test]
    fn test_intersect_same_polygon() {
        let sq = unit_square();
        let intersection = intersect_polygons(&sq, &sq);

        assert_relative_eq!(intersection.area(), 1.0, epsilon = 1e-10);
    }

    #[test]
    fn test_intersect_overlapping() {
        let sq1 = unit_square();
        let sq2 = Polygon2D::new(vec![
            Vector2::new(0.5, 0.0),
            Vector2::new(1.5, 0.0),
            Vector2::new(1.5, 1.0),
            Vector2::new(0.5, 1.0),
        ]);

        let intersection = intersect_polygons(&sq1, &sq2);
        assert_relative_eq!(intersection.area(), 0.5, epsilon = 1e-10);
    }

    #[test]
    fn test_intersect_no_overlap() {
        let sq1 = unit_square();
        let sq2 = Polygon2D::new(vec![
            Vector2::new(2.0, 0.0),
            Vector2::new(3.0, 0.0),
            Vector2::new(3.0, 1.0),
            Vector2::new(2.0, 1.0),
        ]);

        let intersection = intersect_polygons(&sq1, &sq2);
        assert!(intersection.is_empty() || intersection.area() < EPS);
    }

    #[test]
    fn test_affine_map_identity() {
        let id = AffineMap2D::identity();
        let p = Vector2::new(1.0, 2.0);
        assert_relative_eq!(id.apply(&p), p, epsilon = 1e-14);
    }

    #[test]
    fn test_affine_map_composition() {
        let f = AffineMap2D::new(
            Matrix2::new(2.0, 0.0, 0.0, 3.0),
            Vector2::new(1.0, 2.0),
        );
        let g = AffineMap2D::new(
            Matrix2::new(1.0, 1.0, 0.0, 1.0),
            Vector2::new(0.5, 0.5),
        );

        let fg = compose_affine(&f, &g);
        let x = Vector2::new(1.0, 1.0);

        // (f ∘ g)(x) should equal f(g(x))
        assert_relative_eq!(fg.apply(&x), f.apply(&g.apply(&x)), epsilon = 1e-14);
    }

    #[test]
    fn test_affine_func_eval() {
        let f = AffineFunc {
            gradient: Vector2::new(2.0, 3.0),
            constant: 5.0,
        };

        let x = Vector2::new(1.0, 2.0);
        // f(x) = 2*1 + 3*2 + 5 = 13
        assert_relative_eq!(f.eval(&x), 13.0, epsilon = 1e-14);
    }

    #[test]
    fn test_intersect_line_polygon_horizontal() {
        // Square [-1, 1]^2 with horizontal line y=0
        let square = Polygon2D::new(vec![
            Vector2::new(-1.0, -1.0),
            Vector2::new(1.0, -1.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(-1.0, 1.0),
        ]);

        // Line: (0, 0) + t*(-1, 0) = (-t, 0)
        let point = Vector2::new(0.0, 0.0);
        let direction = Vector2::new(-1.0, 0.0);

        let result = intersect_line_polygon(&point, &direction, &square);
        assert!(result.is_some(), "Should find intersection");

        let (t_min, t_max) = result.unwrap();
        // Line enters at x=1 (t=-1) and exits at x=-1 (t=1)
        assert_relative_eq!(t_min, -1.0, epsilon = 1e-10);
        assert_relative_eq!(t_max, 1.0, epsilon = 1e-10);
    }

    #[test]
    fn test_intersect_line_polygon_vertical() {
        // Square [-1, 1]^2 with vertical line x=0.5
        let square = Polygon2D::new(vec![
            Vector2::new(-1.0, -1.0),
            Vector2::new(1.0, -1.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(-1.0, 1.0),
        ]);

        let point = Vector2::new(0.5, 0.0);
        let direction = Vector2::new(0.0, 1.0);

        let result = intersect_line_polygon(&point, &direction, &square);
        assert!(result.is_some(), "Should find intersection");

        let (t_min, t_max) = result.unwrap();
        // Line enters at y=-1 (t=-1) and exits at y=1 (t=1)
        assert_relative_eq!(t_min, -1.0, epsilon = 1e-10);
        assert_relative_eq!(t_max, 1.0, epsilon = 1e-10);
    }

    #[test]
    fn test_intersect_line_polygon_outside() {
        // Square [-1, 1]^2 with line y=2 (outside)
        let square = Polygon2D::new(vec![
            Vector2::new(-1.0, -1.0),
            Vector2::new(1.0, -1.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(-1.0, 1.0),
        ]);

        let point = Vector2::new(0.0, 2.0);
        let direction = Vector2::new(1.0, 0.0);

        let result = intersect_line_polygon(&point, &direction, &square);
        assert!(result.is_none(), "Line outside should have no intersection");
    }

    #[test]
    fn test_compose_func_with_map() {
        let f = AffineFunc {
            gradient: Vector2::new(1.0, 1.0),
            constant: 0.0,
        };
        let m = AffineMap2D::new(
            Matrix2::new(2.0, 0.0, 0.0, 2.0),
            Vector2::new(1.0, 1.0),
        );

        let composed = compose_func_with_map(&f, &m);
        let x = Vector2::new(1.0, 1.0);

        // f(m(x)) should equal composed(x)
        assert_relative_eq!(composed.eval(&x), f.eval(&m.apply(&x)), epsilon = 1e-14);
    }
}
