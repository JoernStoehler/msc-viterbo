//! Convex 2D polygon operations for feasible region tracking.
//!
//! Each tube carries a feasible region: the set of starting points that could
//! lead to valid Reeb orbits. This module provides operations for tracking
//! these regions through intersection and affine transformation.
//!
//! The Sutherland-Hodgman algorithm is used for polygon intersection.

use crate::affine::{AffineFunc, AffineMap2D};
use rust_viterbo_geom::Vector2f;

/// Tolerance for polygon containment and intersection checks.
/// Set to 1e-8 to handle numerical precision issues in chained affine transformations.
const EPS_POLY: f64 = 1e-8;

/// A convex 2D polygon, represented as vertices in counterclockwise order.
///
/// Empty polygon (< 3 vertices) represents an infeasible region.
#[derive(Clone, Debug)]
pub struct Polygon2D {
    pub vertices: Vec<Vector2f>,
}

impl Polygon2D {
    pub fn new(vertices: Vec<Vector2f>) -> Self {
        Self { vertices }
    }

    pub fn empty() -> Self {
        Self { vertices: vec![] }
    }

    pub fn is_empty(&self) -> bool {
        self.vertices.len() < 3
    }

    /// Apply an affine map to all vertices.
    pub fn affine_image(&self, map: &AffineMap2D) -> Polygon2D {
        Polygon2D {
            vertices: self.vertices.iter().map(|v| map.apply(*v)).collect(),
        }
    }

    /// Compute intersection using Sutherland-Hodgman algorithm.
    pub fn intersect(&self, other: &Polygon2D) -> Polygon2D {
        if self.is_empty() || other.is_empty() {
            return Polygon2D::empty();
        }

        let mut output = self.vertices.clone();

        for i in 0..other.vertices.len() {
            if output.is_empty() {
                return Polygon2D::empty();
            }

            let p1 = other.vertices[i];
            let p2 = other.vertices[(i + 1) % other.vertices.len()];
            output = clip_polygon_by_edge(&output, p1, p2);
        }

        if output.len() < 3 {
            Polygon2D::empty()
        } else {
            Polygon2D::new(output)
        }
    }

    /// Find minimum value of an affine function over this polygon.
    /// Returns (min_value, minimizer).
    pub fn minimize(&self, func: &AffineFunc) -> Option<(f64, Vector2f)> {
        if self.is_empty() {
            return None;
        }

        let mut min_val = f64::INFINITY;
        let mut min_pt = self.vertices[0];

        for &v in &self.vertices {
            let val = func.eval(v);
            if val < min_val {
                min_val = val;
                min_pt = v;
            }
        }

        Some((min_val, min_pt))
    }

    /// Check if point is inside the polygon (including boundary).
    ///
    /// Uses the signed area test: for a CCW polygon, interior points have
    /// positive cross products with all edges. For CW polygons, interior
    /// points have negative cross products.
    pub fn contains(&self, p: Vector2f) -> bool {
        if self.is_empty() {
            return false;
        }

        // Determine polygon orientation from signed area
        let signed_area = self.signed_area();
        let is_ccw = signed_area > 0.0;

        for i in 0..self.vertices.len() {
            let v1 = self.vertices[i];
            let v2 = self.vertices[(i + 1) % self.vertices.len()];
            let cross = cross_2d(v2 - v1, p - v1);

            // For CCW polygon, interior points have cross >= 0
            // For CW polygon, interior points have cross <= 0
            if is_ccw {
                if cross < -EPS_POLY {
                    return false;
                }
            } else if cross > EPS_POLY {
                return false;
            }
        }
        true
    }

    /// Compute signed area of the polygon.
    /// Positive for CCW, negative for CW.
    fn signed_area(&self) -> f64 {
        if self.vertices.len() < 3 {
            return 0.0;
        }
        let mut area = 0.0;
        for i in 0..self.vertices.len() {
            let v1 = self.vertices[i];
            let v2 = self.vertices[(i + 1) % self.vertices.len()];
            area += cross_2d(v1, v2);
        }
        area / 2.0
    }
}

/// 2D cross product (returns scalar): a × b = a.x * b.y - a.y * b.x
fn cross_2d(a: Vector2f, b: Vector2f) -> f64 {
    a.x * b.y - a.y * b.x
}

/// Clip polygon by half-plane defined by edge p1 -> p2.
/// Keeps the part to the left of the directed edge.
fn clip_polygon_by_edge(polygon: &[Vector2f], p1: Vector2f, p2: Vector2f) -> Vec<Vector2f> {
    let mut output = Vec::new();
    let edge = p2 - p1;

    for i in 0..polygon.len() {
        let current = polygon[i];
        let next = polygon[(i + 1) % polygon.len()];

        let current_side = cross_2d(edge, current - p1);
        let next_side = cross_2d(edge, next - p1);

        if current_side >= -EPS_POLY {
            output.push(current);
        }

        if (current_side < -EPS_POLY && next_side > EPS_POLY)
            || (current_side > EPS_POLY && next_side < -EPS_POLY)
        {
            if let Some(intersection) = line_segment_intersection(current, next, p1, p2) {
                output.push(intersection);
            }
        }
    }

    output
}

/// Find intersection of line segment (a1, a2) with line through (b1, b2).
fn line_segment_intersection(
    a1: Vector2f,
    a2: Vector2f,
    b1: Vector2f,
    b2: Vector2f,
) -> Option<Vector2f> {
    let d1 = a2 - a1;
    let d2 = b2 - b1;

    let cross = cross_2d(d1, d2);
    if cross.abs() < EPS_POLY {
        return None;
    }

    let t = cross_2d(b1 - a1, d2) / cross;
    Some(a1 + d1 * t)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn unit_square() -> Polygon2D {
        Polygon2D::new(vec![
            Vector2f::new(0.0, 0.0),
            Vector2f::new(1.0, 0.0),
            Vector2f::new(1.0, 1.0),
            Vector2f::new(0.0, 1.0),
        ])
    }

    #[test]
    fn empty_is_empty() {
        assert!(Polygon2D::empty().is_empty());
    }

    #[test]
    fn unit_square_not_empty() {
        assert!(!unit_square().is_empty());
    }

    #[test]
    fn contains_interior_point() {
        let sq = unit_square();
        assert!(sq.contains(Vector2f::new(0.5, 0.5)));
    }

    #[test]
    fn contains_boundary_point() {
        let sq = unit_square();
        assert!(sq.contains(Vector2f::new(0.0, 0.5)));
    }

    #[test]
    fn not_contains_exterior_point() {
        let sq = unit_square();
        assert!(!sq.contains(Vector2f::new(2.0, 0.5)));
    }

    #[test]
    fn intersect_self() {
        let sq = unit_square();
        let result = sq.intersect(&sq);
        assert!(!result.is_empty());
    }

    #[test]
    fn intersect_overlapping() {
        let sq1 = unit_square();
        let sq2 = Polygon2D::new(vec![
            Vector2f::new(0.5, 0.5),
            Vector2f::new(1.5, 0.5),
            Vector2f::new(1.5, 1.5),
            Vector2f::new(0.5, 1.5),
        ]);
        let result = sq1.intersect(&sq2);
        assert!(!result.is_empty());
    }

    #[test]
    fn intersect_disjoint() {
        let sq1 = unit_square();
        let sq2 = Polygon2D::new(vec![
            Vector2f::new(2.0, 0.0),
            Vector2f::new(3.0, 0.0),
            Vector2f::new(3.0, 1.0),
            Vector2f::new(2.0, 1.0),
        ]);
        let result = sq1.intersect(&sq2);
        assert!(result.is_empty());
    }

    #[test]
    fn affine_image_identity() {
        let sq = unit_square();
        let id = AffineMap2D::identity();
        let result = sq.affine_image(&id);
        assert_eq!(result.vertices.len(), sq.vertices.len());
    }

    #[test]
    fn affine_image_translation() {
        let sq = unit_square();
        use rust_viterbo_geom::Matrix2f;
        let translate = AffineMap2D::new(Matrix2f::identity(), Vector2f::new(1.0, 1.0));
        let result = sq.affine_image(&translate);
        assert!((result.vertices[0] - Vector2f::new(1.0, 1.0)).norm() < 1e-12);
    }

    #[test]
    fn minimize_constant() {
        let sq = unit_square();
        let f = AffineFunc::new(Vector2f::new(0.0, 0.0), 5.0);
        let (val, _) = sq.minimize(&f).unwrap();
        assert!((val - 5.0).abs() < 1e-12);
    }

    #[test]
    fn minimize_linear() {
        let sq = unit_square();
        let f = AffineFunc::new(Vector2f::new(1.0, 1.0), 0.0);
        let (val, pt) = sq.minimize(&f).unwrap();
        assert!((val - 0.0).abs() < 1e-12);
        assert!((pt - Vector2f::new(0.0, 0.0)).norm() < 1e-12);
    }
}
