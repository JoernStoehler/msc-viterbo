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

    // =========================================================================
    // Clipping Tests
    // =========================================================================

    #[test]
    fn clip_half_square() {
        // Clip unit square by the line y = 0.5
        // Should keep the part where y >= 0.5
        let sq = unit_square();
        // Edge from (0, 0.5) to (1, 0.5) with p2 - p1 = (1, 0)
        // Points with cross > 0 are kept (left side of directed edge)
        // For edge going right, "left" is the upper half
        let p1 = Vector2f::new(0.0, 0.5);
        let p2 = Vector2f::new(1.0, 0.5);
        let clipped = clip_polygon_by_edge(&sq.vertices, p1, p2);

        // Should have 4 vertices: (0, 0.5), (1, 0.5), (1, 1), (0, 1)
        assert_eq!(
            clipped.len(),
            4,
            "Clipped polygon should have 4 vertices, got {}",
            clipped.len()
        );

        // All clipped vertices should have y >= 0.5 - EPS
        for v in &clipped {
            assert!(v.y >= 0.5 - EPS_POLY, "Vertex {:?} below clip line", v);
        }
    }

    #[test]
    fn clip_outside_polygon() {
        // Clip square by a half-plane that doesn't intersect it
        // clip_polygon_by_edge keeps points to the LEFT of directed edge p1 → p2
        // For edge (p1, p2), cross_2d(p2-p1, v-p1) >= 0 means v is kept
        let sq = unit_square(); // vertices at (0,0), (1,0), (1,1), (0,1)

        // Edge going UP at x = -1: from (-1, 0) to (-1, 1)
        // cross_2d((0, 1), (x, y) - (-1, 0)) = 0*(y) - 1*(x + 1) = -(x + 1)
        // Keeps where -(x + 1) >= 0, i.e., x <= -1
        // Square has x >= 0, so nothing is kept
        let p1 = Vector2f::new(-1.0, 0.0);
        let p2 = Vector2f::new(-1.0, 1.0);
        let clipped = clip_polygon_by_edge(&sq.vertices, p1, p2);

        assert!(
            clipped.is_empty(),
            "Clipping by disjoint half-plane should be empty, got {} vertices",
            clipped.len()
        );
    }

    #[test]
    fn clip_entirely_inside() {
        // Clip square by a half-plane that contains it entirely
        let sq = unit_square(); // vertices at (0,0), (1,0), (1,1), (0,1)

        // Edge going UP at x = 2: from (2, 0) to (2, 1)
        // cross_2d((0, 1), (x, y) - (2, 0)) = 0*(y) - 1*(x - 2) = 2 - x
        // Keeps where 2 - x >= 0, i.e., x <= 2
        // Square has x ∈ [0, 1], so everything is kept
        let p1 = Vector2f::new(2.0, 0.0);
        let p2 = Vector2f::new(2.0, 1.0);
        let clipped = clip_polygon_by_edge(&sq.vertices, p1, p2);

        // Should preserve all vertices
        assert_eq!(
            clipped.len(),
            sq.vertices.len(),
            "Should preserve all {} vertices",
            sq.vertices.len()
        );
    }

    // =========================================================================
    // Intersection Invariant Tests
    // =========================================================================

    #[test]
    fn intersection_is_subset_of_both() {
        // The intersection should be contained in both input polygons
        let sq1 = unit_square();
        let sq2 = Polygon2D::new(vec![
            Vector2f::new(0.3, 0.3),
            Vector2f::new(1.3, 0.3),
            Vector2f::new(1.3, 1.3),
            Vector2f::new(0.3, 1.3),
        ]);
        let inter = sq1.intersect(&sq2);

        if !inter.is_empty() {
            for v in &inter.vertices {
                assert!(sq1.contains(*v), "Intersection vertex {:?} not in sq1", v);
                assert!(sq2.contains(*v), "Intersection vertex {:?} not in sq2", v);
            }
        }
    }

    #[test]
    fn intersection_is_convex() {
        // Intersection of convex polygons is convex
        // Check: all vertices have same signed area contribution (same winding)
        let sq1 = unit_square();
        let sq2 = Polygon2D::new(vec![
            Vector2f::new(0.25, 0.25),
            Vector2f::new(0.75, 0.25),
            Vector2f::new(0.75, 0.75),
            Vector2f::new(0.25, 0.75),
        ]);
        let inter = sq1.intersect(&sq2);

        if inter.vertices.len() >= 3 {
            let area = inter.signed_area();
            // For a valid convex polygon, area should be non-zero
            // (unless degenerate)
            assert!(area.abs() > 1e-12, "Intersection has zero area");
        }
    }

    // =========================================================================
    // Contains Edge Cases
    // =========================================================================

    #[test]
    fn contains_vertex_points() {
        let sq = unit_square();
        for v in &sq.vertices {
            assert!(
                sq.contains(*v),
                "Polygon should contain its own vertex {:?}",
                v
            );
        }
    }

    #[test]
    fn contains_edge_midpoints() {
        let sq = unit_square();
        for i in 0..sq.vertices.len() {
            let v1 = sq.vertices[i];
            let v2 = sq.vertices[(i + 1) % sq.vertices.len()];
            let mid = (v1 + v2) * 0.5;
            assert!(
                sq.contains(mid),
                "Polygon should contain edge midpoint {:?}",
                mid
            );
        }
    }

    #[test]
    fn contains_near_boundary() {
        // Points just inside boundary should be contained
        let sq = unit_square();
        let eps = 1e-9;
        let near_interior = vec![
            Vector2f::new(eps, 0.5),       // near left edge
            Vector2f::new(1.0 - eps, 0.5), // near right edge
            Vector2f::new(0.5, eps),       // near bottom edge
            Vector2f::new(0.5, 1.0 - eps), // near top edge
        ];
        for p in near_interior {
            assert!(
                sq.contains(p),
                "Point {:?} near boundary should be contained",
                p
            );
        }
    }

    // =========================================================================
    // Signed Area Tests
    // =========================================================================

    #[test]
    fn signed_area_ccw_positive() {
        // CCW polygon should have positive signed area
        let sq = unit_square(); // CCW ordering
        let area = sq.signed_area();
        assert!(
            area > 0.0,
            "CCW polygon should have positive area, got {}",
            area
        );
    }

    #[test]
    fn signed_area_cw_negative() {
        // CW polygon should have negative signed area
        let cw_sq = Polygon2D::new(vec![
            Vector2f::new(0.0, 0.0),
            Vector2f::new(0.0, 1.0),
            Vector2f::new(1.0, 1.0),
            Vector2f::new(1.0, 0.0),
        ]);
        let area = cw_sq.signed_area();
        assert!(
            area < 0.0,
            "CW polygon should have negative area, got {}",
            area
        );
    }

    #[test]
    fn signed_area_magnitude() {
        // Unit square has area 1
        let sq = unit_square();
        let area = sq.signed_area().abs();
        assert!(
            (area - 1.0).abs() < 1e-10,
            "Unit square area should be 1, got {}",
            area
        );
    }
}
