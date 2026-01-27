//! Geometric utilities for 2D convex polygons.
//!
//! This module provides:
//! - `sort_ccw`: Sort polygon vertices in counter-clockwise order
//! - `intersect_polygons`: Sutherland-Hodgman polygon clipping
//! - `point_in_polygon`: Point-in-convex-polygon test
//! - `apply_affine_to_polygon`: Apply affine map to all vertices

use nalgebra::Vector2;

use crate::constants::EPS;
use crate::types::{AffineMap2D, Polygon2D};

/// Sort 2D points in counter-clockwise order around their centroid.
///
/// Precondition: points form a convex polygon.
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

/// Check if point p is on the left side (or on) the directed edge from e1 to e2.
#[inline]
fn is_left_of_edge(p: &Vector2<f64>, e1: &Vector2<f64>, e2: &Vector2<f64>) -> bool {
    // Cross product of (e2-e1) and (p-e1)
    let cross = (e2[0] - e1[0]) * (p[1] - e1[1]) - (e2[1] - e1[1]) * (p[0] - e1[0]);
    cross >= -EPS // Include points on the edge
}

/// Compute intersection of two line segments.
/// Segment 1: a1 -> a2
/// Segment 2: b1 -> b2
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

/// Clip polygon by half-plane defined by directed edge (p1 -> p2).
/// Keep points on the left side of the directed edge.
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

/// Compute intersection of two convex polygons using Sutherland-Hodgman algorithm.
///
/// Returns empty polygon if intersection is empty.
pub fn intersect_polygons(p1: &Polygon2D, p2: &Polygon2D) -> Polygon2D {
    if p1.is_empty() || p2.is_empty() {
        return Polygon2D::empty();
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

/// Test if point is inside a convex polygon (CCW vertices).
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

/// Apply affine transformation to all vertices of a polygon.
pub fn apply_affine_to_polygon(map: &AffineMap2D, polygon: &Polygon2D) -> Polygon2D {
    Polygon2D::new(polygon.vertices.iter().map(|v| map.apply(v)).collect())
}

/// Deduplicate nearby vertices in a polygon.
pub fn deduplicate_vertices(mut vertices: Vec<Vector2<f64>>, eps: f64) -> Vec<Vector2<f64>> {
    if vertices.len() < 2 {
        return vertices;
    }

    let mut i = 0;
    while i < vertices.len() {
        let j = (i + 1) % vertices.len();
        if j == 0 && vertices.len() <= 2 {
            break; // Don't reduce below 2 vertices
        }
        if (vertices[i] - vertices[j]).norm() < eps {
            vertices.remove(j);
            if j < i {
                i -= 1;
            }
        } else {
            i += 1;
        }
        if i >= vertices.len() {
            break;
        }
    }

    vertices
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sort_ccw_triangle() {
        // Triangle given in wrong order
        let points = vec![
            Vector2::new(0.0, 1.0),
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
        ];
        let sorted = sort_ccw(points);

        // Verify CCW order by checking positive signed area
        let area = 0.5
            * ((sorted[1][0] - sorted[0][0]) * (sorted[2][1] - sorted[0][1])
                - (sorted[2][0] - sorted[0][0]) * (sorted[1][1] - sorted[0][1]));
        assert!(area > 0.0, "Sorted polygon should have positive area (CCW)");
    }

    #[test]
    fn test_point_in_polygon_inside() {
        let polygon = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);

        // Center point
        assert!(point_in_polygon(&Vector2::new(0.5, 0.5), &polygon));
    }

    #[test]
    fn test_point_in_polygon_outside() {
        let polygon = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);

        // Outside points
        assert!(!point_in_polygon(&Vector2::new(2.0, 0.5), &polygon));
        assert!(!point_in_polygon(&Vector2::new(-1.0, 0.5), &polygon));
    }

    #[test]
    fn test_intersect_polygons_overlap() {
        // Two overlapping squares
        let p1 = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(2.0, 0.0),
            Vector2::new(2.0, 2.0),
            Vector2::new(0.0, 2.0),
        ]);
        let p2 = Polygon2D::new(vec![
            Vector2::new(1.0, 1.0),
            Vector2::new(3.0, 1.0),
            Vector2::new(3.0, 3.0),
            Vector2::new(1.0, 3.0),
        ]);

        let intersection = intersect_polygons(&p1, &p2);

        // Intersection should be the unit square [1,2] x [1,2]
        assert!(!intersection.is_empty());
        let area = intersection.area();
        assert!((area - 1.0).abs() < 0.01, "Expected area 1.0, got {}", area);
    }

    #[test]
    fn test_intersect_polygons_no_overlap() {
        // Two disjoint squares
        let p1 = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);
        let p2 = Polygon2D::new(vec![
            Vector2::new(2.0, 2.0),
            Vector2::new(3.0, 2.0),
            Vector2::new(3.0, 3.0),
            Vector2::new(2.0, 3.0),
        ]);

        let intersection = intersect_polygons(&p1, &p2);
        assert!(intersection.is_empty());
    }

    #[test]
    fn test_intersect_polygons_contained() {
        // Small square inside large square
        let large = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(4.0, 0.0),
            Vector2::new(4.0, 4.0),
            Vector2::new(0.0, 4.0),
        ]);
        let small = Polygon2D::new(vec![
            Vector2::new(1.0, 1.0),
            Vector2::new(2.0, 1.0),
            Vector2::new(2.0, 2.0),
            Vector2::new(1.0, 2.0),
        ]);

        let intersection = intersect_polygons(&large, &small);

        // Intersection should equal the small square
        let area = intersection.area();
        assert!((area - 1.0).abs() < 0.01, "Expected area 1.0, got {}", area);
    }

    #[test]
    fn test_apply_affine_to_polygon() {
        let polygon = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(0.0, 1.0),
        ]);

        // Scale by 2
        let map = AffineMap2D {
            matrix: nalgebra::Matrix2::new(2.0, 0.0, 0.0, 2.0),
            offset: Vector2::zeros(),
        };

        let scaled = apply_affine_to_polygon(&map, &polygon);

        // Area should be 4x original (0.5 -> 2.0)
        assert!((scaled.area() - 2.0).abs() < EPS);
    }
}
