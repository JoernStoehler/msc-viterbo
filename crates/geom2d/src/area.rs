//! Polygon area computation.
//!
//! # Mathematical Background
//!
//! The area of a simple polygon with vertices (x₀, y₀), ..., (x_{n-1}, y_{n-1}) is
//! given by the **shoelace formula**:
//!
//! ```text
//! Area = ½ |Σ_{i=0}^{n-1} (xᵢ yᵢ₊₁ - xᵢ₊₁ yᵢ)|
//! ```
//!
//! For a CCW-oriented polygon, the sum is positive, so we omit the absolute value.
//!
//! # Proof of Correctness
//!
//! The shoelace formula can be derived by summing signed triangle areas:
//!
//! 1. Each edge (vᵢ, vᵢ₊₁) defines a triangle with the origin.
//! 2. The signed area of triangle (O, vᵢ, vᵢ₊₁) is ½(vᵢ × vᵢ₊₁).
//! 3. For a simple polygon, contributions outside the polygon cancel.
//!
//! **Reference:** de Berg et al., "Computational Geometry: Algorithms and Applications",
//! Section 1.1 (polygon area via signed triangles).
//!
//! # Invariant Dependency
//!
//! This function assumes the input is a valid [`Polygon`] (CCW, convex).
//! For invalid input, the result is meaningless.

use crate::polygon::Polygon;
use nalgebra::Vector2;

/// Compute the area of a polygon.
///
/// # Mathematical Definition
///
/// For a polygon P with CCW vertices v₀, v₁, ..., v_{n-1}:
///
/// ```text
/// area(P) = ½ Σ_{i=0}^{n-1} (vᵢ × vᵢ₊₁)
/// ```
///
/// where × denotes the 2D cross product (determinant).
///
/// # Proof of Correctness
///
/// **Claim:** For a valid (CCW, convex) polygon, `area()` returns the Euclidean area.
///
/// **Proof:**
/// 1. By [`Polygon`] invariants, vertices are in CCW order, so signed area > 0.
/// 2. The shoelace formula computes signed area correctly for simple polygons.
/// 3. Convex polygons are simple (non-self-intersecting).
/// 4. Therefore, the formula returns the unsigned Euclidean area. □
///
/// # Complexity
///
/// O(n) where n = number of vertices.
///
/// # Example
///
/// ```
/// use nalgebra::Vector2;
/// use geom2d::{Polygon, area};
///
/// let square = Polygon::new(vec![
///     Vector2::new(0.0, 0.0),
///     Vector2::new(2.0, 0.0),
///     Vector2::new(2.0, 2.0),
///     Vector2::new(0.0, 2.0),
/// ]).unwrap();
///
/// assert!((area(&square) - 4.0).abs() < 1e-10);
/// ```
#[must_use]
pub fn area(polygon: &Polygon) -> f64 {
    let vertices = polygon.vertices();
    let n = vertices.len();

    // Shoelace formula: sum of cross products
    let mut sum = 0.0;
    for i in 0..n {
        sum += cross_2d(&vertices[i], &vertices[(i + 1) % n]);
    }

    // Divide by 2 to get area (sum is 2× signed area)
    // Result is positive for CCW polygons (guaranteed by Polygon invariant)
    debug_assert!(sum > 0.0, "CCW polygon should have positive signed area");
    sum / 2.0
}

/// 2D cross product: a × b = a.x * b.y - a.y * b.x
#[inline]
fn cross_2d(a: &Vector2<f64>, b: &Vector2<f64>) -> f64 {
    a.x * b.y - a.y * b.x
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;
    use std::f64::consts::PI;

    /// Helper: create a unit square [0,1]²
    fn unit_square() -> Polygon {
        Polygon::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ])
        .unwrap()
    }

    /// Helper: create a rectangle with given width and height
    fn rectangle(width: f64, height: f64) -> Polygon {
        Polygon::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(width, 0.0),
            Vector2::new(width, height),
            Vector2::new(0.0, height),
        ])
        .unwrap()
    }

    /// Helper: create a regular n-gon with circumradius r
    fn regular_ngon(n: usize, circumradius: f64) -> Polygon {
        let vertices: Vec<_> = (0..n)
            .map(|i| {
                let angle = 2.0 * PI * (i as f64) / (n as f64);
                Vector2::new(circumradius * angle.cos(), circumradius * angle.sin())
            })
            .collect();
        Polygon::new(vertices).unwrap()
    }

    // ==================== POSITIVE TESTS ====================
    // Verify correct area for known polygons.

    #[test]
    fn test_area_unit_square() {
        let square = unit_square();
        assert_relative_eq!(area(&square), 1.0, epsilon = 1e-10);
    }

    #[test]
    fn test_area_rectangle_2x3() {
        let rect = rectangle(2.0, 3.0);
        assert_relative_eq!(area(&rect), 6.0, epsilon = 1e-10);
    }

    #[test]
    fn test_area_equilateral_triangle() {
        // Equilateral triangle with circumradius r has area (3√3/4) * (r√3)² = (3√3/4) * 3r²
        // Wait, let me recalculate. Side length s = r * √3, area = (√3/4) * s² = (√3/4) * 3r² = (3√3/4) r²
        // For r = 1: area = 3√3/4 ≈ 1.299
        let triangle = regular_ngon(3, 1.0);
        let expected = 3.0 * 3.0_f64.sqrt() / 4.0;
        assert_relative_eq!(area(&triangle), expected, epsilon = 1e-10);
    }

    #[test]
    fn test_area_regular_hexagon() {
        // Regular hexagon with circumradius r has area (3√3/2) r²
        let hexagon = regular_ngon(6, 1.0);
        let expected = 3.0 * 3.0_f64.sqrt() / 2.0;
        assert_relative_eq!(area(&hexagon), expected, epsilon = 1e-10);
    }

    #[test]
    fn test_area_approaches_circle_for_large_n() {
        // As n → ∞, regular n-gon area → π r²
        let r = 2.0;
        let ngon = regular_ngon(1000, r);
        let circle_area = PI * r * r;
        assert_relative_eq!(area(&ngon), circle_area, epsilon = 1e-4);
    }

    // ==================== PROPERTY TESTS ====================
    // Verify mathematical properties of area.

    #[test]
    fn test_area_scales_quadratically() {
        // area(λP) = λ² · area(P)
        let square = unit_square();
        let base_area = area(&square);

        for scale in [0.5, 2.0, 3.0, 10.0] {
            let scaled =
                Polygon::new(square.vertices().iter().map(|v| v * scale).collect()).unwrap();
            let scaled_area = area(&scaled);
            assert_relative_eq!(scaled_area, base_area * scale * scale, epsilon = 1e-10);
        }
    }

    #[test]
    fn test_area_translation_invariant() {
        // area(P + v) = area(P) for any translation v
        let square = unit_square();
        let base_area = area(&square);

        let offsets = [
            Vector2::new(10.0, 0.0),
            Vector2::new(0.0, -5.0),
            Vector2::new(100.0, 200.0),
        ];

        for offset in offsets {
            let translated =
                Polygon::new(square.vertices().iter().map(|v| v + offset).collect()).unwrap();
            assert_relative_eq!(area(&translated), base_area, epsilon = 1e-10);
        }
    }

    #[test]
    fn test_area_rotation_invariant() {
        // area(R·P) = area(P) for any rotation R
        let square = unit_square();
        let base_area = area(&square);

        // Center the square first so rotation is around centroid
        let center = Vector2::new(0.5, 0.5);
        let centered: Vec<_> = square.vertices().iter().map(|v| v - center).collect();

        for angle_deg in [30.0, 45.0, 90.0, 137.0] {
            let angle = angle_deg * PI / 180.0;
            let cos_a = angle.cos();
            let sin_a = angle.sin();

            let rotated: Vec<_> = centered
                .iter()
                .map(|v| Vector2::new(cos_a * v.x - sin_a * v.y, sin_a * v.x + cos_a * v.y))
                .collect();

            let rotated_polygon = Polygon::new(rotated).unwrap();
            assert_relative_eq!(area(&rotated_polygon), base_area, epsilon = 1e-10);
        }
    }

    #[test]
    fn test_area_positive_for_valid_polygon() {
        // Area should always be positive for valid (CCW) polygons
        for n in 3..=10 {
            let ngon = regular_ngon(n, 1.0);
            assert!(area(&ngon) > 0.0, "area should be positive for {}-gon", n);
        }
    }

    // ==================== BOUNDARY/EDGE CASES ====================

    #[test]
    fn test_area_minimum_polygon_triangle() {
        // Smallest valid polygon is a triangle
        let triangle = Polygon::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(0.0, 1.0),
        ])
        .unwrap();
        assert_relative_eq!(area(&triangle), 0.5, epsilon = 1e-10);
    }

    #[test]
    fn test_area_very_small_polygon() {
        // Tiny polygon should still compute correctly
        let tiny = Polygon::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1e-6, 0.0),
            Vector2::new(1e-6, 1e-6),
            Vector2::new(0.0, 1e-6),
        ])
        .unwrap();
        assert_relative_eq!(area(&tiny), 1e-12, epsilon = 1e-15);
    }

    #[test]
    fn test_area_very_large_polygon() {
        // Large polygon should not overflow
        let big = Polygon::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1e6, 0.0),
            Vector2::new(1e6, 1e6),
            Vector2::new(0.0, 1e6),
        ])
        .unwrap();
        assert_relative_eq!(area(&big), 1e12, epsilon = 1e6);
    }
}
