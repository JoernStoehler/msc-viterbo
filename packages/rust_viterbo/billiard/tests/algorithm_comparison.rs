//! Algorithm comparison tests: billiard vs HK2017
//!
//! Compare the billiard and HK2017 algorithms on Lagrangian products.
//! Document where they agree and where they disagree.
//!
//! NO bug fixes, NO assumptions about which is correct.
//! Just observe and document what we see.

use approx::assert_relative_eq;
use billiard::{billiard_capacity_from_polygons, LagrangianProduct, Polygon2D};
use hk2017::{hk2017_capacity, Hk2017Config};
use nalgebra::Vector2;
use std::f64::consts::PI;

/// Helper: Run both algorithms and print comparison
fn compare_algorithms(
    name: &str,
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    expect_agreement: bool,
) -> (f64, f64, f64) {
    let c_billiard = billiard_capacity_from_polygons(k_q, k_p)
        .expect("billiard should succeed")
        .capacity;

    let product = LagrangianProduct::new(k_q.clone(), k_p.clone())
        .expect("valid product");
    let (normals, heights) = product.to_hrep();
    let polytope = hk2017::PolytopeHRep::new(normals, heights);
    let c_hk2017 = hk2017_capacity(&polytope, &Hk2017Config::default())
        .expect("hk2017 should succeed")
        .capacity;

    let ratio = c_billiard / c_hk2017;

    println!(
        "{}: billiard={:.4}, hk2017={:.4}, ratio={:.4}",
        name, c_billiard, c_hk2017, ratio
    );

    if expect_agreement {
        assert_relative_eq!(ratio, 1.0, epsilon = 1e-3, max_relative = 1e-3);
    }

    (c_billiard, c_hk2017, ratio)
}

// ==============================================================================
// CASES EXPECTED TO AGREE (from TODO.md)
// ==============================================================================

/// Test 1: Square × Square (tesseract)
/// Known ground truth: c = 4.0
#[test]
fn test_square_square() {
    let square = Polygon2D::square(2.0).unwrap();
    let (c_b, c_h, _) = compare_algorithms(
        "square×square",
        &square,
        &square,
        true, // expect agreement
    );

    // Both should equal 4.0
    assert_relative_eq!(c_b, 4.0, epsilon = 1e-3);
    assert_relative_eq!(c_h, 4.0, epsilon = 1e-3);
}

/// Test 2: Rectangle × Square
#[test]
fn test_rectangle_square() {
    let rectangle = Polygon2D::from_vertices(vec![
        Vector2::new(-1.0, -2.0),
        Vector2::new(1.0, -2.0),
        Vector2::new(1.0, 2.0),
        Vector2::new(-1.0, 2.0),
    ])
    .unwrap();
    let square = Polygon2D::square(2.0).unwrap();

    compare_algorithms(
        "rectangle×square",
        &rectangle,
        &square,
        true, // expect agreement
    );
}

/// Test 3: Square × Triangle
/// TODO.md line 31 says this agrees
#[test]
fn test_square_triangle() {
    let square = Polygon2D::square(2.0).unwrap();
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();

    compare_algorithms(
        "square×triangle",
        &square,
        &triangle,
        true, // expect agreement
    );
}

/// Test 4: Square(r=0.5) × Square(r=2)
#[test]
fn test_square_scaled_square() {
    let square1 = Polygon2D::square(1.0).unwrap(); // r=0.5 means half-width 0.5
    let square2 = Polygon2D::square(4.0).unwrap(); // r=2 means half-width 2

    compare_algorithms(
        "square(r=0.5)×square(r=2)",
        &square1,
        &square2,
        true, // expect agreement
    );
}

/// Test 5: Square × Square (rotated 45°)
#[test]
fn test_square_square_rotated_45() {
    let square = Polygon2D::square(2.0).unwrap();
    let rotated = square.rotate(PI / 4.0);

    compare_algorithms(
        "square×square(rot 45°)",
        &square,
        &rotated,
        true, // expect agreement
    );
}

/// Test 6: Rectangle(1×2) × Rectangle(1.5×1)
#[test]
fn test_rectangle_rectangle() {
    let rect1 = Polygon2D::from_vertices(vec![
        Vector2::new(-1.0, -2.0),
        Vector2::new(1.0, -2.0),
        Vector2::new(1.0, 2.0),
        Vector2::new(-1.0, 2.0),
    ])
    .unwrap();

    let rect2 = Polygon2D::from_vertices(vec![
        Vector2::new(-1.5, -1.0),
        Vector2::new(1.5, -1.0),
        Vector2::new(1.5, 1.0),
        Vector2::new(-1.5, 1.0),
    ])
    .unwrap();

    compare_algorithms(
        "rectangle(1×2)×rectangle(1.5×1)",
        &rect1,
        &rect2,
        true, // expect agreement
    );
}

/// Test 7: Pentagon × Pentagon
/// Known from HK-O 2024: c ≈ 3.441
#[test]
#[ignore] // Expensive test, run with --ignored
fn test_pentagon_pentagon() {
    let pentagon = Polygon2D::regular_pentagon();
    let (c_b, c_h, _) = compare_algorithms(
        "pentagon×pentagon",
        &pentagon,
        &pentagon,
        true, // expect agreement
    );

    // Both should be close to 3.441
    assert_relative_eq!(c_b, 3.441, epsilon = 0.01);
    assert_relative_eq!(c_h, 3.441, epsilon = 0.01);
}

// ==============================================================================
// TRIANGLE CASES - DOCUMENT DISAGREEMENT (from TODO.md lines 30-46)
// ==============================================================================

/// Test 8: Triangle × Triangle (same)
/// TODO.md line 30: billiard=3.0, hk2017=1.5, ratio=2.0
#[test]
fn test_triangle_triangle_same() {
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();

    let (c_b, c_h, ratio) = compare_algorithms(
        "triangle×triangle (same)",
        &triangle,
        &triangle,
        false, // document disagreement
    );

    // Document the observed pattern
    println!("  → Triangle×triangle disagreement observed");
    println!("  → Expected billiard≈3.0, hk2017≈1.5 from TODO.md");

    // Don't assert exact values, just document the pattern
    assert!(ratio > 1.5, "Expected ratio > 1.5, got {}", ratio);
}

/// Test 9: Triangle × Triangle (rotated 15°)
#[test]
fn test_triangle_triangle_rot15() {
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();
    let rotated = triangle.rotate(15.0 * PI / 180.0);

    compare_algorithms(
        "triangle×triangle (rot 15°)",
        &triangle,
        &rotated,
        false, // document disagreement
    );
}

/// Test 10: Triangle × Triangle (rotated 30°)
#[test]
fn test_triangle_triangle_rot30() {
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();
    let rotated = triangle.rotate(30.0 * PI / 180.0);

    compare_algorithms(
        "triangle×triangle (rot 30°)",
        &triangle,
        &rotated,
        false, // document disagreement
    );
}

/// Test 11: Triangle × Triangle (rotated 60°)
#[test]
fn test_triangle_triangle_rot60() {
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();
    let rotated = triangle.rotate(60.0 * PI / 180.0);

    compare_algorithms(
        "triangle×triangle (rot 60°)",
        &triangle,
        &rotated,
        false, // document disagreement
    );
}

/// Test 12: Triangle × Triangle (rotated 90°)
#[test]
fn test_triangle_triangle_rot90() {
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();
    let rotated = triangle.rotate(90.0 * PI / 180.0);

    compare_algorithms(
        "triangle×triangle (rot 90°)",
        &triangle,
        &rotated,
        false, // document disagreement
    );
}

/// Test 13: Triangle(r=1) × Triangle(r=2)
#[test]
fn test_triangle_scaled_triangle() {
    let triangle1 = Polygon2D::regular(3, 1.0, 0.0).unwrap();
    let triangle2 = Polygon2D::regular(3, 2.0, 0.0).unwrap();

    compare_algorithms(
        "triangle(r=1)×triangle(r=2)",
        &triangle1,
        &triangle2,
        false, // document disagreement
    );
}

/// Test 14: Triangle × Triangle (scaled + rotated)
#[test]
fn test_triangle_scaled_rotated_triangle() {
    let triangle1 = Polygon2D::regular(3, 1.0, 0.0).unwrap();
    let triangle2 = Polygon2D::regular(3, 1.5, 25.0 * PI / 180.0).unwrap();

    compare_algorithms(
        "triangle(r=1)×triangle(r=1.5, rot 25°)",
        &triangle1,
        &triangle2,
        false, // document disagreement
    );
}

/// Test 15: Asymmetric triangles
#[test]
fn test_asymmetric_triangles() {
    // Create two irregular triangles
    let tri_a = Polygon2D::from_vertices(vec![
        Vector2::new(1.0, 0.0),
        Vector2::new(-0.5, 0.866),
        Vector2::new(-0.5, -0.866),
    ])
    .unwrap();

    let tri_b = Polygon2D::from_vertices(vec![
        Vector2::new(0.8, 0.0),
        Vector2::new(-0.6, 0.7),
        Vector2::new(-0.4, -0.9),
    ])
    .unwrap();

    compare_algorithms(
        "asymmetric tri_a × tri_b",
        &tri_a,
        &tri_b,
        false, // document disagreement
    );
}

// ==============================================================================
// BOUNDARY EXPLORATION - WHERE DOES IT TRANSITION? (from TODO.md lines 98-103)
// ==============================================================================

/// Test 16: Almost-triangle (4-gon with vertex near edge midpoint) × Triangle
/// Question: Does it fail like triangle×triangle or pass like square×triangle?
#[test]
fn test_almost_triangle_triangle() {
    // Create a 4-gon that's almost a triangle
    // Regular triangle vertices: (1,0), (-0.5, 0.866), (-0.5, -0.866)
    // Add a 4th vertex near the midpoint of the base edge
    let almost_triangle = Polygon2D::from_vertices(vec![
        Vector2::new(1.0, 0.0),
        Vector2::new(-0.5, 0.866),
        Vector2::new(-0.5, -0.866),
        Vector2::new(-0.48, 0.0), // Near midpoint of (-0.5, 0.866) to (-0.5, -0.866)
    ])
    .unwrap();

    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();

    let (_c_b, _c_h, ratio) = compare_algorithms(
        "almost-triangle×triangle",
        &almost_triangle,
        &triangle,
        false, // don't assert - just observe
    );

    println!("  → Question: Does it behave like triangle×triangle (ratio≈2) or square×triangle (ratio≈1)?");
    println!("  → Observed ratio: {:.4}", ratio);
}

/// Test 17: Pentagon × Triangle
/// Where does N-gon × triangle transition from working to failing?
#[test]
fn test_pentagon_triangle() {
    let pentagon = Polygon2D::regular(5, 1.0, 0.0).unwrap();
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();

    let (_c_b, _c_h, ratio) = compare_algorithms(
        "pentagon×triangle",
        &pentagon,
        &triangle,
        false, // observe
    );

    println!("  → Pentagon has 5 vertices, triangle has 3");
    println!("  → Ratio: {:.4}", ratio);
}

/// Test 18: Hexagon × Hexagon
/// Does it work (like square×square) or fail (like triangle×triangle)?
#[test]
fn test_hexagon_hexagon() {
    let hexagon = Polygon2D::regular(6, 1.0, 0.0).unwrap();

    let (_c_b, _c_h, ratio) = compare_algorithms(
        "hexagon×hexagon",
        &hexagon,
        &hexagon,
        false, // observe
    );

    println!("  → N=6 regular polygon");
    println!("  → Ratio: {:.4}", ratio);
}

/// Test 19: Hexagon × Triangle
#[test]
fn test_hexagon_triangle() {
    let hexagon = Polygon2D::regular(6, 1.0, 0.0).unwrap();
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();

    let (_c_b, _c_h, ratio) = compare_algorithms(
        "hexagon×triangle",
        &hexagon,
        &triangle,
        false, // observe
    );

    println!("  → Hexagon (N=6) × triangle (N=3)");
    println!("  → Ratio: {:.4}", ratio);
}

/// Test 20: Heptagon × Heptagon (N=7)
#[test]
fn test_heptagon_heptagon() {
    let heptagon = Polygon2D::regular(7, 1.0, 0.0).unwrap();

    let (_c_b, _c_h, ratio) = compare_algorithms(
        "heptagon×heptagon",
        &heptagon,
        &heptagon,
        false, // observe
    );

    println!("  → N=7 regular polygon");
    println!("  → Ratio: {:.4}", ratio);
}

// ==============================================================================
// DEGENERATE / EDGE CASES (from TODO.md lines 98-103)
// ==============================================================================

/// Test 21: Very flat triangle × Triangle
/// Triangle with very small height (nearly a line segment)
#[test]
fn test_flat_triangle_triangle() {
    let flat_triangle = Polygon2D::from_vertices(vec![
        Vector2::new(2.0, 0.0),
        Vector2::new(-1.0, 0.01), // Very small height
        Vector2::new(-1.0, -0.01),
    ])
    .unwrap();

    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();

    let (_c_b, _c_h, ratio) = compare_algorithms(
        "flat_triangle×triangle",
        &flat_triangle,
        &triangle,
        false, // observe
    );

    println!("  → Flat triangle: height ≈ 0.02, base ≈ 3");
    println!("  → Ratio: {:.4}", ratio);
}

/// Test 22: Very obtuse triangle × Triangle
/// Triangle with one angle close to 180°
#[test]
fn test_obtuse_triangle_triangle() {
    let obtuse_triangle = Polygon2D::from_vertices(vec![
        Vector2::new(2.0, 0.0),
        Vector2::new(-1.0, 0.3),
        Vector2::new(-1.0, -0.3),
    ])
    .unwrap();

    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();

    let (_c_b, _c_h, ratio) = compare_algorithms(
        "obtuse_triangle×triangle",
        &obtuse_triangle,
        &triangle,
        false, // observe
    );

    println!("  → Obtuse triangle: one angle ≈ 170°");
    println!("  → Ratio: {:.4}", ratio);
}

/// Test 23: Needle rectangle × Square
/// Rectangle with very large aspect ratio
#[test]
fn test_needle_rectangle_square() {
    let needle = Polygon2D::from_vertices(vec![
        Vector2::new(-0.1, -1.0),
        Vector2::new(0.1, -1.0),
        Vector2::new(0.1, 1.0),
        Vector2::new(-0.1, 1.0),
    ])
    .unwrap();

    let square = Polygon2D::square(2.0).unwrap();

    compare_algorithms(
        "needle_rectangle(1×10)×square",
        &needle,
        &square,
        true, // should agree (both rectangular)
    );
}
