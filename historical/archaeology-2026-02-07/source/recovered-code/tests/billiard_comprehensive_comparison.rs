//! Comprehensive comparison of billiard vs HK2017 on all test cases.

use billiard::{billiard_capacity_from_polygons, Polygon2D};
use hk2017::{hk2017_capacity, Hk2017Config, PolytopeHRep};
use nalgebra::{Vector2, Vector4};
use std::f64::consts::PI;

fn compare_algorithms(name: &str, k_q: &Polygon2D, k_p: &Polygon2D) -> (f64, f64, f64) {
    let billiard_result = billiard_capacity_from_polygons(k_q, k_p).unwrap();

    // Convert to H-rep for HK2017
    let mut normals = Vec::new();
    let mut heights = Vec::new();

    for i in 0..k_q.num_edges() {
        let n = k_q.normals[i];
        normals.push(Vector4::new(n[0], n[1], 0.0, 0.0));
        heights.push(k_q.heights[i]);
    }

    for i in 0..k_p.num_edges() {
        let n = k_p.normals[i];
        normals.push(Vector4::new(0.0, 0.0, n[0], n[1]));
        heights.push(k_p.heights[i]);
    }

    let polytope = PolytopeHRep::new(normals, heights);
    let hk_result = hk2017_capacity(&polytope, &Hk2017Config::naive()).unwrap();

    let diff = billiard_result.capacity - hk_result.capacity;
    let ratio = billiard_result.capacity / hk_result.capacity;

    println!("{:45} billiard={:8.4}, hk2017={:8.4}, diff={:8.4}, ratio={:.4}",
             name, billiard_result.capacity, hk_result.capacity, diff, ratio);

    (billiard_result.capacity, hk_result.capacity, ratio)
}

#[test]
fn comprehensive_test_suite() {
    println!("\n=== COMPREHENSIVE BILLIARD vs HK2017 COMPARISON ===\n");

    let mut all_pass = true;
    let tolerance = 1e-4;

    // 1. Square × Square (tesseract)
    let square = Polygon2D::square(2.0).unwrap();
    let (b, h, r) = compare_algorithms("square×square (tesseract)", &square, &square);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 2. Rectangle × Square
    let rect = Polygon2D::from_vertices(vec![
        Vector2::new(-1.0, -2.0),
        Vector2::new(1.0, -2.0),
        Vector2::new(1.0, 2.0),
        Vector2::new(-1.0, 2.0),
    ]).unwrap();
    let (b, h, r) = compare_algorithms("rectangle×square", &rect, &square);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 3. Triangle × Triangle (same)
    let tri = Polygon2D::regular(3, 1.0, 0.0).unwrap();
    let (b, h, r) = compare_algorithms("triangle×triangle (same)", &tri, &tri);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 4. Square × Triangle
    let (b, h, r) = compare_algorithms("square×triangle", &square, &tri);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 5. Small Square × Large Square
    let small_sq = Polygon2D::square(1.0).unwrap();
    let large_sq = Polygon2D::square(4.0).unwrap();
    let (b, h, r) = compare_algorithms("square(r=0.5)×square(r=2)", &small_sq, &large_sq);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 6. Triangle × Rotated Triangle (15°)
    let tri_rot15 = tri.rotate(15.0 * PI / 180.0);
    let (b, h, r) = compare_algorithms("triangle×triangle (rot 15°)", &tri, &tri_rot15);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 7. Triangle × Rotated Triangle (30°)
    let tri_rot30 = tri.rotate(30.0 * PI / 180.0);
    let (b, h, r) = compare_algorithms("triangle×triangle (rot 30°)", &tri, &tri_rot30);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 8. Triangle × Rotated Triangle (60°)
    let tri_rot60 = tri.rotate(60.0 * PI / 180.0);
    let (b, h, r) = compare_algorithms("triangle×triangle (rot 60°)", &tri, &tri_rot60);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 9. Triangle × Rotated Triangle (90°)
    let tri_rot90 = tri.rotate(90.0 * PI / 180.0);
    let (b, h, r) = compare_algorithms("triangle×triangle (rot 90°)", &tri, &tri_rot90);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 10. Triangle × Scaled Triangle
    let tri_large = Polygon2D::regular(3, 2.0, 0.0).unwrap();
    let (b, h, r) = compare_algorithms("triangle(r=1)×triangle(r=2)", &tri, &tri_large);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 11. Triangle × Rotated+Scaled Triangle
    let tri_rot_scaled = Polygon2D::regular(3, 1.5, 25.0 * PI / 180.0).unwrap();
    let (b, h, r) = compare_algorithms("triangle(r=1)×triangle(r=1.5,rot 25°)", &tri, &tri_rot_scaled);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 12. Asymmetric Triangle A × Triangle B
    let tri_a = Polygon2D::from_vertices(vec![
        Vector2::new(1.0, 0.0),
        Vector2::new(-0.5, 0.866),
        Vector2::new(-0.5, -0.866),
    ]).unwrap();
    let tri_b = Polygon2D::from_vertices(vec![
        Vector2::new(1.5, 0.0),
        Vector2::new(-0.8, 0.6),
        Vector2::new(-0.8, -1.0),
    ]).unwrap();
    let (b, h, r) = compare_algorithms("asymmetric tri_a × tri_b", &tri_a, &tri_b);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 13. Square × Rotated Square (45°)
    let sq_rot45 = square.rotate(45.0 * PI / 180.0);
    let (b, h, r) = compare_algorithms("square×square (rot 45°)", &square, &sq_rot45);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 14. Rectangle × Rectangle (different)
    let rect2 = Polygon2D::from_vertices(vec![
        Vector2::new(-1.5, -1.0),
        Vector2::new(1.5, -1.0),
        Vector2::new(1.5, 1.0),
        Vector2::new(-1.5, 1.0),
    ]).unwrap();
    let (b, h, r) = compare_algorithms("rectangle(1×2) × rectangle(1.5×1)", &rect, &rect2);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    // 15. Almost-Triangle (4-gon with one vertex near edge midpoint) × Triangle
    // Create a triangle-like quad: start with triangle vertices, add 4th vertex near edge midpoint
    let almost_tri = Polygon2D::from_vertices(vec![
        Vector2::new(1.0, 0.0),
        Vector2::new(-0.5, 0.866),
        Vector2::new(0.0, 0.3),  // Near midpoint of edge from (-0.5, 0.866) to (-0.5, -0.866)
        Vector2::new(-0.5, -0.866),
    ]).unwrap();
    let (b, h, r) = compare_algorithms("almost-triangle(4-gon) × triangle", &almost_tri, &tri);
    if (r - 1.0).abs() > tolerance {
        all_pass = false;
        println!("  ❌ FAILED");
    }

    println!("\n{}", "=".repeat(80));
    if all_pass {
        println!("✅ ALL TESTS PASSED");
    } else {
        println!("❌ SOME TESTS FAILED");
        panic!("Not all test cases agree between billiard and HK2017");
    }
}
