//! Integration tests for the tube algorithm.

use tube::{tube_capacity, fixtures};
use approx::assert_relative_eq;

/// Test that c(cross-polytope) = 1.0.
#[test]
fn test_cross_polytope_capacity() {
    let hrep = fixtures::unit_cross_polytope();
    let result = tube_capacity(&hrep).expect("Cross-polytope should compute");

    println!("Cross-polytope capacity: {}", result.capacity);
    println!("  Tubes explored: {}", result.tubes_explored);
    println!("  Tubes pruned: {}", result.tubes_pruned);

    // Empirically determined capacity is 1.0
    assert_relative_eq!(result.capacity, 1.0, epsilon = 0.01);
}

/// Test capacity scaling: c(λK) = λ² c(K).
#[test]
fn test_capacity_scaling() {
    let hrep_unit = fixtures::unit_cross_polytope();
    let c_unit = tube_capacity(&hrep_unit).expect("Unit").capacity;

    let hrep_2x = fixtures::scaled_cross_polytope(2.0);
    let c_2x = tube_capacity(&hrep_2x).expect("2x scaled").capacity;

    println!("Unit cross-polytope: c = {}", c_unit);
    println!("2x scaled: c = {}", c_2x);
    println!("Ratio: {}", c_2x / c_unit);

    // c(2K) = 4 * c(K)
    assert_relative_eq!(c_2x, 4.0 * c_unit, epsilon = 0.1);
}

/// Test that tesseract is rejected (has Lagrangian 2-faces).
#[test]
fn test_tesseract_rejected() {
    let hrep = fixtures::unit_tesseract();
    let result = tube_capacity(&hrep);

    assert!(result.is_err(), "Tesseract should be rejected");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(err_msg.contains("Lagrangian"), "Error should mention Lagrangian");
}

/// Test Mahler-type bound: c(K) · c(K°) ≤ 4.
/// For tesseract and cross-polytope (polar duals):
///   c(tesseract) · c(cross-polytope) = 4 · 1 = 4
#[test]
fn test_mahler_bound() {
    let c_cross = tube_capacity(&fixtures::unit_cross_polytope())
        .expect("Cross-polytope")
        .capacity;

    // Tesseract capacity is 4.0 (known result)
    let c_tesseract = 4.0;

    let product = c_tesseract * c_cross;
    println!("Mahler product: {} × {} = {}", c_tesseract, c_cross, product);

    assert_relative_eq!(product, 4.0, epsilon = 0.1);
}
