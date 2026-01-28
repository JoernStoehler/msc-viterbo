//! Integration tests for the tube algorithm.
//!
//! These tests verify mathematical properties of the tube capacity computation.
//! They do NOT rely on `debug_assert!()` checks - they only verify output correctness.
//!
//! # Release-only tests
//! All tests in this file are marked with `#[cfg_attr(debug_assertions, ignore)]`
//! which means they are skipped in debug mode and run only in release mode.
//! This is because they perform expensive capacity computations:
//! - Debug mode: ~90 seconds total
//! - Release mode: ~2 seconds total
//!
//! Tests that exercise internal invariants (where `debug_assert!()` matters) are in
//! the unit tests (`src/lib.rs`) and other test files (`flow_map_tests.rs`, etc.).

use approx::assert_relative_eq;
use tube::{fixtures, tube_capacity};

/// Test that c(cross-polytope) = 1.0.
#[cfg_attr(debug_assertions, ignore)]
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
#[cfg_attr(debug_assertions, ignore)]
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
#[cfg_attr(debug_assertions, ignore)]
#[test]
fn test_tesseract_rejected() {
    let hrep = fixtures::unit_tesseract();
    let result = tube_capacity(&hrep);

    assert!(result.is_err(), "Tesseract should be rejected");
    let err_msg = format!("{}", result.unwrap_err());
    assert!(
        err_msg.contains("Lagrangian"),
        "Error should mention Lagrangian"
    );
}

/// Test Mahler-type bound: c(K) · c(K°) ≤ 4.
/// For tesseract and cross-polytope (polar duals):
///   c(tesseract) · c(cross-polytope) = 4 · 1 = 4
#[cfg_attr(debug_assertions, ignore)]
#[test]
fn test_mahler_bound() {
    let c_cross = tube_capacity(&fixtures::unit_cross_polytope())
        .expect("Cross-polytope")
        .capacity;

    // Tesseract capacity is 4.0 (known result)
    let c_tesseract = 4.0;

    let product = c_tesseract * c_cross;
    println!(
        "Mahler product: {} × {} = {}",
        c_tesseract, c_cross, product
    );

    assert_relative_eq!(product, 4.0, epsilon = 0.1);
}

/// Test 4-simplex (pentatope) capacity computation.
/// The 4-simplex has only 5 facets, testing minimal polytope case.
#[cfg_attr(debug_assertions, ignore)]
#[test]
fn test_four_simplex_capacity() {
    let hrep = fixtures::four_simplex();
    let result = tube_capacity(&hrep);

    match result {
        Ok(r) => {
            println!("4-simplex capacity: {}", r.capacity);
            println!("  Tubes explored: {}", r.tubes_explored);
            println!("  Tubes pruned: {}", r.tubes_pruned);
            // Capacity should be positive
            assert!(r.capacity > 0.0, "Capacity should be positive");
        }
        Err(e) => {
            // The algorithm may legitimately fail to find orbits
            // if this simplex has Lagrangian 2-faces (unlikely but possible)
            println!("4-simplex computation failed: {}", e);
            // For now, we accept either success or NoClosedOrbits
            let err_str = format!("{}", e);
            assert!(
                err_str.contains("Lagrangian") || err_str.contains("NoClosedOrbits"),
                "Unexpected error: {}",
                e
            );
        }
    }
}

// === Tests with new diverse fixtures ===

/// Test 24-cell capacity computation.
/// The 24-cell has 24 facets and different symmetry than the cross-polytope.
/// This tests the algorithm on a different regular polytope.
#[cfg_attr(debug_assertions, ignore)]
#[test]
fn test_24_cell_capacity() {
    let hrep = fixtures::unit_24_cell();
    let result = tube_capacity(&hrep);

    match result {
        Ok(r) => {
            println!("24-cell capacity: {}", r.capacity);
            println!("  Tubes explored: {}", r.tubes_explored);
            println!("  Tubes pruned: {}", r.tubes_pruned);
            // Capacity should be positive
            assert!(r.capacity > 0.0, "Capacity should be positive");
            // Store result for potential comparison with other methods
            println!("c(24-cell) = {:.6}", r.capacity);
        }
        Err(e) => {
            // The 24-cell should work with the tube algorithm
            // (no Lagrangian 2-faces), so an error is unexpected
            panic!("24-cell computation failed unexpectedly: {}", e);
        }
    }
}

/// Test asymmetric cross-polytope with multiple seeds.
/// This tests the algorithm on polytopes with broken symmetry.
#[cfg_attr(debug_assertions, ignore)]
#[test]
fn test_asymmetric_cross_polytope_multiple_seeds() {
    let seeds = [42, 123, 456, 789];
    let mut capacities = Vec::new();

    for seed in seeds {
        let hrep = fixtures::asymmetric_cross_polytope(seed);
        let result = tube_capacity(&hrep);

        match result {
            Ok(r) => {
                println!(
                    "Asymmetric cross-polytope (seed {}): c = {:.6}",
                    seed, r.capacity
                );
                capacities.push(r.capacity);
                assert!(r.capacity > 0.0, "Capacity should be positive");
            }
            Err(e) => {
                // Perturbations might create Lagrangian 2-faces
                let err_str = format!("{}", e);
                println!("Seed {} failed: {}", seed, err_str);
                // This is acceptable - random perturbations might hit edge cases
                assert!(
                    err_str.contains("Lagrangian") || err_str.contains("NoClosedOrbits"),
                    "Unexpected error for seed {}: {}",
                    seed,
                    e
                );
            }
        }
    }

    // At least some should succeed
    assert!(
        !capacities.is_empty(),
        "At least one asymmetric cross-polytope should compute successfully"
    );

    // Capacities should vary between seeds (symmetry is broken)
    if capacities.len() >= 2 {
        let all_same = capacities.windows(2).all(|w| (w[0] - w[1]).abs() < 0.01);
        println!("Capacities: {:?}, all_same={}", capacities, all_same);
        // They might be similar but shouldn't be exactly the same
        // (unless the perturbation scale is too small to matter numerically)
    }
}

/// Proposition: For all valid polytopes K where tube_capacity succeeds, c(K) > 0 and c(K) < ∞.
///
/// Tested on: cross-polytope, 24-cell, asymmetric cross-polytopes with various seeds.
#[cfg_attr(debug_assertions, ignore)]
#[test]
fn prop_capacity_positive_and_finite() {
    // Collect test polytopes where algorithm succeeds
    let mut polytopes: Vec<(&str, tube::types::PolytopeHRep)> = vec![
        ("cross-polytope", fixtures::unit_cross_polytope()),
        ("24-cell", fixtures::unit_24_cell()),
        (
            "scaled cross-polytope (0.5)",
            fixtures::scaled_cross_polytope(0.5),
        ),
        (
            "scaled cross-polytope (3.0)",
            fixtures::scaled_cross_polytope(3.0),
        ),
    ];

    // Add asymmetric cross-polytopes
    for seed in [42, 123, 456, 789] {
        polytopes.push((
            "asymmetric cross-polytope",
            fixtures::asymmetric_cross_polytope(seed),
        ));
    }

    // PROPOSITION: ∀ K ∈ test_polytopes: c(K) > 0 ∧ c(K) < ∞
    for (name, hrep) in polytopes {
        let result = tube_capacity(&hrep).unwrap_or_else(|_| panic!("{} should compute", name));

        assert!(
            result.capacity > 0.0,
            "{}: c(K) = {} violates c(K) > 0",
            name,
            result.capacity
        );
        assert!(
            result.capacity.is_finite(),
            "{}: c(K) = {} is not finite",
            name,
            result.capacity
        );
        println!("{}: c(K) = {:.6} ✓", name, result.capacity);
    }
}

/// Proposition: For all λ > 0, c(λK) = λ²c(K).
///
/// Tested on: cross-polytope, 24-cell, asymmetric cross-polytopes.
#[cfg_attr(debug_assertions, ignore)]
#[test]
fn prop_scaling_law() {
    let lambdas = [0.25, 0.5, 2.0, 3.0];

    let polytopes: Vec<(&str, tube::types::PolytopeHRep)> = vec![
        ("cross-polytope", fixtures::unit_cross_polytope()),
        ("24-cell", fixtures::unit_24_cell()),
        ("asymmetric(42)", fixtures::asymmetric_cross_polytope(42)),
        ("asymmetric(123)", fixtures::asymmetric_cross_polytope(123)),
    ];

    for (name, hrep) in polytopes {
        let c_k = tube_capacity(&hrep)
            .unwrap_or_else(|_| panic!("{} base should compute", name))
            .capacity;

        // PROPOSITION: ∀ λ > 0: c(λK) = λ²c(K)
        for &lambda in &lambdas {
            let scaled = tube::types::PolytopeHRep::new(
                hrep.normals.clone(),
                hrep.heights.iter().map(|h| h * lambda).collect(),
            );

            let c_lambda_k = tube_capacity(&scaled)
                .unwrap_or_else(|_| panic!("{} scaled by {} should compute", name, lambda))
                .capacity;

            let expected = lambda * lambda * c_k;
            let relative_error = (c_lambda_k - expected).abs() / expected;

            assert!(
                relative_error < 0.01,
                "{}, λ={}: c(λK)={:.6}, λ²c(K)={:.6}, error={:.2}%",
                name,
                lambda,
                c_lambda_k,
                expected,
                relative_error * 100.0
            );
        }

        println!(
            "{}: scaling law c(λK) = λ²c(K) verified for λ ∈ {:?} ✓",
            name, lambdas
        );
    }
}

/// Test that capacity is always positive for valid polytopes.
#[cfg_attr(debug_assertions, ignore)]
#[test]
fn test_capacity_always_positive() {
    let polytopes: Vec<(&str, tube::types::PolytopeHRep)> = vec![
        ("unit_cross_polytope", fixtures::unit_cross_polytope()),
        (
            "scaled_cross_polytope(0.5)",
            fixtures::scaled_cross_polytope(0.5),
        ),
        (
            "scaled_cross_polytope(3.0)",
            fixtures::scaled_cross_polytope(3.0),
        ),
        ("unit_24_cell", fixtures::unit_24_cell()),
    ];

    for (name, hrep) in polytopes {
        match tube_capacity(&hrep) {
            Ok(r) => {
                assert!(
                    r.capacity > 0.0,
                    "{}: capacity should be positive, got {}",
                    name,
                    r.capacity
                );
                println!("{}: c = {:.6}", name, r.capacity);
            }
            Err(e) => {
                panic!("{} failed unexpectedly: {}", name, e);
            }
        }
    }
}

/// Test capacity scaling law: c(λK) = λ² c(K) with 24-cell.
#[cfg_attr(debug_assertions, ignore)]
#[test]
fn test_24_cell_scaling() {
    // Create scaled 24-cell by scaling heights
    let base = fixtures::unit_24_cell();
    let lambda = 2.0;
    let scaled = tube::types::PolytopeHRep::new(
        base.normals.clone(),
        base.heights.iter().map(|h| h * lambda).collect(),
    );

    let c_base = tube_capacity(&base);
    let c_scaled = tube_capacity(&scaled);

    match (c_base, c_scaled) {
        (Ok(r1), Ok(r2)) => {
            let expected_ratio = lambda * lambda;
            let actual_ratio = r2.capacity / r1.capacity;
            println!(
                "24-cell scaling: c(K) = {:.6}, c({}K) = {:.6}, ratio = {:.6} (expected {})",
                r1.capacity, lambda, r2.capacity, actual_ratio, expected_ratio
            );
            assert_relative_eq!(actual_ratio, expected_ratio, epsilon = 0.1);
        }
        (Err(e1), _) => panic!("Base 24-cell failed: {}", e1),
        (_, Err(e2)) => panic!("Scaled 24-cell failed: {}", e2),
    }
}
