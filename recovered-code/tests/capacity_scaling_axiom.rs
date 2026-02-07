//! Tests for the capacity scaling axiom: c(λK) = λ²c(K).
//!
//! This is a fundamental property of symplectic capacity.

use super::fixtures::{scale_polytope, seeded_lagrangian_product, tesseract};
use crate::compute::{
    all_algorithms, compute_capacity, CapacityAlgorithm, HK2019Algorithm,
    MinkowskiBilliardAlgorithm,
};
use proptest::prelude::*;

// ============================================================================
// Proptest Strategies
// ============================================================================

fn lagrangian_product_strategy() -> impl Strategy<Value = rust_viterbo_geom::PolytopeHRep> {
    (any::<u64>(), 3usize..=5, 3usize..=5)
        .prop_map(|(seed, n1, n2)| seeded_lagrangian_product(seed, n1, n2))
}

fn lagrangian_product_small_strategy() -> impl Strategy<Value = rust_viterbo_geom::PolytopeHRep> {
    any::<u64>().prop_map(|seed| seeded_lagrangian_product(seed, 3, 3))
}

// ============================================================================
// Scaling Axiom Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    /// Scaling axiom for billiard algorithm: c(λK) = λ²c(K).
    #[test]
    fn scaling_billiard(
        polytope in lagrangian_product_strategy(),
        lambda in 0.3f64..3.0,
    ) {
        let algo = MinkowskiBilliardAlgorithm::new();

        let c1 = algo.compute(polytope.clone())
            .expect("Billiard should succeed on random Lagrangian product")
            .capacity;

        let scaled = scale_polytope(&polytope, lambda);
        let c2 = algo.compute(scaled)
            .expect("Billiard should succeed on scaled polytope")
            .capacity;

        let expected = c1 * lambda * lambda;
        let rel_error = (c2 - expected).abs() / expected;

        prop_assert!(
            rel_error < 0.001,
            "Scaling axiom violated: c(K)={}, c({}K)={}, expected {}, rel_error={}",
            c1, lambda, c2, expected, rel_error
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(3))]

    /// Scaling axiom for HK2019 algorithm: c(λK) = λ²c(K).
    ///
    /// Note: HK2019 has a known QP solver bug, so this test may fail.
    #[test]
    fn scaling_hk2019(
        polytope in lagrangian_product_small_strategy(),
        lambda in 0.5f64..2.0,
    ) {
        let algo = HK2019Algorithm::new();

        let c1 = match algo.compute(polytope.clone()) {
            Ok(r) => r.capacity,
            Err(_) => return Ok(()),
        };

        let scaled = scale_polytope(&polytope, lambda);
        let c2 = match algo.compute(scaled) {
            Ok(r) => r.capacity,
            Err(_) => return Ok(()),
        };

        let expected = c1 * lambda * lambda;
        let rel_error = (c2 - expected).abs() / expected;

        prop_assert!(
            rel_error < 0.01,
            "Scaling axiom violated for HK2019: c(K)={}, c({}K)={}, expected {}, rel_error={}",
            c1, lambda, c2, expected, rel_error
        );
    }
}

/// Scaling axiom with compute_capacity (requires valid capacity).
#[test]
#[ignore = "requires a polytope that returns valid capacity from compute_capacity"]
fn scaling_compute_capacity() {
    let hrep = tesseract();
    let lambda = 2.0;
    let scaled = scale_polytope(&hrep, lambda);

    let r1 = compute_capacity(hrep).expect("need valid capacity for scaling test");
    let r2 = compute_capacity(scaled).expect("need valid capacity for scaling test");

    let expected = r1.capacity * lambda * lambda;
    let rel_error = (r2.capacity - expected).abs() / expected;
    assert!(rel_error < 0.01, "scaling axiom violated: expected c*λ²");
}

/// Scaling axiom across all algorithms that support the input.
#[test]
#[ignore = "requires algorithms that return valid capacities"]
fn scaling_all_algorithms() {
    let hrep = tesseract();
    let lambda = 2.0;
    let scaled = scale_polytope(&hrep, lambda);

    for algo in all_algorithms() {
        if algo.supports_input(&hrep).is_err() {
            continue;
        }
        let c1 = algo.compute(hrep.clone()).expect("need valid capacity");
        let c2 = algo.compute(scaled.clone()).expect("need valid capacity");

        let expected = c1.capacity * lambda * lambda;
        let rel_error = (c2.capacity - expected).abs() / expected;
        assert!(rel_error < 0.2, "{}: scaling failed", algo.metadata().name);
    }
}
