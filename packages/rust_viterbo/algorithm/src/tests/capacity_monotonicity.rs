//! Tests for the capacity monotonicity axiom: K ⊆ L ⟹ c(K) ≤ c(L).
//!
//! This is a fundamental property of symplectic capacity.

use super::fixtures::{scale_polytope, seeded_lagrangian_product};
use crate::compute::{CapacityAlgorithm, MinkowskiBilliardAlgorithm};
use proptest::prelude::*;

// ============================================================================
// Proptest Strategies
// ============================================================================

fn lagrangian_product_strategy() -> impl Strategy<Value = rust_viterbo_geom::PolytopeHRep> {
    (any::<u64>(), 3usize..=5, 3usize..=5).prop_map(|(seed, n1, n2)| {
        seeded_lagrangian_product(seed, n1, n2)
    })
}

// ============================================================================
// Monotonicity Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]

    /// Monotonicity for billiard algorithm: K ⊆ λK ⟹ c(K) ≤ c(λK) for λ > 1.
    ///
    /// We use scaling to create containment: K ⊆ λK for λ > 1.
    #[test]
    fn monotonicity_billiard(
        polytope in lagrangian_product_strategy(),
        expansion in 1.01f64..2.0,
    ) {
        let algo = MinkowskiBilliardAlgorithm::new();

        let c_inner = algo.compute(polytope.clone())
            .expect("Billiard should succeed")
            .capacity;

        let outer = scale_polytope(&polytope, expansion);
        let c_outer = algo.compute(outer)
            .expect("Billiard should succeed on expanded")
            .capacity;

        prop_assert!(
            c_inner <= c_outer + 1e-9,
            "Monotonicity violated: c(K)={} > c({}K)={}",
            c_inner, expansion, c_outer
        );
    }
}
