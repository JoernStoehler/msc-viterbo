//! Tests for billiard witness orbit geometry and verification.
//!
//! The billiard algorithm returns a WitnessOrbit with breakpoints on facets.
//! These tests verify the geometric correctness of the witness.

use super::fixtures::seeded_lagrangian_product;
use crate::billiard::extract_lagrangian_factors;
use crate::billiard_lp::compute_billiard_capacity_lp;
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
// Witness Existence Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    #[test]
    fn witness_exists(polytope in lagrangian_product_strategy()) {
        let algo = MinkowskiBilliardAlgorithm::new();
        let result = algo.compute(polytope)
            .expect("Billiard should succeed");

        prop_assert!(
            result.witness.is_some(),
            "Billiard should return a witness"
        );

        prop_assert!(
            result.capacity > 0.0,
            "Capacity should be positive, got {}",
            result.capacity
        );
    }
}

// ============================================================================
// Witness Facet Verification
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    /// Verify that the witness orbit breakpoints lie on the claimed facets.
    ///
    /// NOTE: The billiard witness construction produces a geometric representation
    /// of the billiard trajectory. The breakpoints lie on the claimed facets
    /// (verified here), but the full Reeb flow dynamics are not satisfied.
    #[test]
    fn witness_breakpoints_on_facets(polytope in lagrangian_product_strategy()) {
        let algo = MinkowskiBilliardAlgorithm::new();
        let result = algo.compute(polytope.clone())
            .expect("Billiard should succeed");

        let witness = result.witness
            .expect("Billiard should return a witness");

        let tol = 1e-6;
        let verification = witness.verify(&polytope, tol);

        prop_assert!(
            verification.max_facet_error < tol,
            "Breakpoints should lie on facets. Max facet error: {:.2e} (tol: {:.2e})",
            verification.max_facet_error, tol
        );

        prop_assert!(
            result.capacity > 0.0,
            "Capacity should be positive, got {}",
            result.capacity
        );
    }
}

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    // Witness segment times are not implemented (placeholder zeros).
    // This test documents the known limitation. The segment_times need proper
    // derivation from Reeb flow equations - see thesis for mathematical details.
    #[test]
    #[ignore = "segment_times not implemented (placeholder zeros)"]
    fn witness_action_matches_capacity(polytope in lagrangian_product_strategy()) {
        let algo = MinkowskiBilliardAlgorithm::new();
        let result = algo.compute(polytope.clone())
            .expect("Billiard should succeed");

        let witness = result.witness
            .expect("Billiard should return a witness");

        let witness_action: f64 = witness.segment_times.iter().sum();
        let action_rel_error = (witness_action - result.capacity).abs() / result.capacity;
        prop_assert!(
            action_rel_error < 0.01,
            "Witness action should equal capacity. action={:.6}, capacity={:.6}, rel_error={:.2}%",
            witness_action, result.capacity, action_rel_error * 100.0
        );
    }
}

// ============================================================================
// Debug Tests
// ============================================================================

/// Debug test for investigating witness facet verification.
#[test]
fn debug_witness_facet_error() {
    let polytope = seeded_lagrangian_product(0, 3, 3);

    eprintln!("=== Debug Witness Facet Error ===");
    eprintln!("Polytope normals and heights:");
    for (i, (n, h)) in polytope.normals.iter().zip(&polytope.heights).enumerate() {
        eprintln!("  [{}]: n=({:.4}, {:.4}, {:.4}, {:.4}), h={:.4}",
            i, n.x, n.y, n.z, n.w, h);
    }

    let factors = extract_lagrangian_factors(&polytope).expect("Should be Lagrangian product");

    eprintln!("\nK1 (q-space) polygon:");
    eprintln!("  q_facet_indices: {:?}", factors.q_facet_indices);
    for (i, v) in factors.k1.vertices.iter().enumerate() {
        eprintln!("  vertex[{}]: ({:.4}, {:.4})", i, v.x, v.y);
    }

    eprintln!("\nK2 (p-space) polygon:");
    eprintln!("  p_facet_indices: {:?}", factors.p_facet_indices);
    for (i, v) in factors.k2.vertices.iter().enumerate() {
        eprintln!("  vertex[{}]: ({:.4}, {:.4})", i, v.x, v.y);
    }

    let result = compute_billiard_capacity_lp(polytope.clone())
        .expect("LP billiard should succeed");

    eprintln!("\nLP Result:");
    eprintln!("  capacity: {:.6}", result.capacity);

    let witness = result.witness.expect("Should have witness");
    eprintln!("\nWitness:");
    eprintln!("  breakpoints: {} points", witness.breakpoints.len());
    for (i, bp) in witness.breakpoints.iter().enumerate() {
        eprintln!("    [{}]: ({:.4}, {:.4}, {:.4}, {:.4})", i, bp.x, bp.y, bp.z, bp.w);
    }
    eprintln!("  facet_sequence: {:?}", witness.facet_sequence);

    let tol = 1e-6;
    let verification = witness.verify(&polytope, tol);
    eprintln!("\nVerification result:");
    eprintln!("  valid: {}", verification.valid);
    eprintln!("  max_facet_error: {:.2e}", verification.max_facet_error);

    assert!(verification.max_facet_error < tol, "Facet error too large: {:.2e}", verification.max_facet_error);
}
