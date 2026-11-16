//! Tests for billiard witness orbit geometry and verification.
//!
//! The billiard algorithm returns a WitnessOrbit with breakpoints on facets.
//! These tests verify the geometric correctness of the witness.
//!
//! # Test Categories
//!
//! 1. **Existence tests**: Verify witness is returned (PASS)
//! 2. **Breakpoint tests**: Verify breakpoints lie on facets (PASS)
//! 3. **Reeb flow tests**: Verify velocities satisfy Reeb inclusion (KNOWN FAILURE)
//! 4. **segment_times tests**: Verify action computation (NOT IMPLEMENTED)
//!
//! # Known Limitations
//!
//! - **segment_times are placeholder zeros**: The billiard algorithm computes
//!   breakpoints and capacity, but does not derive the Reeb flow times between
//!   segments. This is a known gap that requires proper derivation from Reeb
//!   flow equations.
//!
//! - **Reeb flow error is high (~2.36)**: The witness velocities computed from
//!   breakpoint differences do NOT satisfy the Reeb differential inclusion.
//!   The breakpoints are geometrically correct, but the flow dynamics are wrong.

use super::fixtures::seeded_lagrangian_product;
use crate::billiard::extract_lagrangian_factors;
use crate::billiard_lp::compute_billiard_capacity_lp;
use crate::compute::{CapacityAlgorithm, MinkowskiBilliardAlgorithm};
use proptest::prelude::*;

// ============================================================================
// Proptest Strategies
// ============================================================================

fn lagrangian_product_strategy() -> impl Strategy<Value = rust_viterbo_geom::PolytopeHRep> {
    (any::<u64>(), 3usize..=5, 3usize..=5)
        .prop_map(|(seed, n1, n2)| seeded_lagrangian_product(seed, n1, n2))
}

// ============================================================================
// Witness Existence Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    /// Verify that billiard algorithm returns a witness for Lagrangian products.
    ///
    /// **Expected**: Always succeeds. Billiard algorithm is complete for
    /// Lagrangian products.
    #[test]
    fn witness_exists(polytope in lagrangian_product_strategy()) {
        let algo = MinkowskiBilliardAlgorithm::new();
        let result = algo.compute(polytope)
            .expect("Billiard should succeed on Lagrangian products");

        prop_assert!(
            result.witness.is_some(),
            "Billiard MUST return a witness - this is a completeness property"
        );

        prop_assert!(
            result.capacity > 0.0,
            "Capacity must be positive for non-empty polytopes, got {}",
            result.capacity
        );
    }
}

// ============================================================================
// Witness Breakpoint Verification (SHOULD PASS)
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    /// Verify that witness breakpoints lie on their claimed facets.
    ///
    /// **Expected**: PASS. The billiard LP computes breakpoints that satisfy
    /// the facet constraints by construction.
    ///
    /// **What this tests**: For each breakpoint p_i on facet k_i, verify
    /// |<n_{k_i}, p_i> - h_{k_i}| < tolerance.
    #[test]
    fn witness_breakpoints_on_facets(polytope in lagrangian_product_strategy()) {
        let algo = MinkowskiBilliardAlgorithm::new();
        let result = algo.compute(polytope.clone())
            .expect("Billiard should succeed");

        let witness = result.witness
            .expect("Billiard should return a witness");

        let tol = 1e-6;
        let verification = witness.verify(&polytope, tol);

        // EXPLICIT ASSERTION: breakpoint facet error must be small
        prop_assert!(
            verification.max_facet_error < tol,
            "BREAKPOINT ERROR: max_facet_error={:.2e} exceeds tolerance {:.2e}\n\
             This indicates the LP solver produced invalid breakpoints.",
            verification.max_facet_error, tol
        );

        // Sanity check: capacity is positive
        prop_assert!(
            result.capacity > 0.0,
            "Capacity must be positive, got {}",
            result.capacity
        );
    }
}

// ============================================================================
// Witness Reeb Flow Verification (KNOWN FAILURE - SHOULD PANIC)
// ============================================================================

/// Verify that witness velocities satisfy the Reeb differential inclusion.
///
/// **KNOWN BUG**: Currently FAILS because max_flow_error ≈ 2.36, far exceeding
/// the tolerance of 0.1. The billiard witness has correct BREAKPOINTS but
/// the VELOCITIES between them do not satisfy the Reeb differential inclusion
/// (v should be in cone of Jn).
///
/// **Root cause**: The billiard algorithm computes a Minkowski billiard
/// trajectory, not a Reeb orbit. The conversion to witness orbit does
/// not properly derive velocities from the Reeb flow equations.
///
/// **When this passes**: Someone has properly implemented Reeb flow derivation.
/// Remove #[should_panic] when fixed.
#[test]
#[should_panic(expected = "flow error")]
fn witness_reeb_flow_error_is_small() {
    // Use a single representative test case instead of proptest
    let polytope = seeded_lagrangian_product(42, 4, 4);
    let algo = MinkowskiBilliardAlgorithm::new();
    let result = algo.compute(polytope.clone())
        .expect("Billiard should succeed");

    let witness = result.witness
        .expect("Billiard should return a witness");

    let facet_tol = 1e-6;
    let verification = witness.verify(&polytope, facet_tol);

    // CORRECT ASSERTION: flow error should be small for valid Reeb orbit
    let flow_tol = 0.1;
    assert!(
        verification.max_flow_error < flow_tol,
        "flow error {:.4} exceeds tolerance {:.4} - Reeb flow derivation not implemented",
        verification.max_flow_error, flow_tol
    );
}

// ============================================================================
// Witness segment_times Verification (KNOWN FAILURE - SHOULD PANIC)
// ============================================================================

/// Verify that segment_times are positive (properly computed Reeb flow times).
///
/// **KNOWN BUG**: Currently FAILS because segment_times are placeholder zeros.
/// The billiard LP optimizes trajectory geometry, not the Reeb flow
/// parameterization. Deriving segment_times requires solving the Reeb flow
/// ODEs along each segment.
///
/// **When this passes**: Someone has properly implemented Reeb flow time derivation.
/// Remove #[should_panic] when fixed.
#[test]
#[should_panic(expected = "segment_times should be positive")]
fn witness_segment_times_are_positive() {
    // Use a single representative test case instead of proptest
    let polytope = seeded_lagrangian_product(42, 4, 4);
    let algo = MinkowskiBilliardAlgorithm::new();
    let result = algo.compute(polytope)
        .expect("Billiard should succeed");

    let witness = result.witness
        .expect("Billiard should return a witness");

    // CORRECT ASSERTION: segment_times should be positive for valid Reeb flow
    assert!(
        witness.segment_times.iter().all(|&t| t > 0.0),
        "segment_times should be positive, got {:?} - Reeb flow times not implemented",
        witness.segment_times
    );
}

// ============================================================================
// Tesseract-Specific Tests (Concrete Expected Values)
// ============================================================================

/// Test witness for tesseract with explicit expected values.
///
/// **Expected**: Tesseract capacity = 4.0, breakpoints on axis-aligned facets.
#[test]
fn tesseract_witness_explicit_expectations() {
    use super::fixtures::tesseract;

    let polytope = tesseract();
    let algo = MinkowskiBilliardAlgorithm::new();
    let result = algo.compute(polytope.clone())
        .expect("Billiard should succeed on tesseract");

    // EXPLICIT: capacity must be 4.0
    assert!(
        (result.capacity - 4.0).abs() < 1e-6,
        "Tesseract capacity must be 4.0, got {}",
        result.capacity
    );

    let witness = result.witness.expect("Must have witness");

    // EXPLICIT: must have breakpoints (at least 2 for a closed orbit)
    assert!(
        witness.breakpoints.len() >= 2,
        "Witness must have at least 2 breakpoints, got {}",
        witness.breakpoints.len()
    );

    // EXPLICIT: breakpoints must lie on facets
    let tol = 1e-6;
    let verification = witness.verify(&polytope, tol);
    assert!(
        verification.max_facet_error < tol,
        "Breakpoint facet error {:.2e} exceeds tolerance {:.2e}",
        verification.max_facet_error, tol
    );

    // Note: segment_times are currently placeholder zeros (known limitation).
    // See witness_segment_times_are_positive for the tracked failure.
}

/// Test witness for triangle product with explicit expected values.
///
/// **Expected**: Triangle×Triangle capacity ≈ 1.5, breakpoints on facets.
#[test]
fn triangle_witness_explicit_expectations() {
    use super::fixtures::equilateral_triangle_product;

    let polytope = equilateral_triangle_product();
    let algo = MinkowskiBilliardAlgorithm::new();
    let result = algo.compute(polytope.clone())
        .expect("Billiard should succeed on triangle product");

    // EXPLICIT: capacity must be approximately 1.5
    assert!(
        (result.capacity - 1.5).abs() < 0.1,
        "Triangle×Triangle capacity should be ~1.5, got {}",
        result.capacity
    );

    let witness = result.witness.expect("Must have witness");

    // EXPLICIT: breakpoints must lie on facets
    let tol = 1e-6;
    let verification = witness.verify(&polytope, tol);
    assert!(
        verification.max_facet_error < tol,
        "Breakpoint facet error {:.2e} exceeds tolerance {:.2e}",
        verification.max_facet_error, tol
    );

    // Note: segment_times are currently placeholder zeros (known limitation).
    // See witness_segment_times_are_positive for the tracked failure.
}

// ============================================================================
// Debug Tests
// ============================================================================

/// Debug test for investigating witness facet verification.
///
/// This test prints detailed information about the witness construction.
/// It has an explicit assertion that breakpoints lie on facets.
#[test]
fn debug_witness_facet_error() {
    let polytope = seeded_lagrangian_product(0, 3, 3);

    eprintln!("=== Debug Witness Facet Error ===");
    eprintln!("Polytope normals and heights:");
    for (i, (n, h)) in polytope.normals.iter().zip(&polytope.heights).enumerate() {
        eprintln!(
            "  [{}]: n=({:.4}, {:.4}, {:.4}, {:.4}), h={:.4}",
            i, n.x, n.y, n.z, n.w, h
        );
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

    let result =
        compute_billiard_capacity_lp(polytope.clone()).expect("LP billiard should succeed");

    eprintln!("\nLP Result:");
    eprintln!("  capacity: {:.6}", result.capacity);

    let witness = result.witness.expect("Should have witness");
    eprintln!("\nWitness:");
    eprintln!("  breakpoints: {} points", witness.breakpoints.len());
    for (i, bp) in witness.breakpoints.iter().enumerate() {
        eprintln!(
            "    [{}]: ({:.4}, {:.4}, {:.4}, {:.4})",
            i, bp.x, bp.y, bp.z, bp.w
        );
    }
    eprintln!("  facet_sequence: {:?}", witness.facet_sequence);

    let tol = 1e-6;
    let verification = witness.verify(&polytope, tol);
    eprintln!("\nVerification result:");
    eprintln!("  valid: {}", verification.valid);
    eprintln!("  max_facet_error: {:.2e}", verification.max_facet_error);
    eprintln!("  max_flow_error: {:.4}", verification.max_flow_error);

    // EXPLICIT ASSERTION: breakpoints on facets
    assert!(
        verification.max_facet_error < tol,
        "Facet error too large: {:.2e} (expected < {:.2e})",
        verification.max_facet_error, tol
    );

    // Debug output for known limitations (flow error and segment_times).
    // See witness_reeb_flow_error_is_small and witness_segment_times_are_positive
    // for the tracked failures with #[should_panic].
    eprintln!("\nKnown limitations:");
    eprintln!("  max_flow_error: {:.4} (should be < 0.1 when fixed)", verification.max_flow_error);
    eprintln!("  segment_times: {:?} (should be positive when fixed)", witness.segment_times);
}
