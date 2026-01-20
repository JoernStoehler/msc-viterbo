//! Tests for algorithm metadata and input validation.

use super::fixtures::{generic_polytope, tesseract};
use crate::compute::{
    compute_capacity, CapacityAlgorithm, HK2019Algorithm, MinkowskiBilliardAlgorithm, TubeAlgorithm,
};
use crate::result::AlgorithmError;

// ============================================================================
// Metadata Tests
// ============================================================================

#[test]
fn tube_algorithm_metadata() {
    let algo = TubeAlgorithm::new();
    let meta = algo.metadata();
    assert_eq!(meta.name, "Tube (CH2021)");
    assert!(!meta.lagrangian_product_only);
}

#[test]
fn hk2019_algorithm_metadata() {
    let algo = HK2019Algorithm::new();
    assert_eq!(algo.metadata().name, "HK2019 (QP)");
}

#[test]
fn minkowski_billiard_metadata() {
    let algo = MinkowskiBilliardAlgorithm::new();
    assert!(algo.metadata().lagrangian_product_only);
}

// ============================================================================
// Input Validation Tests
// ============================================================================

#[test]
fn minkowski_rejects_non_lagrangian_product() {
    let algo = MinkowskiBilliardAlgorithm::new();
    assert!(algo.supports_input(&generic_polytope()).is_err());
}

#[test]
fn minkowski_accepts_lagrangian_product() {
    let algo = MinkowskiBilliardAlgorithm::new();
    assert!(algo.supports_input(&tesseract()).is_ok());
}

// ============================================================================
// Dispatcher Tests
// ============================================================================

/// compute_capacity returns InvalidInput for tesseract.
///
/// The tesseract is a Lagrangian product ([-1,1]^2 x [-1,1]^2), so ALL its 2-faces
/// are Lagrangian (omega(n_i, n_j) = 0 for all pairs of axis-aligned normals).
/// The tube algorithm requires non-Lagrangian 2-faces, so it must return InvalidInput.
#[test]
fn compute_capacity_returns_failure_for_tesseract() {
    let result = compute_capacity(tesseract());
    assert!(
        matches!(result, Err(AlgorithmError::InvalidInput(_))),
        "tesseract is Lagrangian product, should return InvalidInput, got {:?}",
        result
    );
}

/// Diagnostics are populated when algorithm runs (not for InvalidInput).
///
/// Use a valid non-Lagrangian polytope to test diagnostics.
#[test]
fn diagnostics_populated_when_algorithm_runs() {
    use crate::tests::fixtures::random_nonlagrangian_polytope;
    // Seed 57 produces a valid 5-facet polytope with 0 Lagrangian 2-faces
    let polytope = random_nonlagrangian_polytope(57).expect("seed 57 must produce valid polytope");
    let result = compute_capacity(polytope);
    match result {
        Err(AlgorithmError::NoValidOrbits) => {}
        Err(AlgorithmError::SearchExhausted) => {}
        Ok(r) => {
            assert!(r.diagnostics.nodes_explored > 0);
        }
        Err(AlgorithmError::InvalidInput(msg)) => {
            panic!("seed 57 should be valid, got InvalidInput: {}", msg);
        }
        Err(e) => panic!("unexpected error: {e}"),
    }
}
