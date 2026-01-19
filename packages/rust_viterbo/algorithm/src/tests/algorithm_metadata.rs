//! Tests for algorithm metadata and input validation.

use super::fixtures::{generic_polytope, tesseract};
use crate::compute::{compute_capacity, CapacityAlgorithm, HK2019Algorithm, MinkowskiBilliardAlgorithm, TubeAlgorithm};
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

/// compute_capacity returns NoValidOrbits for tesseract (tube fails, billiard not selected).
#[test]
fn compute_capacity_returns_no_valid_orbits_for_tesseract() {
    let result = compute_capacity(tesseract());
    assert!(
        matches!(result, Err(AlgorithmError::NoValidOrbits)),
        "tesseract should return NoValidOrbits, got {:?}",
        result
    );
}

/// Diagnostics are populated even when no orbits found.
#[test]
fn diagnostics_populated_when_no_orbits() {
    let result = compute_capacity(tesseract());
    match result {
        Err(AlgorithmError::NoValidOrbits) => {}
        Ok(r) => {
            assert!(r.diagnostics.nodes_explored > 0);
        }
        Err(e) => panic!("unexpected error: {e}"),
    }
}
