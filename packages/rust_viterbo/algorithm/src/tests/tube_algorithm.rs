//! Tests for the tube algorithm (CH2021 method).
//!
//! The tube algorithm works on non-Lagrangian polytopes but requires
//! non-degenerate 2-faces with rotation numbers in (0, 0.5).

use super::fixtures::{generic_polytope, perturbed_tesseract, tesseract};
use crate::compute::{CapacityAlgorithm, TubeAlgorithm};
use crate::result::AlgorithmError;
use crate::tube::Tube;

// ============================================================================
// Tube Construction Tests
// ============================================================================

/// Root tube has zero rotation.
#[test]
fn root_tube_has_zero_rotation() {
    let data = perturbed_tesseract();
    for face in &data.two_faces {
        let tube = Tube::create_root(face);
        assert_eq!(tube.rotation, 0.0);
    }
}

/// Root tube sequence contains both facets.
#[test]
fn root_tube_sequence_correct() {
    let data = perturbed_tesseract();
    if let Some(face) = data.two_faces.first() {
        let tube = Tube::create_root(face);
        assert_eq!(tube.facet_sequence, vec![face.i, face.j]);
    }
}

// ============================================================================
// Algorithm Behavior Tests
// ============================================================================

/// Tube returns NoValidOrbits for Lagrangian product (expected).
#[test]
fn tube_returns_no_valid_orbits_for_lagrangian_product() {
    let algo = TubeAlgorithm::new();
    let result = algo.compute(tesseract());
    assert!(
        matches!(result, Err(AlgorithmError::NoValidOrbits)),
        "expected NoValidOrbits for Lagrangian square product, got {:?}",
        result
    );
}

/// Both ablation variants return NoValidOrbits for tesseract.
#[test]
fn ablation_variants_return_no_valid_orbits() {
    let hrep = tesseract();
    let with_cutoffs = TubeAlgorithm::with_options(true, true);
    let without_cutoffs = TubeAlgorithm::with_options(false, true);

    let result1 = with_cutoffs.compute(hrep.clone());
    let result2 = without_cutoffs.compute(hrep);

    assert!(
        matches!(&result1, Err(AlgorithmError::NoValidOrbits)),
        "with_cutoffs: expected NoValidOrbits, got {:?}",
        result1
    );
    assert!(
        matches!(&result2, Err(AlgorithmError::NoValidOrbits)),
        "without_cutoffs: expected NoValidOrbits, got {:?}",
        result2
    );
}

/// Tube supports any polytope (no input restrictions).
#[test]
fn tube_supports_any_polytope() {
    let algo = TubeAlgorithm::new();
    assert!(algo.supports_input(&tesseract()).is_ok());
    assert!(algo.supports_input(&generic_polytope()).is_ok());
}

// ============================================================================
// Success Case (currently blocked)
// ============================================================================

/// Find a polytope where tube algorithm successfully computes capacity.
///
/// BLOCKED: Tube returns NoValidOrbits on all tested polytopes.
/// Candidates to try:
/// - Cross-polytope (16-cell): 16 facets, non-Lagrangian
/// - Random perturbations of Lagrangian products with larger ε
/// - Polytopes from papers that use CH2021 method
#[test]
#[ignore = "blocked: tube algorithm never succeeds on tested polytopes"]
fn tube_algorithm_success_case() {
    todo!()
}
