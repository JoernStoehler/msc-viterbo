//! Tests for PolytopeData construction and preprocessing.
//!
//! PolytopeData filters out Lagrangian 2-faces and computes rotation numbers.

use super::fixtures::tesseract;
use crate::polytope::PolytopeData;
use rust_viterbo_geom::perturb_polytope_normals;

// ============================================================================
// 2-Face Counting Tests
// ============================================================================

/// Tesseract has exactly 8 non-Lagrangian 2-faces.
#[test]
fn tesseract_has_eight_non_lagrangian_two_faces() {
    let data = PolytopeData::new(tesseract());
    assert_eq!(
        data.two_faces.len(),
        8,
        "tesseract should have exactly 8 non-Lagrangian 2-faces"
    );
}

/// Perturbed tesseract has more non-Lagrangian 2-faces.
#[test]
fn perturbed_tesseract_has_many_non_lagrangian_two_faces() {
    let hrep = tesseract();
    let outcome = perturb_polytope_normals(&hrep, 42, 1e-2);
    let data = PolytopeData::new(outcome.polytope);
    assert!(
        data.two_faces.len() >= 20,
        "perturbed tesseract should have many non-Lagrangian 2-faces"
    );
}
