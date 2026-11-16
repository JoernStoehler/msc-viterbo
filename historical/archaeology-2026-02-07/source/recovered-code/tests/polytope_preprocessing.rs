//! Tests for PolytopeData construction and preprocessing.
//!
//! PolytopeData filters out Lagrangian 2-faces and computes rotation numbers.

use super::fixtures::tesseract;
use crate::polytope::PolytopeData;
use rust_viterbo_geom::{perturb_polytope_normals, symplectic_form, SymplecticVector};

// ============================================================================
// Tesseract 2-Face Structure Tests (EXPLICIT VERIFICATION)
// ============================================================================

/// Verify omega calculation for tesseract normals with explicit formulas.
///
/// Tesseract normals: ±e1 (±1,0,0,0), ±e2 (0,±1,0,0), ±e3 (0,0,±1,0), ±e4 (0,0,0,±1)
/// With ω = dq1∧dp1 + dq2∧dp2 (coords = q1,q2,p1,p2):
/// - ω(e1, e3) = 1 (q1 with p1)
/// - ω(e2, e4) = 1 (q2 with p2)
/// - All other basis pairs have ω = 0
#[test]
fn tesseract_omega_explicit_values() {
    let e1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
    let e2 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);
    let e3 = SymplecticVector::new(0.0, 0.0, 1.0, 0.0);
    let e4 = SymplecticVector::new(0.0, 0.0, 0.0, 1.0);

    // Non-Lagrangian pairs: q1-p1 and q2-p2 give omega = ±1
    assert!(
        (symplectic_form(e1, e3) - 1.0).abs() < 1e-12,
        "ω(e1, e3) must be 1.0 (q1 with p1)"
    );
    assert!(
        (symplectic_form(e2, e4) - 1.0).abs() < 1e-12,
        "ω(e2, e4) must be 1.0 (q2 with p2)"
    );

    // Lagrangian pairs: same plane (q-q or p-p) or cross (q1-p2, q2-p1) give omega = 0
    assert!(
        symplectic_form(e1, e2).abs() < 1e-12,
        "ω(e1, e2) must be 0 (both in q-space)"
    );
    assert!(
        symplectic_form(e3, e4).abs() < 1e-12,
        "ω(e3, e4) must be 0 (both in p-space)"
    );
    assert!(
        symplectic_form(e1, e4).abs() < 1e-12,
        "ω(e1, e4) must be 0 (q1 with p2 = wrong pair)"
    );
    assert!(
        symplectic_form(e2, e3).abs() < 1e-12,
        "ω(e2, e3) must be 0 (q2 with p1 = wrong pair)"
    );
}

/// Count all 28 tesseract normal pairs and verify Lagrangian/non-Lagrangian split.
///
/// With 8 facets: C(8,2) = 28 pairs total.
/// Non-Lagrangian pairs (ω ≠ 0): 8 pairs
/// - (±e1, ±e3): 4 sign combinations, all have |ω| = 1
/// - (±e2, ±e4): 4 sign combinations, all have |ω| = 1
/// Lagrangian pairs (ω = 0): 20 pairs
#[test]
fn tesseract_all_28_pairs_explicit_count() {
    let hrep = tesseract();
    let n = hrep.normals.len();
    assert_eq!(n, 8, "tesseract must have 8 facets");

    let mut lagrangian_count = 0;
    let mut nonlagrangian_count = 0;

    for i in 0..n {
        for j in (i + 1)..n {
            let omega = symplectic_form(hrep.normals[i], hrep.normals[j]);
            if omega.abs() < 1e-10 {
                lagrangian_count += 1;
            } else {
                nonlagrangian_count += 1;
            }
        }
    }

    assert_eq!(
        lagrangian_count, 20,
        "tesseract must have 20 Lagrangian 2-faces"
    );
    assert_eq!(
        nonlagrangian_count, 8,
        "tesseract must have 8 non-Lagrangian 2-faces"
    );
}

/// Tesseract has exactly 8 non-Lagrangian 2-faces (PolytopeData filters Lagrangian ones).
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
