//! Tests for the LP-based boundedness check.

use super::*;

// ==================== FIXTURE HELPERS ====================

/// Tesseract (hypercube) normals: ±eᵢ for i = 0..4
pub(crate) fn tesseract_normals() -> Vec<Vector4<f64>> {
    vec![
        Vector4::new(1.0, 0.0, 0.0, 0.0),
        Vector4::new(-1.0, 0.0, 0.0, 0.0),
        Vector4::new(0.0, 1.0, 0.0, 0.0),
        Vector4::new(0.0, -1.0, 0.0, 0.0),
        Vector4::new(0.0, 0.0, 1.0, 0.0),
        Vector4::new(0.0, 0.0, -1.0, 0.0),
        Vector4::new(0.0, 0.0, 0.0, 1.0),
        Vector4::new(0.0, 0.0, 0.0, -1.0),
    ]
}

/// Cross-polytope normals: all (±1, ±1, ±1, ±1)/2
pub(crate) fn cross_polytope_normals() -> Vec<Vector4<f64>> {
    let mut normals = Vec::with_capacity(16);
    for s1 in [-1.0, 1.0] {
        for s2 in [-1.0, 1.0] {
            for s3 in [-1.0, 1.0] {
                for s4 in [-1.0, 1.0] {
                    normals.push(Vector4::new(s1, s2, s3, s4).normalize());
                }
            }
        }
    }
    normals
}

/// Minimal bounded configuration: simplex-like (5 normals)
pub(crate) fn simplex_like_normals() -> Vec<Vector4<f64>> {
    vec![
        Vector4::new(1.0, 0.0, 0.0, 0.0),
        Vector4::new(0.0, 1.0, 0.0, 0.0),
        Vector4::new(0.0, 0.0, 1.0, 0.0),
        Vector4::new(0.0, 0.0, 0.0, 1.0),
        Vector4::new(-1.0, -1.0, -1.0, -1.0).normalize(),
    ]
}

// ==================== POSITIVE TESTS (BOUNDED) ====================

#[test]
fn test_is_bounded_tesseract() {
    assert!(is_bounded(&tesseract_normals()), "tesseract should be bounded");
}

#[test]
fn test_is_bounded_cross_polytope() {
    assert!(
        is_bounded(&cross_polytope_normals()),
        "cross-polytope should be bounded"
    );
}

#[test]
fn test_is_bounded_simplex_like() {
    assert!(
        is_bounded(&simplex_like_normals()),
        "simplex-like polytope should be bounded"
    );
}

#[test]
fn test_is_bounded_perturbed_cross_polytope() {
    for seed in 0..5 {
        let offset = seed as f64 * 0.01;
        let mut normals = Vec::with_capacity(16);

        for s1 in [-1.0, 1.0] {
            for s2 in [-1.0, 1.0] {
                for s3 in [-1.0, 1.0] {
                    for s4 in [-1.0, 1.0] {
                        let n = Vector4::new(
                            s1 + offset * 0.1,
                            s2 + offset * 0.2,
                            s3 + offset * 0.3,
                            s4 + offset * 0.4,
                        )
                        .normalize();
                        normals.push(n);
                    }
                }
            }
        }

        assert!(
            is_bounded(&normals),
            "perturbed cross-polytope (seed {}) should be bounded",
            seed
        );
    }
}

// ==================== NEGATIVE TESTS (UNBOUNDED) ====================

#[test]
fn test_is_bounded_positive_orthant_unbounded() {
    let normals = vec![
        Vector4::new(1.0, 0.0, 0.0, 0.0),
        Vector4::new(0.0, 1.0, 0.0, 0.0),
        Vector4::new(0.0, 0.0, 1.0, 0.0),
        Vector4::new(0.0, 0.0, 0.0, 1.0),
        Vector4::new(1.0, 1.0, 0.0, 0.0).normalize(),
    ];

    assert!(!is_bounded(&normals), "positive orthant should be unbounded");
}

#[test]
fn test_is_bounded_half_space_unbounded() {
    let normals = vec![
        Vector4::new(1.0, 0.0, 0.0, 0.0),
        Vector4::new(0.6, 0.8, 0.0, 0.0).normalize(),
        Vector4::new(0.6, 0.0, 0.8, 0.0).normalize(),
        Vector4::new(0.6, 0.0, 0.0, 0.8).normalize(),
        Vector4::new(0.5, 0.5, 0.5, 0.5).normalize(),
    ];

    assert!(
        normals.iter().all(|n| n[0] > 0.0),
        "test setup: all normals should have positive x₁"
    );

    assert!(
        !is_bounded(&normals),
        "half-space configuration should be unbounded"
    );
}

#[test]
fn test_is_bounded_tesseract_missing_facet_unbounded() {
    let normals = vec![
        Vector4::new(-1.0, 0.0, 0.0, 0.0),
        Vector4::new(0.0, 1.0, 0.0, 0.0),
        Vector4::new(0.0, -1.0, 0.0, 0.0),
        Vector4::new(0.0, 0.0, 1.0, 0.0),
        Vector4::new(0.0, 0.0, -1.0, 0.0),
        Vector4::new(0.0, 0.0, 0.0, 1.0),
        Vector4::new(0.0, 0.0, 0.0, -1.0),
    ];

    assert!(
        !is_bounded(&normals),
        "tesseract with missing +e₁ facet should be unbounded"
    );
}

#[test]
fn test_is_bounded_counterexample_axis_check_insufficient() {
    let normals = vec![
        Vector4::new(1.0, -1.0, -1.0, -1.0).normalize(),
        Vector4::new(-1.0, 1.0, -1.0, -1.0).normalize(),
        Vector4::new(-1.0, -1.0, 1.0, -1.0).normalize(),
        Vector4::new(-1.0, -1.0, -1.0, 1.0).normalize(),
        Vector4::new(-1.0, -1.0, -1.0, -1.0).normalize(),
    ];

    for axis in 0..4 {
        assert!(normals.iter().any(|n| n[axis] > 0.1));
        assert!(normals.iter().any(|n| n[axis] < -0.1));
    }

    let v = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
    for n in &normals {
        assert!(n.dot(&v) < -0.1);
    }

    assert!(
        !is_bounded(&normals),
        "normals cover all axes but polytope is unbounded in (1,1,1,1) direction"
    );
}

// ==================== EDGE CASES ====================

#[test]
fn test_is_bounded_barely_bounded() {
    let eps = 0.001;
    let normals = vec![
        Vector4::new(1.0, eps, eps, eps).normalize(),
        Vector4::new(-1.0, eps, eps, eps).normalize(),
        Vector4::new(eps, 1.0, eps, eps).normalize(),
        Vector4::new(eps, -1.0, eps, eps).normalize(),
        Vector4::new(eps, eps, 1.0, eps).normalize(),
        Vector4::new(eps, eps, -1.0, eps).normalize(),
        Vector4::new(eps, eps, eps, 1.0).normalize(),
        Vector4::new(eps, eps, eps, -1.0).normalize(),
    ];

    assert!(
        is_bounded(&normals),
        "barely-covering normals should still be bounded"
    );
}

#[path = "bounded_crosscheck_tests.rs"]
mod crosscheck;
