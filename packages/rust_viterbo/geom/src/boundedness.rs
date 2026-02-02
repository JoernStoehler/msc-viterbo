//! Check if an H-representation defines a bounded polytope.
//!
//! # Mathematical Background
//!
//! An H-rep K = intersection{x : <n_i, x> <= h_i} is bounded if and only if the normals
//! {n_1, ..., n_k} **positively span** R^4. This means:
//!
//! - For every direction d in R^4 \ {0}, there exists some n_i with <n_i, d> > 0
//! - Equivalently: no direction d has <n_i, d> <= 0 for all i
//! - Equivalently: the origin lies in the interior of conv{n_1, ..., n_k}
//!
//! # LP Formulation
//!
//! To check if the polytope is bounded, we check whether there exists a "recession direction"
//! d such that <n_i, d> <= 0 for all i (with d != 0). If such a direction exists, the polytope
//! is unbounded along d.
//!
//! We formulate this as an LP feasibility check:
//!
//! **Find d such that:** <n_i, d> <= -1 for all i
//!
//! If feasible: there exists a direction d with all dot products strictly negative,
//!              so d (or any positive scaling of it) is a recession direction.
//!              The polytope is **unbounded**.
//!
//! If infeasible: no such d exists. Combined with the fact that d = 0 is the only
//!                solution to <n_i, d> <= 0 for all i, this means the normals
//!                positively span R^4. The polytope is **bounded**.
//!
//! The constraint <n_i, d> <= -1 (rather than <= 0) ensures we find a non-zero d
//! while keeping the LP bounded.

use minilp::{ComparisonOp, OptimizationDirection, Problem};
use nalgebra::Vector4;

use crate::tolerances::EPS_UNIT;

/// Check if an H-representation defines a bounded polytope.
///
/// # Mathematical Background
///
/// An H-rep K = intersection{x : <n_i, x> <= h_i} is bounded iff the normals
/// {n_1, ..., n_k} **positively span** R^4.
///
/// # Implementation
///
/// Uses linear programming to check if there exists a recession direction d with
/// <n_i, d> <= -1 for all i. If such d exists, the polytope is unbounded.
/// If the LP is infeasible, the polytope is bounded.
///
/// # Preconditions (debug_assert)
///
/// - All normals must be unit vectors (|n_i| approx 1.0)
/// - At least 5 normals (minimum for a 4D polytope with interior)
///
/// # Arguments
///
/// * `normals` - Slice of 4D unit normal vectors
///
/// # Returns
///
/// `true` if the normals positively span R^4 (polytope is bounded),
/// `false` otherwise.
pub fn is_bounded(normals: &[Vector4<f64>]) -> bool {
    // Precondition: at least 5 normals for a 4D polytope
    debug_assert!(
        normals.len() >= 5,
        "is_bounded: need at least 5 normals for a 4D polytope, got {}",
        normals.len()
    );

    // Precondition: all normals must be unit vectors
    debug_assert!(
        normals.iter().all(|n| (n.norm() - 1.0).abs() < EPS_UNIT),
        "is_bounded: all normals must be unit vectors"
    );

    // LP formulation:
    // Check if there exists d with <n_i, d> <= -1 for all i.
    // If yes -> unbounded (return false)
    // If no (infeasible) -> bounded (return true)

    let mut problem = Problem::new(OptimizationDirection::Minimize);

    // Variables: d[0], d[1], d[2], d[3] (components of the direction vector)
    // We use a large but finite bound; the LP will be infeasible if bounded.
    let bound = 1e10;
    let d: Vec<_> = (0..4)
        .map(|_| problem.add_var(0.0, (-bound, bound)))
        .collect();

    // Constraints: <n_i, d> <= -1 for all i
    // This is: n[0]*d[0] + n[1]*d[1] + n[2]*d[2] + n[3]*d[3] <= -1
    for n in normals {
        problem.add_constraint(
            &[(d[0], n[0]), (d[1], n[1]), (d[2], n[2]), (d[3], n[3])],
            ComparisonOp::Le,
            -1.0,
        );
    }

    match problem.solve() {
        Ok(_) => false, // Feasible -> recession direction exists -> unbounded
        Err(_) => true, // Infeasible -> no recession direction -> bounded
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use nalgebra::Vector4;

    use crate::tolerances::EPS;

    /// Helper: generate cross-polytope normals (16 normals of form (+/-1,+/-1,+/-1,+/-1)/2).
    fn cross_polytope_normals() -> Vec<Vector4<f64>> {
        let mut normals = Vec::new();
        for s1 in [-1.0, 1.0] {
            for s2 in [-1.0, 1.0] {
                for s3 in [-1.0, 1.0] {
                    for s4 in [-1.0, 1.0] {
                        normals.push(Vector4::new(s1, s2, s3, s4) / 2.0);
                    }
                }
            }
        }
        normals
    }

    /// Helper: generate tesseract (hypercube) normals (+/- e_i for i=0..4).
    fn tesseract_normals() -> Vec<Vector4<f64>> {
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

    #[test]
    fn test_is_bounded_cross_polytope() {
        // Cross-polytope normals: all (+/-1,+/-1,+/-1,+/-1)/2
        // These positively span R^4, so the polytope is bounded.
        let normals = cross_polytope_normals();
        assert!(
            is_bounded(&normals),
            "Cross-polytope normals should define a bounded polytope"
        );
    }

    #[test]
    fn test_is_bounded_tesseract() {
        // Tesseract (hypercube) normals: +/- e_i
        // These positively span R^4, so the polytope is bounded.
        let normals = tesseract_normals();
        assert!(
            is_bounded(&normals),
            "Tesseract normals should define a bounded polytope"
        );
    }

    #[test]
    fn test_is_bounded_positive_quadrant_unbounded() {
        // Axis-aligned positive quadrant: normals are +e_1, +e_2, +e_3, +e_4, and one more
        // This defines the positive orthant { x : x_i <= h_i }, which is unbounded
        // in the -e_1, -e_2, -e_3, -e_4 directions.
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            // Add one more to satisfy the >= 5 precondition
            Vector4::new(1.0, 1.0, 0.0, 0.0).normalize(),
        ];

        assert!(
            !is_bounded(&normals),
            "Positive quadrant normals should be unbounded (no coverage for -e_i directions)"
        );
    }

    #[test]
    fn test_is_bounded_all_positive_first_component() {
        // All normals have positive first component (n[0] > 0).
        // This is unbounded in the -e_1 direction.
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.5, 0.5, 0.5, 0.5).normalize(),
            Vector4::new(0.3, 0.6, 0.5, 0.4).normalize(),
            Vector4::new(0.2, -0.5, 0.6, -0.3).normalize(),
            Vector4::new(0.4, 0.3, -0.7, 0.2).normalize(),
            Vector4::new(0.1, 0.2, 0.3, -0.9).normalize(),
        ];

        // Verify all normals have positive first component
        assert!(
            normals.iter().all(|n| n[0] > 0.0),
            "Test setup: all normals should have positive first component"
        );

        assert!(
            !is_bounded(&normals),
            "Normals with all-positive first component should be unbounded in -e_1 direction"
        );
    }

    #[test]
    fn test_is_bounded_half_space() {
        // A half-space is unbounded: normals all pointing in +x_1 direction
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),             // +e_1
            Vector4::new(0.6, 0.8, 0.0, 0.0).normalize(), // positive x_1
            Vector4::new(0.6, 0.0, 0.8, 0.0).normalize(), // positive x_1
            Vector4::new(0.6, 0.0, 0.0, 0.8).normalize(), // positive x_1
            Vector4::new(0.5, 0.5, 0.5, 0.5).normalize(), // positive x_1
        ];

        // All normals have positive first component
        assert!(
            normals.iter().all(|n| n[0] > 0.0),
            "Test setup: all normals should have positive first component"
        );

        // Therefore unbounded in -e_1 direction
        assert!(
            !is_bounded(&normals),
            "Normals all pointing in +x_1 half-space should be unbounded in -x_1"
        );
    }

    #[test]
    fn test_is_bounded_barely_bounded() {
        // Normals that barely cover all axis directions.
        // Each axis direction +/- e_i has exactly one normal with positive dot product.
        let eps = 0.001;
        let normals = vec![
            // These cover +e_1 and -e_1
            Vector4::new(1.0, eps, eps, eps).normalize(),
            Vector4::new(-1.0, eps, eps, eps).normalize(),
            // These cover +e_2 and -e_2
            Vector4::new(eps, 1.0, eps, eps).normalize(),
            Vector4::new(eps, -1.0, eps, eps).normalize(),
            // These cover +e_3 and -e_3
            Vector4::new(eps, eps, 1.0, eps).normalize(),
            Vector4::new(eps, eps, -1.0, eps).normalize(),
            // These cover +e_4 and -e_4
            Vector4::new(eps, eps, eps, 1.0).normalize(),
            Vector4::new(eps, eps, eps, -1.0).normalize(),
        ];

        assert!(
            is_bounded(&normals),
            "Normals covering all 8 axis directions with opposite pairs should be bounded"
        );
    }

    /// CRITICAL TEST: The counterexample that proves the axis-only check is insufficient.
    ///
    /// These normals:
    /// - Cover all 8 axis directions (+/- e_i)
    /// - But do NOT positively span R^4
    /// - The polytope is unbounded in direction (1,1,1,1)/2
    ///
    /// The old broken implementation would return TRUE for these.
    /// The correct implementation must return FALSE.
    #[test]
    fn test_is_bounded_counterexample_axis_check_insufficient() {
        // Direction we want to be uncovered: v = (1,1,1,1)/2
        // All normals have <n, v> <= 0, meaning the polytope is unbounded in direction v.
        //
        // Construction: Use normals of form (a, b, c, d) where a+b+c+d <= 0
        // but still cover all axis directions.

        let normals = vec![
            // Normal 1: covers +e_1 (has positive first component)
            // Sum = 1-1-1-1 = -2 < 0, so <n, v> < 0
            Vector4::new(1.0, -1.0, -1.0, -1.0).normalize(),
            // Normal 2: covers +e_2
            Vector4::new(-1.0, 1.0, -1.0, -1.0).normalize(),
            // Normal 3: covers +e_3
            Vector4::new(-1.0, -1.0, 1.0, -1.0).normalize(),
            // Normal 4: covers +e_4
            Vector4::new(-1.0, -1.0, -1.0, 1.0).normalize(),
            // Normal 5: covers all -e_j directions
            // n = (-1, -1, -1, -1)/2, sum = -4 < 0
            Vector4::new(-1.0, -1.0, -1.0, -1.0).normalize(),
        ];

        // Verify precondition: all unit vectors
        for n in &normals {
            let norm: f64 = n.norm();
            assert!((norm - 1.0).abs() < 1e-10, "Normal should be unit vector");
        }

        // Verify: all normals have <n, v> <= 0 where v = (1,1,1,1)/2
        let v = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        for (i, n) in normals.iter().enumerate() {
            let dot = n.dot(&v);
            assert!(
                dot <= EPS,
                "Normal {} should have non-positive dot with v, got {}",
                i,
                dot
            );
        }

        // Verify: each axis direction is covered
        for axis in 0..4 {
            // Check +e_axis
            let has_positive = normals.iter().any(|n| n[axis] > 0.0);
            assert!(has_positive, "Should cover +e{} axis direction", axis + 1);

            // Check -e_axis
            let has_negative = normals.iter().any(|n| n[axis] < 0.0);
            assert!(has_negative, "Should cover -e{} axis direction", axis + 1);
        }

        // The normals DON'T positively span R^4!
        // Direction v = (1,1,1,1)/2 has <n_i, v> <= 0 for all normals.
        // This means the polytope is unbounded in direction v.
        //
        // The correct implementation MUST return false.
        assert!(
            !is_bounded(&normals),
            "Counterexample normals pass axis check but don't positively span R^4. \
             Direction v = (1,1,1,1)/2 has <n_i, v> <= 0 for all normals, \
             proving the polytope is unbounded in direction v."
        );
    }

    /// Test with a simplex (5 facets in general position).
    #[test]
    fn test_is_bounded_simplex() {
        // Regular 4-simplex: 5 facets, each normal points away from opposite vertex
        // The normals positively span R^4.
        //
        // Use vertices at (1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1), and (-1,-1,-1,-1)/sqrt(4)
        // Actually, for simplicity, use a slightly perturbed simplex.

        // 4-simplex with centroid at origin has normals pointing to vertices
        // of the dual (with appropriate scaling)
        let c = 1.0 / 5.0_f64.sqrt();
        let normals = vec![
            Vector4::new(1.0, c, c, c).normalize(),
            Vector4::new(c, 1.0, c, c).normalize(),
            Vector4::new(c, c, 1.0, c).normalize(),
            Vector4::new(c, c, c, 1.0).normalize(),
            Vector4::new(-1.0, -1.0, -1.0, -1.0).normalize(),
        ];

        assert!(
            is_bounded(&normals),
            "Simplex normals should define a bounded polytope"
        );
    }

    /// Property-based test: random bounded polytopes (cross-polytope like)
    /// should be detected as bounded.
    #[test]
    fn test_random_bounded_polytopes() {
        // Generate several cross-polytope-like configurations
        // (all sign combinations) which are guaranteed to be bounded
        for seed in 0..5 {
            let offset = seed as f64 * 0.1;
            let mut normals = Vec::new();

            for s1 in [-1.0, 1.0] {
                for s2 in [-1.0, 1.0] {
                    for s3 in [-1.0, 1.0] {
                        for s4 in [-1.0, 1.0] {
                            let n = Vector4::new(
                                s1 + offset * 0.01,
                                s2 + offset * 0.02,
                                s3 + offset * 0.03,
                                s4 + offset * 0.04,
                            )
                            .normalize();
                            normals.push(n);
                        }
                    }
                }
            }

            assert!(
                is_bounded(&normals),
                "Cross-polytope-like configuration (seed {}) should be bounded",
                seed
            );
        }
    }

    /// Test that removing one facet from tesseract makes it unbounded.
    #[test]
    fn test_tesseract_missing_facet_unbounded() {
        // Tesseract with +e_1 facet removed is unbounded in -e_1 direction
        let normals = vec![
            // Vector4::new(1.0, 0.0, 0.0, 0.0),  // REMOVED
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
            "Tesseract with missing +e_1 facet should be unbounded"
        );
    }
}
