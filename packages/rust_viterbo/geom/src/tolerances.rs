//! Numerical tolerances for geometric computations.
//!
//! These tolerances are engineering choices based on the following considerations:
//!
//! 1. **Machine precision**: f64 has ~15-16 significant digits (epsilon ≈ 2.2e-16)
//! 2. **Error accumulation**: Operations compound errors; tolerances must account for this
//! 3. **Geometric meaning**: Some tolerances relate to physically meaningful quantities
//!
//! # Tolerance Hierarchy
//!
//! ```text
//! Strictest                                                    Most lenient
//!    |                                                              |
//!    v                                                              v
//! EPS (1e-10)  ---  EPS_UNIT (1e-9)  ---  algorithm-specific tolerances
//! ```
//!
//! Algorithms may define additional tolerances (e.g., for constraint satisfaction,
//! Lagrangian detection) that are calibrated for their specific numerical needs.

/// General numerical tolerance for floating-point equality checks.
///
/// This is the baseline tolerance for comparing two floating-point numbers.
/// It's set to 1e-10, which allows for ~5-6 orders of magnitude of accumulated
/// error from machine epsilon (2.2e-16).
///
/// **Usage**: `(a - b).abs() < EPS` for approximate equality.
pub const EPS: f64 = 1e-10;

/// Tolerance for unit vector checks (||n|| = 1).
///
/// Slightly more lenient than EPS because:
/// - Normal vectors may come from user input
/// - Normalization itself introduces small errors
///
/// **Usage**: `(n.norm() - 1.0).abs() < EPS_UNIT`
pub const EPS_UNIT: f64 = 1e-9;

/// Tolerance for Lagrangian detection.
///
/// A 2-face F_ij is Lagrangian if `|ω(n_i, n_j)| < EPS_LAGRANGIAN`.
/// For Lagrangian 2-faces, the Reeb flow slides along the face rather than crossing it.
///
/// This is the canonical threshold used by all algorithms (hk2017, tube).
/// Algorithms must not define their own Lagrangian thresholds.
///
/// **Thesis reference**: Section 5 (Reeb dynamics), Lemma 3.7 (flow direction).
pub const EPS_LAGRANGIAN: f64 = 1e-9;

// Compile-time checks for tolerance invariants
const _: () = {
    assert!(EPS < EPS_UNIT); // EPS should be stricter than EPS_UNIT
    assert!(EPS < 1e-6); // Not so large as to be meaningless
    assert!(EPS_UNIT < 1e-6);
};

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tolerances_well_above_machine_epsilon() {
        // Tolerances should be well above machine epsilon
        let machine_eps = f64::EPSILON;
        assert!(EPS > 1000.0 * machine_eps);
        assert!(EPS_UNIT > 1000.0 * machine_eps);
    }
}
