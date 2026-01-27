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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_tolerance_hierarchy() {
        // Ensure tolerances are ordered as documented
        assert!(EPS < EPS_UNIT, "EPS should be stricter than EPS_UNIT");
    }

    #[test]
    fn test_tolerances_reasonable() {
        // Tolerances should be well above machine epsilon
        let machine_eps = f64::EPSILON;
        assert!(EPS > 1000.0 * machine_eps);
        assert!(EPS_UNIT > 1000.0 * machine_eps);

        // But not so large as to be meaningless
        assert!(EPS < 1e-6);
        assert!(EPS_UNIT < 1e-6);
    }
}
