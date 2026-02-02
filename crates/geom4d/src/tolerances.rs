//! Numerical tolerances for 4D geometry computations.
//!
//! # Design Rationale
//!
//! Floating-point comparisons require tolerances. We define named constants
//! to make the intent clear and allow tuning if needed.
//!
//! # Constants
//!
//! | Constant | Value | Use |
//! |----------|-------|-----|
//! | `EPS` | 1e-10 | General floating-point comparison |
//! | `EPS_UNIT` | 1e-9 | Unit vector validation (‖n‖ ≈ 1) |
//! | `EPS_HEIGHT` | 1e-12 | Height positivity (h > 0) |
//! | `MAX_COORD` | 1e15 | Maximum coordinate magnitude |

/// General tolerance for floating-point comparison.
pub const EPS: f64 = 1e-10;

/// Tolerance for unit vector validation.
pub const EPS_UNIT: f64 = 1e-9;

/// Tolerance for height positivity check.
pub const EPS_HEIGHT: f64 = 1e-12;

/// Maximum allowed coordinate magnitude.
///
/// Coordinates beyond this range risk overflow in arithmetic operations
/// and accumulated numerical error. Polytopes should use coordinates
/// well within [-MAX_COORD, MAX_COORD].
pub const MAX_COORD: f64 = 1e15;
