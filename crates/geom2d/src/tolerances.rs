//! Numerical tolerances for 2D geometry computations.
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
//! | `EPS_VERTEX` | 1e-9 | Vertex deduplication / coincidence |
//! | `EPS_AREA` | 1e-12 | Area positivity check |
//! | `MAX_COORD` | 1e15 | Maximum coordinate magnitude (avoid overflow) |

/// General tolerance for floating-point comparison.
pub const EPS: f64 = 1e-10;

/// Tolerance for vertex coincidence (are two points the same?).
pub const EPS_VERTEX: f64 = 1e-9;

/// Tolerance for area positivity (is polygon non-degenerate?).
pub const EPS_AREA: f64 = 1e-12;

/// Maximum allowed coordinate magnitude.
///
/// Coordinates beyond this range risk overflow in arithmetic operations
/// (e.g., cross products) and accumulated numerical error. Polytopes should
/// be scaled to use coordinates well within [-MAX_COORD, MAX_COORD].
pub const MAX_COORD: f64 = 1e15;
