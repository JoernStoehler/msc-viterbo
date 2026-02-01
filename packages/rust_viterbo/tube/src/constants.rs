//! Numerical constants and tolerances for the tube algorithm.
//!
//! These tolerances are engineering choices, not mathematically derived.
//! They may need tuning based on empirical testing.

/// General numerical tolerance for floating-point equality checks.
pub const EPS: f64 = 1e-10;

/// Tolerance for Lagrangian 2-face detection (ω(n_i, n_j) ≈ 0).
/// A 2-face is Lagrangian if |ω(n_i, n_j)| < EPS_LAGRANGIAN.
///
/// Re-exported from geom for consistency across all algorithms.
pub use geom::EPS_LAGRANGIAN;

/// Tolerance for unit vector checks (||n|| = 1).
pub const EPS_UNIT: f64 = 1e-9;

/// Tolerance for constraint feasibility checks.
pub const EPS_FEASIBILITY: f64 = 1e-10;

/// Tolerance for vertex deduplication.
pub const EPS_DEDUP: f64 = 1e-8;

/// Tolerance for polygon reconstruction checks.
/// More lenient than EPS because projection to 2D and reconstruction to 4D
/// accumulates numerical error through multiple operations.
pub const EPS_RECONSTRUCTION: f64 = 1e-8;

/// Rotation bound margin for pruning (in turns).
/// Tubes with rotation > 2.0 + EPS_ROTATION are pruned.
pub const EPS_ROTATION: f64 = 0.01;

/// Maximum rotation allowed for valid orbits (in turns).
/// From CH2021 Prop 1.10: action-minimizing orbits have rotation in (1, 2).
pub const MAX_ROTATION: f64 = 2.0;

/// Minimum area threshold for non-empty polygons.
pub const MIN_POLYGON_AREA: f64 = 1e-14;

/// Tolerance for fixed point verification and orbit closure checks.
/// This is more lenient than EPS because numerical errors accumulate
/// along the orbit trajectory. The value 1e-6 allows for ~10^4 accumulated
/// operations at machine precision.
pub const EPS_CLOSURE: f64 = 1e-6;
