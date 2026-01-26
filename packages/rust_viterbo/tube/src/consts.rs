//! Numerical constants and tolerances.
//!
//! See spec §1.16 for tolerance philosophy.

/// General numerical tolerance for floating-point comparisons.
pub const EPS: f64 = 1e-10;

/// Threshold for detecting Lagrangian 2-faces (|ω(n_i, n_j)| < EPS_LAGRANGIAN).
pub const EPS_LAGRANGIAN: f64 = 1e-9;

/// Tolerance for ||n|| = 1 check on facet normals.
pub const EPS_UNIT: f64 = 1e-9;

/// Tolerance for constraint satisfaction checks.
pub const EPS_FEASIBILITY: f64 = 1e-10;

/// Rotation pruning margin (turns). Prune tubes with rotation > 2 + EPS_ROTATION.
pub const EPS_ROTATION: f64 = 0.01;
