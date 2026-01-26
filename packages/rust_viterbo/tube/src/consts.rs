//! Constants and tolerances for the tube algorithm.
//!
//! Tolerance philosophy:
//! - Use relative tolerance where possible
//! - Tight tolerances for input validation
//! - Looser tolerances for derived quantities

use std::f64::consts::PI;

/// General numerical tolerance for floating-point equality.
pub const EPS: f64 = 1e-10;

/// Tolerance for Lagrangian detection: |ω(n_i, n_j)| < EPS_LAGRANGIAN → Lagrangian.
pub const EPS_LAGRANGIAN: f64 = 1e-9;

/// Tolerance for unit vector checks: ||n|| ∈ (1 - EPS_UNIT, 1 + EPS_UNIT).
pub const EPS_UNIT: f64 = 1e-9;

/// Tolerance for constraint feasibility (polygon containment, etc.).
pub const EPS_FEASIBILITY: f64 = 1e-10;

/// Tolerance for vertex deduplication in polygon operations.
pub const EPS_DEDUP: f64 = 1e-8;

/// Rotation pruning margin (in turns). Prune tubes with rotation > 2 + EPS_ROTATION.
pub const EPS_ROTATION: f64 = 0.01;

/// Two-pi constant for rotation calculations.
pub const TAU: f64 = 2.0 * PI;
