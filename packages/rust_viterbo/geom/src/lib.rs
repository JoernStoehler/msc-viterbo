//! Shared geometry types for symplectic capacity algorithms.
//!
//! This crate provides fundamental geometric types used across all
//! symplectic capacity algorithms (HK2017, tube, billiard).
//!
//! # Types
//!
//! - [`PolytopeHRep`]: H-representation of a 4D convex polytope
//!
//! # Numerical Tolerances
//!
//! Tolerances are defined in the [`tolerances`] module with documented justifications.

pub mod polytope;
pub mod tolerances;

pub use polytope::PolytopeHRep;
pub use tolerances::{EPS, EPS_UNIT};
