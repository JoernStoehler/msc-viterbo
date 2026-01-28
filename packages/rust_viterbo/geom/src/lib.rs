//! Shared geometry types for symplectic capacity algorithms.
//!
//! This crate provides fundamental geometric types used across all
//! symplectic capacity algorithms (HK2017, tube, billiard).
//!
//! # Design Philosophy
//!
//! `geom` provides **clean reference implementations** of symplectic and euclidean
//! geometry in 2D and 4D. Algorithms are expected to:
//!
//! - **Use geom** when the standard implementation fits their needs
//! - **Copy and customize** when algorithm-specific requirements diverge
//!
//! Duplication is acceptable when purposeful. Having clean reference code in `geom`
//! makes algorithm-specific deviations obvious and intentional.
//!
//! # Types
//!
//! - [`PolytopeHRep`]: H-representation of a 4D convex polytope
//!
//! # Numerical Tolerances
//!
//! Tolerances are defined in the [`tolerances`] module with documented justifications.
//!
//! # Volume and Systolic Ratio
//!
//! - [`volume`]: Volume computation using QHull
//! - [`systolic`]: Systolic ratio from capacity and volume

pub mod polytope;
pub mod systolic;
pub mod tolerances;
pub mod volume;

pub use polytope::PolytopeHRep;
pub use tolerances::{EPS, EPS_UNIT};
