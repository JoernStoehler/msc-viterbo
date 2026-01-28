//! Billiard algorithm for computing EHZ capacity of Lagrangian product polytopes.
//!
//! This crate implements the billiard algorithm for computing the
//! Ekeland-Hofer-Zehnder (EHZ) capacity of Lagrangian products K_q × K_p in R⁴,
//! where K_q and K_p are convex 2D polygons.
//!
//! # Algorithm Overview
//!
//! Algorithm specification: see thesis algorithms.tex.
//!
//! Implementation: enumerates 2-bounce and 3-bounce trajectories (Bezdek-Bezdek theorem)
//! and computes action using support functions.
//!
//! # Usage
//!
//! ```
//! use billiard::{billiard_capacity_from_polygons, Polygon2D};
//! use std::f64::consts::PI;
//!
//! // Create a regular pentagon
//! let pentagon = Polygon2D::regular_pentagon();
//! let rotated = pentagon.rotate(PI / 2.0);
//!
//! // Compute capacity
//! let result = billiard_capacity_from_polygons(&pentagon, &rotated).unwrap();
//! println!("Capacity: {}", result.capacity);
//! ```
//!
//! # References
//!
//! - Rudolf 2021: "Minkowski billiards and symplectic capacities" (JMD vol. 17)
//! - Bezdek-Bezdek 2009: "Short billiard trajectories"
//! - HK-O 2024: "A Counterexample to Viterbo's Conjecture" (arXiv:2405.16513)

pub mod action;
pub mod algorithm;
pub mod polygon;
pub mod solve;
pub mod types;

// Re-export main public API
pub use algorithm::{billiard_capacity, billiard_capacity_from_polygons};
pub use types::{
    BilliardError, BilliardResult, BilliardTrajectory, EdgeCombination, LagrangianProduct,
    Polygon2D, CONSTRAINT_TOL, EDGE_PARAM_TOL, EPS, MIN_ACTION,
};
