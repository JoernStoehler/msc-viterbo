//! Tube algorithm for computing EHZ capacity of convex polytopes.
//!
//! This crate implements the tube algorithm for computing the Ekeland-Hofer-Zehnder
//! capacity of 4D convex polytopes with no Lagrangian 2-faces.
//!
//! # Algorithm Overview
//!
//! The tube algorithm searches over all Reeb trajectories by organizing them into
//! "tubes" — sets of trajectories sharing a combinatorial class (facet sequence).
//! A branch-and-bound search finds the minimum-action closed orbit.
//!
//! # Usage
//!
//! ```rust
//! use tube::{tube_capacity, fixtures::unit_cross_polytope};
//!
//! let hrep = unit_cross_polytope();
//! let result = tube_capacity(&hrep).unwrap();
//! println!("Capacity: {}", result.capacity);
//! ```
//!
//! # Mathematical Background
//!
//! See the thesis (Stöhler 2026) for full mathematical details. Key references:
//! - CH2021: Chaidez-Hutchings, "Computing Reeb Dynamics on Four-Dimensional Convex Polytopes"
//! - HK2017: Haim-Kislev, "On the Symplectic Size of Convex Polytopes"

pub mod algorithm;
pub mod constants;
pub mod fixtures;
pub mod geometry;
pub mod preprocess;
pub mod quaternion;
pub mod trivialization;
pub mod types;

// Re-export main API
pub use algorithm::tube_capacity;
pub use preprocess::{preprocess, PolytopeData};
pub use types::{
    validate_for_tube, AffineFunc, AffineMap2D, ClosedReebOrbit, Polygon2D, PolytopeHRep,
    ThreeFacetData, Tube, TubeError, TubeResult, TwoFaceData, TwoFaceLookup,
};
