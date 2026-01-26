//! Tube algorithm for computing EHZ capacity of non-Lagrangian polytopes.
//!
//! This implements the algorithm from Stöhler 2026 (MSc thesis), extending
//! CH2021's mathematical framework with a branch-and-bound search over "tubes"
//! (sets of trajectories sharing a combinatorial facet sequence).
//!
//! # Algorithm Applicability
//!
//! The tube algorithm requires polytopes with **no Lagrangian 2-faces**
//! (i.e., ω(n_i, n_j) ≠ 0 for all adjacent facet pairs).
//!
//! # Usage
//!
//! ```ignore
//! use tube::{PolytopeHRep, tube_capacity};
//!
//! let normals = vec![...];  // unit outward normals
//! let heights = vec![...];  // positive heights (0 in interior)
//! let hrep = PolytopeHRep::new(normals, heights)?;
//!
//! let (capacity, orbit) = tube_capacity(&hrep)?;
//! ```

mod consts;
mod error;
mod geom;
mod polytope;
mod trivialization;
mod tube;
mod algorithm;
#[cfg(test)]
mod debug_transition;

pub use consts::*;
pub use error::{Error, Result};
pub use polytope::{PolytopeHRep, PolytopeData, TwoFace, TwoFaceEnriched, FlowDirection};
pub use tube::{Tube, AffineMap2D, AffineFunc, ClosedReebOrbit};
pub use algorithm::tube_capacity;
