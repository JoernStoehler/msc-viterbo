//! Tube algorithm for computing EHZ capacity of convex polytopes.
//!
//! This crate implements the tube algorithm from the thesis (Stöhler 2026),
//! building on CH2021's mathematical framework for Reeb dynamics on polytopes.
//!
//! The algorithm applies to polytopes with **no Lagrangian 2-faces**.

mod geom;
mod polytope;
mod trivialization;
mod tube;

pub use geom::{AffineFunc, AffineMap2D, Polygon2D};
pub use polytope::{PolytopeData, PolytopeHRep, TwoFace, TwoFaceEnriched};
pub use tube::{tube_capacity, ClosedReebOrbit, Tube, TubeError};

/// Numerical tolerance constants.
pub mod tol {
    pub const EPS: f64 = 1e-10;
    pub const EPS_LAGRANGIAN: f64 = 1e-9;
    pub const EPS_UNIT: f64 = 1e-9;
    pub const EPS_FEASIBILITY: f64 = 1e-10;
    pub const EPS_DEDUP: f64 = 1e-8;
    pub const EPS_ROTATION: f64 = 0.01;
}
