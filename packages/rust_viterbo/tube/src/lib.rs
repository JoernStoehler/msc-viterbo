//! Tube algorithm for computing EHZ capacity of convex polytopes.
//!
//! This crate implements the Tube algorithm from Stöhler 2026 thesis for computing
//! the Ekeland-Hofer-Zehnder (EHZ) capacity of convex polytopes in R^4 with **no
//! Lagrangian 2-faces**.
//!
//! # Algorithm Overview
//!
//! The Tube algorithm uses branch-and-bound search over "tubes" — sets of Reeb
//! trajectories sharing a combinatorial class (facet sequence). Key features:
//!
//! - Works on polytopes with NO Lagrangian 2-faces (ω(n_i, n_j) ≠ 0 for all adjacent pairs)
//! - Uses trivialization (CH2021 Def 2.15) to reduce 4D flow to 2D affine maps
//! - Prunes tubes by action lower bound and rotation bound (≤ 2 turns)
//! - Finds closed orbits as fixed points of the composed flow map
//!
//! # Usage
//!
//! ```
//! use tube::{tube_capacity, PolytopeHRep, TubeError};
//!
//! // The cross-polytope has Lagrangian 2-faces, so the tube algorithm rejects it
//! let cross_polytope = tube::fixtures::unit_cross_polytope();
//! let result = tube_capacity(&cross_polytope);
//!
//! // Expect rejection due to Lagrangian 2-faces
//! assert!(matches!(result, Err(TubeError::LagrangianTwoFaces { .. })));
//! ```
//!
//! # Applicability
//!
//! **Requires:** Polytope with NO Lagrangian 2-faces.
//!
//! Use the Billiard algorithm or HK2017 for polytopes with Lagrangian 2-faces.
//!
//! # References
//!
//! - CH2021: Chaidez-Hutchings, "Computing Reeb Dynamics on Four-Dimensional Convex Polytopes"
//! - Stöhler 2026: This thesis (tube algorithm design)

pub mod consts;
pub mod error;
pub mod fixtures;
pub mod geom;
pub mod polytope;
pub mod polygon;
pub mod symplectic;
pub mod trivialization;
pub mod tube;
pub mod algorithm;

// Re-export main public API
pub use algorithm::tube_capacity;
pub use error::TubeError;
pub use polytope::{PolytopeHRep, PolytopeData};
pub use tube::{Tube, ClosedReebOrbit};

#[cfg(test)]
mod integration_tests {
    use super::*;

    #[test]
    fn test_cross_polytope_rejected_for_lagrangian_2faces() {
        // The cross-polytope has Lagrangian 2-faces, so the tube algorithm should reject it.
        // This is a spec finding: the cross-polytope was proposed as a test case assuming
        // it had NO Lagrangian 2-faces, but verification showed it has ~40 Lagrangian pairs.
        let cross = fixtures::unit_cross_polytope();
        let result = tube_capacity(&cross);

        assert!(matches!(result, Err(TubeError::LagrangianTwoFaces { .. })),
            "Expected LagrangianTwoFaces error, got {:?}", result);
    }
}
