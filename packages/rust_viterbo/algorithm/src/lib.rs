//! EHZ capacity algorithms for convex polytopes in ℝ⁴.
//!
//! This crate implements multiple algorithms for computing the Ekeland-Hofer-Zehnder
//! capacity of a 4-dimensional convex polytope:
//!
//! - **Tube (CH2021)**: Branch-and-bound search over tube compositions
//! - **HK2019**: Quadratic programming over permutations (Haim-Kislev)
//! - **Minkowski Billiard**: Billiard dynamics for Lagrangian products
//!
//! # Architecture
//!
//! The tube algorithm reduces 4D flow maps to 2D affine algebra via trivialization.
//! Key modules:
//!
//! - `affine`: 2D affine maps and functions for tube composition
//! - `polygon`: Convex 2D polygon operations for feasible region tracking
//! - `polytope`: Preprocessed polytope data (non-Lagrangian 2-faces)
//! - `tube`: Tube data structure and extension operations
//! - `result`: Output types (WitnessOrbit, Diagnostics, CapacityResult)
//! - `compute`: Main algorithm and trait abstraction
//! - `billiard`: Minkowski billiard for Lagrangian products
//! - `hk2019`: HK2019 quadratic programming algorithm
//!
//! # References
//!
//! - [algorithm-spec.md](../docs/algorithm-spec.md) - Implementation details
//! - [tube-geometry-spec.md](../docs/tube-geometry-spec.md) - Flow map derivation
//! - Rudolf (2022): Minkowski billiard characterization
//! - Haim-Kislev (2019): QP formulation
//! - Thesis §4 - Mathematical background

pub mod affine;
pub mod billiard;
pub mod billiard_lp;
pub mod compute;
pub mod hk2019;
pub mod polygon;
pub mod polytope;
pub mod result;
pub mod tube;

// Re-export main API
pub use compute::{
    all_algorithms, compute_capacity, AlgorithmMetadata, CapacityAlgorithm, HK2019Algorithm,
    MinkowskiBilliardAlgorithm, TubeAlgorithm,
};
pub use result::{AlgorithmError, CapacityResult, Diagnostics, WitnessOrbit, WitnessVerification};

// Re-export commonly used types for internal use
pub use affine::{AffineFunc, AffineMap2D};
pub use polygon::Polygon2D;
pub use polytope::{FlowDir, PolytopeData, TwoFaceData, EPS_DEDUP, EPS_FEAS, EPS_LAGR};
pub use tube::{ExtensionResult, Tube};

#[cfg(test)]
mod tests;
