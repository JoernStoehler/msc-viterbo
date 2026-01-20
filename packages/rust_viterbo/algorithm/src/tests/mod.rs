//! Test suite for the capacity algorithm crate.
//!
//! Tests are organized by topic:
//!
//! - `fixtures` - Test polytopes and random generation utilities
//! - `generators` - Sp(4) generators, witness property checkers, proptest strategies
//! - `capacity_known_values` - Literature-verifiable capacity values (tesseract=4, etc.)
//! - `capacity_scaling_axiom` - c(λK) = λ²c(K) tests
//! - `capacity_monotonicity` - K⊆L ⟹ c(K)≤c(L) tests
//! - `capacity_symplectomorphism` - c(AK) = c(K) for A ∈ Sp(4) tests
//! - `algorithm_agreement` - Billiard vs HK2019 agreement
//! - `algorithm_metadata` - Algorithm trait and input validation
//! - `billiard_witness` - Witness orbit geometry and verification
//! - `lagrangian_product` - Product detection and structure
//! - `polygon_2d` - 2D polygon operations
//! - `tube_algorithm` - Tube algorithm (CH2021) tests
//! - `polytope_preprocessing` - PolytopeData construction

pub mod fixtures;
pub mod generators;

mod algorithm_agreement;
mod algorithm_metadata;
mod billiard_witness;
mod capacity_known_values;
mod capacity_monotonicity;
mod capacity_scaling_axiom;
mod capacity_symplectomorphism;
mod lagrangian_product;
mod polygon_2d;
mod polytope_preprocessing;
mod tube_algorithm;
mod tube_rotation_debug;
