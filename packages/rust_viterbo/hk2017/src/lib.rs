//! HK2017 algorithm for computing EHZ capacity of convex polytopes.
//!
//! This crate implements the algorithm from Haim-Kislev's 2017 paper
//! "On the Symplectic Size of Convex Polytopes" for computing the
//! Ekeland-Hofer-Zehnder (EHZ) capacity of convex polytopes in R^4.
//!
//! # Algorithm Overview
//!
//! The HK2017 algorithm computes capacity using the formula:
//!
//! ```text
//! c_EHZ(K) = (1/2) * [max_{sigma, beta} Q(sigma, beta)]^{-1}
//! ```
//!
//! where:
//! - sigma is a permutation of facets (the order the orbit visits them)
//! - beta are non-negative coefficients satisfying closure and height constraints
//! - Q is a quadratic form involving the symplectic form of facet normals
//!
//! # Usage
//!
//! ```
//! use hk2017::{hk2017_capacity, Hk2017Config, PolytopeHRep};
//! use nalgebra::Vector4;
//!
//! // Create a tesseract [-1, 1]^4
//! let normals = vec![
//!     Vector4::new( 1.0,  0.0,  0.0,  0.0),
//!     Vector4::new(-1.0,  0.0,  0.0,  0.0),
//!     Vector4::new( 0.0,  1.0,  0.0,  0.0),
//!     Vector4::new( 0.0, -1.0,  0.0,  0.0),
//!     Vector4::new( 0.0,  0.0,  1.0,  0.0),
//!     Vector4::new( 0.0,  0.0, -1.0,  0.0),
//!     Vector4::new( 0.0,  0.0,  0.0,  1.0),
//!     Vector4::new( 0.0,  0.0,  0.0, -1.0),
//! ];
//! let heights = vec![1.0; 8];
//! let polytope = PolytopeHRep::new(normals, heights);
//!
//! let result = hk2017_capacity(&polytope, &Hk2017Config::default()).unwrap();
//! assert!((result.capacity - 4.0).abs() < 1e-6);
//! ```
//!
//! # Enumeration Strategies
//!
//! Two enumeration strategies are available:
//!
//! - **Naive**: Enumerate all subset permutations. Complexity O(F!) where F is
//!   the number of facets. Guaranteed to find the global optimum.
//!
//! - **Graph-pruned**: Build a facet transition graph and enumerate only valid
//!   cycles. Much faster for polytopes with sparse transition graphs.
//!
//! ```
//! use hk2017::{hk2017_capacity, Hk2017Config, PolytopeHRep, EnumerationStrategy};
//! # use nalgebra::Vector4;
//! # let normals = vec![
//! #     Vector4::new( 1.0,  0.0,  0.0,  0.0),
//! #     Vector4::new(-1.0,  0.0,  0.0,  0.0),
//! #     Vector4::new( 0.0,  1.0,  0.0,  0.0),
//! #     Vector4::new( 0.0, -1.0,  0.0,  0.0),
//! #     Vector4::new( 0.0,  0.0,  1.0,  0.0),
//! #     Vector4::new( 0.0,  0.0, -1.0,  0.0),
//! #     Vector4::new( 0.0,  0.0,  0.0,  1.0),
//! #     Vector4::new( 0.0,  0.0,  0.0, -1.0),
//! # ];
//! # let heights = vec![1.0; 8];
//! # let polytope = PolytopeHRep::new(normals, heights);
//!
//! // Graph-pruned enumeration may be faster for some polytopes,
//! // but doesn't work for all (see crate documentation).
//! // For reliable results, use naive enumeration:
//! let config = Hk2017Config::naive();
//! let result = hk2017_capacity(&polytope, &config).unwrap();
//! ```
//!
//! # Correctness of Interior-Only Search
//!
//! For each (subset S, permutation sigma), the KKT solver finds the unique
//! critical point of Q on the affine subspace defined by the equality
//! constraints. We then check if all beta_i > 0; if not, we reject this
//! (S, sigma) pair.
//!
//! One might worry: what if the true maximum of Q over the feasible region
//! M(S) = {beta : constraints, beta >= 0} occurs on the boundary (some
//! beta_i = 0) rather than at the interior critical point?
//!
//! **This is not a problem.** If beta* in M(S) has beta*_j = 0 for some j,
//! then:
//! - The constraints remain satisfied after dropping facet j (zero terms).
//! - The Q value is unchanged (terms with beta_j = 0 contribute nothing).
//! - Thus beta* corresponds to an interior point in M(S') where S' = S \ {j}.
//!
//! By searching over all subsets S, we cover all boundary cases via smaller
//! subsets. Therefore the global maximum is achieved at an interior point
//! of some (S*, sigma*), and the algorithm correctly finds it.
//!
//! **Proof reference:** See thesis Section 3.3 (Algorithm of Haim-Kislev 2017),
//! specifically Lemma `lem:hk-boundary` (Boundary Reduction) and Corollary
//! `cor:hk-interior-correct` (Correctness of Interior-Only Search).
//!
//! ## Historical note
//!
//! The MATLAB reference implementation uses the same interior-only approach
//! but does not document why it is correct. The correctness argument above
//! was formalized as part of this thesis.
//!
//! # References
//!
//! - Haim-Kislev, P. "On the Symplectic Size of Convex Polytopes."
//!   *Geometric and Functional Analysis* 29 (2019): 440-463.
//!   arXiv:1712.03494 (December 2017).
//!
//! - Reference implementation: <https://github.com/pazithaimkislev/EHZ-capacity>

pub mod algorithm;
pub mod enumerate;
pub mod preprocess;
pub mod solve;
pub mod symplectic;
pub mod types;
pub mod verify;

// Re-export main public API
pub use algorithm::hk2017_capacity;
pub use symplectic::{apply_j, j_matrix, reeb_vector, symplectic_form};
pub use types::{
    validate_for_hk2017, EnumerationStrategy, FacetData, Hk2017Config, Hk2017Error, Hk2017Result,
    PolytopeHRep, RejectionHistogram, RejectionReason, CONSTRAINT_TOL, EPS, LAGRANGIAN_TOL,
    POSITIVE_TOL,
};
pub use verify::{verify_results_equivalent, VerificationDetails, VerificationError};

/// Integration tests for the HK2017 algorithm.
///
/// These tests verify output correctness and are marked with
/// `#[cfg_attr(debug_assertions, ignore)]` to run only in release mode.
/// They perform expensive capacity computations that are ~10x faster in release.
#[cfg(test)]
mod integration_tests {
    use super::*;
    use approx::assert_relative_eq;
    use nalgebra::Vector4;

    /// Helper to create a tesseract [-1, 1]^4.
    fn make_tesseract() -> PolytopeHRep {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(0.0, 0.0, 0.0, -1.0),
        ];
        let heights = vec![1.0; 8];
        PolytopeHRep::new(normals, heights)
    }

    #[cfg_attr(debug_assertions, ignore)]
    #[test]
    fn test_full_pipeline_tesseract() {
        let polytope = make_tesseract();
        let config = Hk2017Config::default();

        let result = hk2017_capacity(&polytope, &config).unwrap();

        // Ground truth: tesseract capacity = 4.0
        assert_relative_eq!(result.capacity, 4.0, epsilon = 1e-6);

        // Verify the result passes all checks
        let facet_data = FacetData::from_polytope(&polytope).unwrap();
        assert!(result.verify_checked(&facet_data).is_ok());
    }

    #[cfg_attr(debug_assertions, ignore)]
    #[test]
    fn test_enumeration_strategies_agree() {
        let polytope = make_tesseract();

        let result_naive = hk2017_capacity(&polytope, &Hk2017Config::naive()).unwrap();
        let result_graph = hk2017_capacity(&polytope, &Hk2017Config::graph_pruned()).unwrap();

        assert!(verify_results_equivalent(&result_naive, &result_graph, 1e-10).is_ok());
    }

    #[cfg_attr(debug_assertions, ignore)]
    #[test]
    fn test_scaling_axiom() {
        let polytope = make_tesseract();
        let config = Hk2017Config::default();

        let c_base = hk2017_capacity(&polytope, &config).unwrap().capacity;

        // Scale by lambda
        for lambda in [0.5, 2.0, 3.0] {
            let scaled_heights: Vec<f64> = polytope.heights.iter().map(|h| h * lambda).collect();
            let scaled_polytope = PolytopeHRep::new(polytope.normals.clone(), scaled_heights);

            let c_scaled = hk2017_capacity(&scaled_polytope, &config).unwrap().capacity;

            // c(lambda * K) = lambda^2 * c(K)
            assert_relative_eq!(
                c_scaled,
                lambda * lambda * c_base,
                epsilon = 1e-6,
                max_relative = 1e-6
            );
        }
    }

    #[cfg_attr(debug_assertions, ignore)]
    #[test]
    fn test_capacity_positive() {
        let polytope = make_tesseract();
        let result = hk2017_capacity(&polytope, &Hk2017Config::default()).unwrap();

        assert!(result.capacity > 0.0);
        assert!(result.q_max > 0.0);
    }
}
