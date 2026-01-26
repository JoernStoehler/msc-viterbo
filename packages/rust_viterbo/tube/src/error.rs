//! Error types for the tube algorithm.

use thiserror::Error;

/// Errors that can occur during tube algorithm execution.
#[derive(Debug, Error)]
pub enum TubeError {
    /// The input polytope is invalid.
    #[error("Invalid polytope: {0}")]
    InvalidPolytope(String),

    /// The polytope has Lagrangian 2-faces, making the tube algorithm inapplicable.
    /// (The tube algorithm requires NO Lagrangian 2-faces.)
    #[error("Polytope has {count} Lagrangian 2-faces at indices {indices:?}. Tube algorithm requires NO Lagrangian 2-faces.")]
    LagrangianTwoFaces {
        /// Number of Lagrangian 2-faces.
        count: usize,
        /// Indices of Lagrangian 2-faces (as (i, j) pairs).
        indices: Vec<(usize, usize)>,
    },

    /// No closed orbit was found (all tubes pruned).
    #[error("No closed orbit found after exploring {tubes_explored} tubes")]
    NoClosedOrbitFound {
        /// Number of tubes explored before giving up.
        tubes_explored: usize,
    },

    /// Numerical instability detected (e.g., near-singular matrix).
    #[error("Numerical instability: {message}")]
    NumericalInstability {
        /// Description of the instability.
        message: String,
        /// The facet sequence where the instability occurred, if applicable.
        facet_sequence: Option<Vec<usize>>,
    },

    /// Near-singular flow map detected (det(A - I) ≈ 0).
    #[error("Near-singular flow map: det(A - I) = {determinant:.2e}. Facet sequence: {facet_sequence:?}")]
    NearSingularFlowMap {
        /// The determinant value.
        determinant: f64,
        /// The facet sequence.
        facet_sequence: Vec<usize>,
    },

    /// Matrix inversion failed (degenerate 2-face).
    #[error("Degenerate 2-face at facets ({i}, {j}): {message}")]
    DegenerateTwoFace {
        /// First facet index.
        i: usize,
        /// Second facet index.
        j: usize,
        /// Description of why it's degenerate.
        message: String,
    },

    /// Orbit validation failed.
    #[error("Orbit validation failed: {0}")]
    ValidationFailed(String),
}

/// Result type for tube algorithm operations.
pub type TubeResult<T> = Result<T, TubeError>;
