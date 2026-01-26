//! Error types for the tube algorithm.

use thiserror::Error;

/// Result type for tube algorithm operations.
pub type Result<T> = std::result::Result<T, Error>;

/// Errors that can occur during tube algorithm computation.
#[derive(Debug, Error)]
pub enum Error {
    /// Polytope has no facets.
    #[error("polytope has no facets")]
    EmptyPolytope,

    /// Normals and heights vectors have different lengths.
    #[error("normals and heights have different lengths: {0} vs {1}")]
    LengthMismatch(usize, usize),

    /// A facet normal is not a unit vector.
    #[error("normal {index} is not a unit vector: ||n|| = {norm}")]
    NonUnitNormal { index: usize, norm: f64 },

    /// A facet height is not positive (0 must be in interior).
    #[error("height {index} is not positive: h = {height}")]
    NonPositiveHeight { index: usize, height: f64 },

    /// Duplicate half-spaces detected.
    #[error("half-spaces {i} and {j} are duplicates")]
    DuplicateHalfspaces { i: usize, j: usize },

    /// Polytope has Lagrangian 2-faces (tube algorithm inapplicable).
    #[error("polytope has Lagrangian 2-faces: tube algorithm requires all 2-faces non-Lagrangian")]
    LagrangianTwoFaces,

    /// No valid closed Reeb orbits found.
    #[error("no valid closed Reeb orbits found")]
    NoValidOrbits,

    /// Near-singular flow map in tube closure (degenerate polytope or numerical instability).
    #[error("near-singular flow map: det(A - I) = {det:.2e}, facet sequence = {facets:?}")]
    NearSingularFlowMap { det: f64, facets: Vec<usize> },

    /// Orbit validation failed.
    #[error("orbit validation failed: {0}")]
    ValidationError(String),
}
