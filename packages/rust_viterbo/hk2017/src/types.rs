//! Data structures for the HK2017 algorithm.
//!
//! This module defines the input, output, configuration, and error types.

use nalgebra::{DMatrix, Vector4};

/// Numerical tolerance for floating-point equality checks.
pub const EPS: f64 = 1e-12;

/// Tolerance for constraint satisfaction (height sum, closure).
pub const CONSTRAINT_TOL: f64 = 1e-10;

/// Tolerance for checking beta >= 0 (reject if beta < -POSITIVE_TOL).
pub const POSITIVE_TOL: f64 = 1e-10;

/// Tolerance for Lagrangian face detection (omega near 0).
pub const LAGRANGIAN_TOL: f64 = 1e-8;

/// H-representation of a convex polytope K = {x : <n_i, x> <= h_i for all i}.
///
/// # Requirements
///
/// - `normals[i]` must be a unit vector (norm = 1 within EPS)
/// - `heights[i]` must be positive (origin is in the interior)
/// - `normals.len() == heights.len()`
/// - At least 2 facets for a valid closed orbit
#[derive(Debug, Clone)]
pub struct PolytopeHRep {
    /// Unit outward normals to each facet.
    pub normals: Vec<Vector4<f64>>,
    /// Signed distance from origin to each facet (must be > 0).
    pub heights: Vec<f64>,
}

impl PolytopeHRep {
    /// Create a new polytope from normals and heights.
    pub fn new(normals: Vec<Vector4<f64>>, heights: Vec<f64>) -> Self {
        Self { normals, heights }
    }

    /// Number of facets.
    pub fn num_facets(&self) -> usize {
        self.normals.len()
    }

    /// Validate the polytope representation.
    ///
    /// Returns `Ok(())` if valid, or an error describing the problem.
    pub fn validate(&self) -> Result<(), Hk2017Error> {
        // Check lengths match
        if self.normals.len() != self.heights.len() {
            return Err(Hk2017Error::InvalidPolytope(format!(
                "normals length ({}) != heights length ({})",
                self.normals.len(),
                self.heights.len()
            )));
        }

        // Need at least 2 facets for a valid closed orbit
        if self.normals.len() < 2 {
            return Err(Hk2017Error::InvalidPolytope(format!(
                "need at least 2 facets, got {}",
                self.normals.len()
            )));
        }

        // Check normals are unit vectors
        for (i, n) in self.normals.iter().enumerate() {
            let norm = n.norm();
            if (norm - 1.0).abs() > EPS {
                return Err(Hk2017Error::InvalidPolytope(format!(
                    "normal[{}] is not unit: norm = {:.15} (expected 1.0)",
                    i, norm
                )));
            }
        }

        // Check heights are positive (origin in interior)
        for (i, &h) in self.heights.iter().enumerate() {
            if h <= 0.0 {
                return Err(Hk2017Error::InvalidPolytope(format!(
                    "height[{}] = {:.15} is not positive (origin not in interior)",
                    i, h
                )));
            }
        }

        Ok(())
    }
}

/// Configuration for the HK2017 algorithm.
#[derive(Debug, Clone)]
pub struct Hk2017Config {
    /// Enumeration strategy to use.
    pub strategy: EnumerationStrategy,

    /// Numerical tolerance for constraint satisfaction.
    pub constraint_tol: f64,

    /// Numerical tolerance for beta >= 0 check.
    pub positive_tol: f64,
}

impl Default for Hk2017Config {
    fn default() -> Self {
        Self {
            strategy: EnumerationStrategy::Naive,
            constraint_tol: CONSTRAINT_TOL,
            positive_tol: POSITIVE_TOL,
        }
    }
}

impl Hk2017Config {
    /// Create config with naive enumeration.
    pub fn naive() -> Self {
        Self::default()
    }

    /// Create config with graph-pruned enumeration.
    pub fn graph_pruned() -> Self {
        Self {
            strategy: EnumerationStrategy::GraphPruned,
            ..Self::default()
        }
    }
}

/// Strategy for enumerating permutations.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum EnumerationStrategy {
    /// Enumerate all subset permutations: O(F!) complexity.
    Naive,
    /// Enumerate cycles in the facet transition graph.
    GraphPruned,
}

/// Result of the HK2017 capacity computation.
///
/// # Warning: Uncheckable Assumption
///
/// This result assumes the global maximum of Q occurs at an interior point
/// of the feasible region M(K). If the true maximum is on the boundary
/// (some beta_i = 0), this result will be **incorrect** (capacity too large).
///
/// There is no way to detect this from the output. See `impl-plan-hk2017.md`
/// for mitigation strategies.
#[derive(Debug, Clone)]
pub struct Hk2017Result {
    /// The computed EHZ capacity.
    pub capacity: f64,

    /// The optimal permutation (facet indices in visitation order).
    pub optimal_permutation: Vec<usize>,

    /// The optimal beta coefficients indexed by facet.
    /// `optimal_beta[i]` is the coefficient for facet i.
    /// Non-participating facets have beta = 0.
    pub optimal_beta: Vec<f64>,

    /// The maximum Q value achieved: capacity = 1 / (2 * q_max).
    pub q_max: f64,

    /// Number of permutations evaluated.
    pub permutations_evaluated: usize,

    /// Number of permutations where interior critical point was infeasible.
    pub permutations_rejected: usize,

    /// This flag is always `true` for the current implementation.
    /// It indicates the result relies on the uncheckable assumption that
    /// the global maximum of Q occurs at an interior point.
    pub interior_only_assumption: bool,
}

/// Error types for the HK2017 algorithm.
#[derive(Debug, thiserror::Error)]
pub enum Hk2017Error {
    /// The input polytope is invalid.
    #[error("Invalid polytope: {0}")]
    InvalidPolytope(String),

    /// No permutation yielded a feasible interior critical point.
    ///
    /// This may indicate the true maximum lies on a boundary face,
    /// which this implementation cannot find.
    #[error(
        "No feasible interior critical point found ({checked} permutations checked, {rejected} rejected)"
    )]
    NoFeasibleInteriorPoint {
        /// Number of permutations checked.
        checked: usize,
        /// Number of permutations rejected.
        rejected: usize,
        /// Histogram of rejection reasons for diagnostics.
        rejection_reasons: RejectionHistogram,
    },

    /// All permutations have non-positive Q value.
    #[error("All permutations have Q <= 0 (checked {checked} permutations)")]
    NoPositiveQ {
        /// Number of permutations checked.
        checked: usize,
    },

    /// The KKT system is singular for a permutation.
    #[error("KKT system is singular for permutation {permutation:?}")]
    SingularKkt {
        /// The permutation that caused the singularity.
        permutation: Vec<usize>,
    },

    /// Numerical computation failed.
    #[error("Numerical instability: {0}")]
    NumericalInstability(String),

    /// Result verification failed (constraints not satisfied).
    #[error("Verification failed: {0}")]
    VerificationFailed(String),
}

/// Histogram of rejection reasons for diagnostic purposes.
#[derive(Debug, Clone, Default)]
pub struct RejectionHistogram {
    /// Permutations rejected because some beta_i < 0.
    pub negative_beta: usize,
    /// Permutations rejected because KKT system was singular.
    pub singular_kkt: usize,
    /// Permutations rejected because Q <= 0.
    pub non_positive_q: usize,
    /// Permutations rejected for other reasons.
    pub other: usize,
}

impl RejectionHistogram {
    /// Total number of rejections.
    pub fn total(&self) -> usize {
        self.negative_beta + self.singular_kkt + self.non_positive_q + self.other
    }

    /// Record a rejection reason.
    pub fn record(&mut self, reason: RejectionReason) {
        match reason {
            RejectionReason::NegativeBeta => self.negative_beta += 1,
            RejectionReason::SingularKkt => self.singular_kkt += 1,
            RejectionReason::NonPositiveQ => self.non_positive_q += 1,
            RejectionReason::Other => self.other += 1,
        }
    }
}

/// Reason a permutation was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum RejectionReason {
    /// Some beta_i < 0 (interior critical point not feasible).
    NegativeBeta,
    /// KKT system was singular.
    SingularKkt,
    /// Q value was non-positive.
    NonPositiveQ,
    /// Other reason.
    Other,
}

/// Precomputed data about facets for efficient algorithm execution.
#[derive(Debug, Clone)]
pub struct FacetData {
    /// Number of facets.
    pub num_facets: usize,
    /// Unit outward normals.
    pub normals: Vec<Vector4<f64>>,
    /// Heights (distance from origin to facet).
    pub heights: Vec<f64>,
    /// Reeb vectors: p_i = (2/h_i) * J * n_i.
    pub reeb_vectors: Vec<Vector4<f64>>,
    /// Precomputed symplectic form matrix: omega_matrix[(i,j)] = omega(n_i, n_j).
    pub omega_matrix: DMatrix<f64>,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_polytope_validation_success() {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
        ];
        let heights = vec![1.0, 1.0];
        let polytope = PolytopeHRep::new(normals, heights);
        assert!(polytope.validate().is_ok());
    }

    #[test]
    fn test_polytope_validation_non_unit_normal() {
        let normals = vec![
            Vector4::new(2.0, 0.0, 0.0, 0.0), // Not unit
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
        ];
        let heights = vec![1.0, 1.0];
        let polytope = PolytopeHRep::new(normals, heights);
        let err = polytope.validate().unwrap_err();
        assert!(matches!(err, Hk2017Error::InvalidPolytope(_)));
    }

    #[test]
    fn test_polytope_validation_non_positive_height() {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
        ];
        let heights = vec![1.0, -1.0]; // Negative height
        let polytope = PolytopeHRep::new(normals, heights);
        let err = polytope.validate().unwrap_err();
        assert!(matches!(err, Hk2017Error::InvalidPolytope(_)));
    }

    #[test]
    fn test_polytope_validation_length_mismatch() {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
        ];
        let heights = vec![1.0]; // Wrong length
        let polytope = PolytopeHRep::new(normals, heights);
        let err = polytope.validate().unwrap_err();
        assert!(matches!(err, Hk2017Error::InvalidPolytope(_)));
    }

    #[test]
    fn test_polytope_validation_too_few_facets() {
        let normals = vec![Vector4::new(1.0, 0.0, 0.0, 0.0)];
        let heights = vec![1.0];
        let polytope = PolytopeHRep::new(normals, heights);
        let err = polytope.validate().unwrap_err();
        assert!(matches!(err, Hk2017Error::InvalidPolytope(_)));
    }

    #[test]
    fn test_config_default() {
        let config = Hk2017Config::default();
        assert_eq!(config.strategy, EnumerationStrategy::Naive);
        assert!((config.constraint_tol - CONSTRAINT_TOL).abs() < 1e-15);
    }
}
