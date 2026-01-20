//! Optimization library for non-convex QP over polytopes.
//!
//! # Status: STUB - NOT IMPLEMENTED
//!
//! This crate is a placeholder. See `SPEC.md` for the implementation plan.
//!
//! # Problem Statement
//!
//! Maximize Q(β) = Σ_{j<i} β_i β_j c_{ij} subject to:
//! - β_i ≥ 0 (n inequality constraints)
//! - Σ β_i h_i = 1 (1 equality constraint)
//! - Σ β_i n_i = 0 (4 equality constraints, n_i ∈ ℝ⁴)
//!
//! Q is an **indefinite quadratic** (zero diagonal, off-diagonal = symplectic form values).
//! Standard convex QP solvers (OSQP) cannot help because they require PSD objectives.
//!
//! # Consumers
//!
//! - `rust_viterbo_algorithm::hk2019` - uses `solve_qp_for_permutation` which should
//!   be replaced by `maximize_quadratic_over_polytope` from this crate.
//!
//! # Implementation Plan
//!
//! 1. First determine if Hessian is NSD empirically (tesseract test case)
//! 2. If NSD: can use OSQP by negating objective
//! 3. If indefinite: implement complete KKT enumeration over all faces
//!
//! See `SPEC.md` for details.

use nalgebra::{DMatrix, DVector};
use thiserror::Error;

/// Errors that can occur during optimization.
#[derive(Debug, Error)]
pub enum OptimError {
    /// The problem is infeasible (empty constraint polytope).
    #[error("Infeasible: constraint polytope is empty")]
    Infeasible,

    /// The problem is unbounded (Q can grow without bound).
    #[error("Unbounded: Q grows without bound on feasible region")]
    Unbounded,

    /// Numerical issues prevented finding a solution.
    #[error("Numerical error: {0}")]
    Numerical(String),

    /// The solver is not yet implemented.
    #[error("Not implemented: {0}")]
    NotImplemented(String),
}

/// Maximize a quadratic Q(x) = x^T H x over a polytope defined by
/// equality constraints Ax = b and inequality constraints x >= 0.
///
/// # Arguments
///
/// * `hessian` - n×n symmetric matrix H (may have zero diagonal)
/// * `eq_matrix` - m×n matrix A for equality constraints
/// * `eq_rhs` - m-vector b for equality constraints
///
/// # Returns
///
/// On success, returns (max_value, argmax) where max_value = Q(argmax).
///
/// # Errors
///
/// - `Infeasible` if {x : Ax = b, x ≥ 0} is empty
/// - `Unbounded` if Q can grow without bound on the feasible region
/// - `Numerical` if numerical issues prevent finding a solution
/// - `NotImplemented` (currently always returned - this is a stub)
pub fn maximize_quadratic_over_polytope(
    _hessian: &DMatrix<f64>,
    _eq_matrix: &DMatrix<f64>,
    _eq_rhs: &DVector<f64>,
) -> Result<(f64, DVector<f64>), OptimError> {
    Err(OptimError::NotImplemented(
        "See SPEC.md for implementation plan. \
         This crate is a stub waiting for implementation."
            .to_string(),
    ))
}

/// Check if a matrix is negative semidefinite (all eigenvalues ≤ 0).
///
/// This is useful for determining if OSQP can be used (requires -H to be PSD).
pub fn is_negative_semidefinite(matrix: &DMatrix<f64>, tol: f64) -> bool {
    let eigen = matrix.clone().symmetric_eigen();
    eigen.eigenvalues.iter().all(|&ev| ev <= tol)
}

/// Check if a matrix is positive semidefinite (all eigenvalues ≥ 0).
pub fn is_positive_semidefinite(matrix: &DMatrix<f64>, tol: f64) -> bool {
    let eigen = matrix.clone().symmetric_eigen();
    eigen.eigenvalues.iter().all(|&ev| ev >= -tol)
}

/// Check if a matrix is indefinite (has both positive and negative eigenvalues).
pub fn is_indefinite(matrix: &DMatrix<f64>, tol: f64) -> bool {
    let eigen = matrix.clone().symmetric_eigen();
    let has_positive = eigen.eigenvalues.iter().any(|&ev| ev > tol);
    let has_negative = eigen.eigenvalues.iter().any(|&ev| ev < -tol);
    has_positive && has_negative
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stub_returns_not_implemented() {
        let h = DMatrix::from_row_slice(2, 2, &[0.0, 1.0, 1.0, 0.0]);
        let a = DMatrix::from_row_slice(1, 2, &[1.0, 1.0]);
        let b = DVector::from_row_slice(&[1.0]);

        let result = maximize_quadratic_over_polytope(&h, &a, &b);
        assert!(matches!(result, Err(OptimError::NotImplemented(_))));
    }

    #[test]
    fn identity_is_psd() {
        let eye = DMatrix::identity(3, 3);
        assert!(is_positive_semidefinite(&eye, 1e-10));
        assert!(!is_negative_semidefinite(&eye, 1e-10));
        assert!(!is_indefinite(&eye, 1e-10));
    }

    #[test]
    fn negative_identity_is_nsd() {
        let neg_eye = -DMatrix::<f64>::identity(3, 3);
        assert!(!is_positive_semidefinite(&neg_eye, 1e-10));
        assert!(is_negative_semidefinite(&neg_eye, 1e-10));
        assert!(!is_indefinite(&neg_eye, 1e-10));
    }

    #[test]
    fn mixed_eigenvalues_is_indefinite() {
        // diag(1, -1) is indefinite
        let mixed = DMatrix::from_row_slice(2, 2, &[1.0, 0.0, 0.0, -1.0]);
        assert!(!is_positive_semidefinite(&mixed, 1e-10));
        assert!(!is_negative_semidefinite(&mixed, 1e-10));
        assert!(is_indefinite(&mixed, 1e-10));
    }
}
