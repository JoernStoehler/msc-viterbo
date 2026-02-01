//! Trivialization of 2-face tangent spaces.
//!
//! Source: CH2021 Definition 2.15 (quaternionic trivialization), Lemma 2.16.
//!
//! Each non-Lagrangian 2-face F_{ij} has a 2D tangent space TF.
//! We trivialize it using the quaternion structure:
//!   τ_n(V) = (⟨V, jn⟩, ⟨V, kn⟩)
//!
//! This module provides:
//! - `trivialize`: Map 4D vector to 2D trivialized coordinates
//! - `compute_exit_basis`: Compute basis vectors for reconstruction
//! - `compute_entry_basis`: Compute basis vectors for entry trivialization
//! - `compute_transition_matrix`: Compute τ_exit ∘ τ_entry^{-1}
//! - `rotation_number`: Compute rotation number from transition matrix

use nalgebra::{Matrix2, Matrix4, Vector2, Vector4};

use crate::constants::EPS;
#[cfg(test)]
use crate::quaternion::apply_quat_i;
use crate::quaternion::{apply_quat_j, apply_quat_k};

/// Trivialize a 4D vector using normal n.
///
/// τ_n(V) = (⟨V, jn⟩, ⟨V, kn⟩)
///
/// IMPORTANT: This maps 4D vectors to 2D coordinates. It is an isomorphism
/// when restricted to a 2-face tangent space, but does NOT have a simple
/// inverse formula. Use explicit basis vectors for reconstruction.
#[inline]
pub fn trivialize(n: &Vector4<f64>, v: &Vector4<f64>) -> Vector2<f64> {
    let jn = apply_quat_j(n);
    let kn = apply_quat_k(n);
    Vector2::new(v.dot(&jn), v.dot(&kn))
}

/// Compute explicit basis vectors for exit trivialization.
///
/// Given a 2-face F at intersection of facets with normals n_entry and n_exit,
/// compute {b₁, b₂} ∈ TF such that:
///   τ_{n_exit}(b₁) = (1, 0)
///   τ_{n_exit}(b₂) = (0, 1)
///
/// Matrix formulation: M = [n_entry; n_exit; jn_exit; kn_exit]
/// Then b₁ = M⁻¹ · [0, 0, 1, 0]ᵀ (3rd column of M⁻¹)
///      b₂ = M⁻¹ · [0, 0, 0, 1]ᵀ (4th column of M⁻¹)
pub fn compute_exit_basis(
    n_entry: &Vector4<f64>,
    n_exit: &Vector4<f64>,
) -> Result<[Vector4<f64>; 2], &'static str> {
    let jn_exit = apply_quat_j(n_exit);
    let kn_exit = apply_quat_k(n_exit);

    // Build matrix M with rows: n_entry, n_exit, jn_exit, kn_exit
    let m = Matrix4::from_rows(&[
        n_entry.transpose(),
        n_exit.transpose(),
        jn_exit.transpose(),
        kn_exit.transpose(),
    ]);

    let m_inv = m
        .try_inverse()
        .ok_or("Degenerate 2-face: M not invertible")?;

    // Extract 3rd and 4th columns
    Ok([m_inv.column(2).into(), m_inv.column(3).into()])
}

/// Compute explicit basis vectors for entry trivialization.
///
/// Similar to `compute_exit_basis`, but using n_entry for trivialization.
pub fn compute_entry_basis(
    n_entry: &Vector4<f64>,
    n_exit: &Vector4<f64>,
) -> Result<[Vector4<f64>; 2], &'static str> {
    let jn_entry = apply_quat_j(n_entry);
    let kn_entry = apply_quat_k(n_entry);

    let m = Matrix4::from_rows(&[
        n_entry.transpose(),
        n_exit.transpose(),
        jn_entry.transpose(),
        kn_entry.transpose(),
    ]);

    let m_inv = m
        .try_inverse()
        .ok_or("Degenerate 2-face: M not invertible")?;

    Ok([m_inv.column(2).into(), m_inv.column(3).into()])
}

/// Compute transition matrix using explicit basis vectors (recommended method).
///
/// ψ_F = τ_{n_exit} ∘ τ_{n_entry}^{-1}
///
/// Column k of ψ is τ_{n_exit}(b_k^entry).
pub fn compute_transition_matrix_basis(
    b_entry: &[Vector4<f64>; 2],
    n_exit: &Vector4<f64>,
) -> Matrix2<f64> {
    let jn_exit = apply_quat_j(n_exit);
    let kn_exit = apply_quat_k(n_exit);

    // Column k of ψ is τ_{n_exit}(b_k^entry)
    Matrix2::new(
        b_entry[0].dot(&jn_exit),
        b_entry[1].dot(&jn_exit),
        b_entry[0].dot(&kn_exit),
        b_entry[1].dot(&kn_exit),
    )
}

/// Compute transition matrix using CH2021 direct formula (for verification).
///
/// From CH2021 Lemma 2.17:
///   a₁ = ⟨n_entry, n_exit⟩
///   a₂ = ⟨in_entry, n_exit⟩
///   a₃ = ⟨jn_entry, n_exit⟩
///   a₄ = ⟨kn_entry, n_exit⟩
///
///   ψ = (1/a₂) * | a₁a₂ - a₃a₄    -(a₂² + a₄²) |
///                | a₂² + a₃²       a₁a₂ + a₃a₄  |
#[cfg(test)]
pub fn compute_transition_matrix_ch2021(
    n_entry: &Vector4<f64>,
    n_exit: &Vector4<f64>,
) -> Result<Matrix2<f64>, &'static str> {
    let a1 = n_entry.dot(n_exit);
    let a2 = apply_quat_i(n_entry).dot(n_exit);
    let a3 = apply_quat_j(n_entry).dot(n_exit);
    let a4 = apply_quat_k(n_entry).dot(n_exit);

    if a2.abs() < EPS {
        return Err("a2 ≈ 0 indicates Lagrangian 2-face or wrong flow direction");
    }

    let inv_a2 = 1.0 / a2;
    Ok(Matrix2::new(
        inv_a2 * (a1 * a2 - a3 * a4),
        inv_a2 * -(a2 * a2 + a4 * a4),
        inv_a2 * (a2 * a2 + a3 * a3),
        inv_a2 * (a1 * a2 + a3 * a4),
    ))
}

/// Compute rotation number from transition matrix trace.
///
/// ρ(F) = (1/2π) * arccos(tr(ψ)/2)
///
/// Since tr(ψ) = 2⟨n_entry, n_exit⟩ for polytope 2-faces,
/// this is just the angle between normals divided by 2π.
pub fn rotation_number_from_trace(trace: f64) -> f64 {
    // Clamp for numerical robustness (trace should be in (-2, 2))
    let half_trace = (0.5 * trace).clamp(-1.0 + EPS, 1.0 - EPS);
    half_trace.acos() / (2.0 * std::f64::consts::PI)
}

/// Compute rotation number directly from normals.
///
/// ρ = (1/2π) * arccos(⟨n_entry, n_exit⟩)
#[cfg(test)]
pub fn rotation_number_direct(n_entry: &Vector4<f64>, n_exit: &Vector4<f64>) -> f64 {
    let cos_angle = n_entry.dot(n_exit).clamp(-1.0 + EPS, 1.0 - EPS);
    cos_angle.acos() / (2.0 * std::f64::consts::PI)
}

/// Validate basis vectors lie in the 2-face tangent space.
#[cfg(test)]
fn validate_basis_in_tf(
    basis: &[Vector4<f64>; 2],
    n_entry: &Vector4<f64>,
    n_exit: &Vector4<f64>,
) -> bool {
    // Basis vectors must be perpendicular to BOTH normals
    basis[0].dot(n_entry).abs() < EPS
        && basis[0].dot(n_exit).abs() < EPS
        && basis[1].dot(n_entry).abs() < EPS
        && basis[1].dot(n_exit).abs() < EPS
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    /// Test with cross-polytope adjacent facet normals (regression test for trivialization bug).
    #[test]
    fn test_cross_polytope_trivialization() {
        // Adjacent facet normals from 16-cell (cross-polytope)
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        // Compute basis vectors
        let b_exit = compute_exit_basis(&n_entry, &n_exit).unwrap();
        let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();

        // Basis vectors must lie in TF (perpendicular to BOTH normals)
        assert!(validate_basis_in_tf(&b_exit, &n_entry, &n_exit));
        assert!(validate_basis_in_tf(&b_entry, &n_entry, &n_exit));

        // Verify exit basis gives correct coordinates
        let jn_exit = apply_quat_j(&n_exit);
        let kn_exit = apply_quat_k(&n_exit);
        assert_relative_eq!(b_exit[0].dot(&jn_exit), 1.0, epsilon = EPS);
        assert_relative_eq!(b_exit[0].dot(&kn_exit), 0.0, epsilon = EPS);
        assert_relative_eq!(b_exit[1].dot(&jn_exit), 0.0, epsilon = EPS);
        assert_relative_eq!(b_exit[1].dot(&kn_exit), 1.0, epsilon = EPS);
    }

    #[test]
    fn test_transition_matrix_methods_agree() {
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();
        let psi_basis = compute_transition_matrix_basis(&b_entry, &n_exit);
        let psi_ch2021 = compute_transition_matrix_ch2021(&n_entry, &n_exit).unwrap();

        assert_relative_eq!(psi_basis, psi_ch2021, epsilon = 1e-9);
    }

    #[test]
    fn test_transition_matrix_is_symplectic() {
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();
        let psi = compute_transition_matrix_basis(&b_entry, &n_exit);

        // det(ψ) = 1 for symplectic matrices
        assert_relative_eq!(psi.determinant(), 1.0, epsilon = EPS);
    }

    #[test]
    fn test_transition_matrix_trace_formula() {
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();
        let psi = compute_transition_matrix_basis(&b_entry, &n_exit);

        // tr(ψ) = 2⟨n_entry, n_exit⟩
        let expected_trace = 2.0 * n_entry.dot(&n_exit);
        assert_relative_eq!(psi.trace(), expected_trace, epsilon = EPS);
    }

    #[test]
    fn test_rotation_number_consistency() {
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();
        let psi = compute_transition_matrix_basis(&b_entry, &n_exit);

        let rho_trace = rotation_number_from_trace(psi.trace());
        let rho_direct = rotation_number_direct(&n_entry, &n_exit);

        assert_relative_eq!(rho_trace, rho_direct, epsilon = EPS);
    }

    #[test]
    fn test_rotation_number_valid_range() {
        // For any non-parallel, non-opposite unit normals, rotation should be in (0, 0.5)
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let rho = rotation_number_direct(&n_entry, &n_exit);
        assert!(rho > 0.0 && rho < 0.5, "rotation = {} not in (0, 0.5)", rho);
    }

    #[test]
    fn test_trivialize_round_trip() {
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let b_exit = compute_exit_basis(&n_entry, &n_exit).unwrap();

        // A vector in TF
        let v = 0.3 * b_exit[0] + 0.7 * b_exit[1];

        // Trivialize and reconstruct
        let coords = trivialize(&n_exit, &v);
        let v_recovered = coords[0] * b_exit[0] + coords[1] * b_exit[1];

        assert_relative_eq!(v, v_recovered, epsilon = EPS);
    }
}
