//! Trivialization of 2-face tangent spaces.
//!
//! This module implements the quaternionic trivialization from CH2021 Definition 2.15.
//!
//! For a non-Lagrangian 2-face F at intersection of facets with normals n_entry and n_exit,
//! the trivialization τ_n: TF → ℝ² is given by:
//!
//!   τ_n(V) = (⟨V, Jn⟩, ⟨V, Kn⟩)
//!
//! where J, K are the quaternion matrices.
//!
//! # Important: Correct inverse
//!
//! The WRONG inverse (from old spec): V = coords[0] * Jn + coords[1] * Kn
//! This gives a vector in span{Jn, Kn}, NOT in TF!
//!
//! The CORRECT inverse requires explicit basis vectors b₁, b₂ ∈ TF such that
//! τ(bᵢ) = eᵢ. These are computed by solving a linear system.

use nalgebra::{Matrix4, Vector2, Vector4};

use crate::error::{TubeError, TubeResult};
use crate::symplectic::{apply_j, apply_k};

/// Trivialize a 4D vector using normal n.
///
/// τ_n(V) = (⟨V, Jn⟩, ⟨V, Kn⟩)
///
/// IMPORTANT: This function works for any 4D vector V, but it's only an
/// isomorphism when restricted to TF (the 2-face tangent space).
#[inline]
pub fn trivialize(n: &Vector4<f64>, v: &Vector4<f64>) -> Vector2<f64> {
    let jn = apply_j(n);
    let kn = apply_k(n);
    Vector2::new(v.dot(&jn), v.dot(&kn))
}

/// Compute exit basis vectors for a 2-face.
///
/// These are vectors b₁, b₂ ∈ TF such that τ_{n_exit}(bᵢ) = eᵢ.
///
/// # Arguments
/// - `n_entry`: Normal of the entry facet
/// - `n_exit`: Normal of the exit facet
///
/// # Returns
/// [b₁, b₂] where τ_{n_exit}(b₁) = (1, 0) and τ_{n_exit}(b₂) = (0, 1)
pub fn compute_exit_basis(
    n_entry: &Vector4<f64>,
    n_exit: &Vector4<f64>,
) -> TubeResult<[Vector4<f64>; 2]> {
    let jn_exit = apply_j(n_exit);
    let kn_exit = apply_k(n_exit);

    // Build matrix M with rows: n_entry, n_exit, jn_exit, kn_exit
    let m = Matrix4::from_rows(&[
        n_entry.transpose(),
        n_exit.transpose(),
        jn_exit.transpose(),
        kn_exit.transpose(),
    ]);

    let m_inv = m.try_inverse().ok_or_else(|| TubeError::NumericalInstability {
        message: "Cannot invert basis matrix for exit trivialization".to_string(),
        facet_sequence: None,
    })?;

    // b₁ = M⁻¹ * [0, 0, 1, 0]ᵀ (3rd column)
    // b₂ = M⁻¹ * [0, 0, 0, 1]ᵀ (4th column)
    Ok([m_inv.column(2).into(), m_inv.column(3).into()])
}

/// Compute entry basis vectors for a 2-face.
///
/// These are vectors b₁, b₂ ∈ TF such that τ_{n_entry}(bᵢ) = eᵢ.
pub fn compute_entry_basis(
    n_entry: &Vector4<f64>,
    n_exit: &Vector4<f64>,
) -> TubeResult<[Vector4<f64>; 2]> {
    let jn_entry = apply_j(n_entry);
    let kn_entry = apply_k(n_entry);

    let m = Matrix4::from_rows(&[
        n_entry.transpose(),
        n_exit.transpose(),
        jn_entry.transpose(),
        kn_entry.transpose(),
    ]);

    let m_inv = m.try_inverse().ok_or_else(|| TubeError::NumericalInstability {
        message: "Cannot invert basis matrix for entry trivialization".to_string(),
        facet_sequence: None,
    })?;

    Ok([m_inv.column(2).into(), m_inv.column(3).into()])
}

/// Untrivialize using explicit basis vectors.
///
/// Given 2D coordinates and basis vectors, reconstruct the 4D point:
/// V = coords[0] * basis[0] + coords[1] * basis[1]
///
/// To get an absolute position (not just tangent vector), add the centroid.
#[inline]
pub fn untrivialize_with_basis(
    coords: &Vector2<f64>,
    basis: &[Vector4<f64>; 2],
) -> Vector4<f64> {
    coords[0] * basis[0] + coords[1] * basis[1]
}

/// Untrivialize and add centroid to get absolute 4D position.
#[inline]
pub fn untrivialize_point(
    coords: &Vector2<f64>,
    basis: &[Vector4<f64>; 2],
    centroid: &Vector4<f64>,
) -> Vector4<f64> {
    centroid + untrivialize_with_basis(coords, basis)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::consts::EPS;
    use crate::symplectic::{symplectic_form, symplectic_form_2d};
    use approx::assert_relative_eq;

    #[test]
    fn test_trivialize_jn_gives_1_0() {
        let n = Vector4::new(0.5, 0.5, 0.5, 0.5);
        let jn = apply_j(&n);

        let _result = trivialize(&n, &jn);
        // ⟨Jn, Jn⟩ = |Jn|² = |n|²
        // ⟨Jn, Kn⟩ = ?
        // For unit n: τ(Jn) = (1, 0)
        let n_normalized = n.normalize();
        let jn_normalized = apply_j(&n_normalized);
        let result_normalized = trivialize(&n_normalized, &jn_normalized);

        assert_relative_eq!(result_normalized[0], 1.0, epsilon = 1e-14);
        assert_relative_eq!(result_normalized[1], 0.0, epsilon = 1e-14);
    }

    #[test]
    fn test_trivialize_kn_gives_0_1() {
        let n = Vector4::new(0.5, 0.5, 0.5, 0.5).normalize();
        let kn = apply_k(&n);

        let result = trivialize(&n, &kn);

        assert_relative_eq!(result[0], 0.0, epsilon = 1e-14);
        assert_relative_eq!(result[1], 1.0, epsilon = 1e-14);
    }

    #[test]
    fn test_exit_basis_lies_in_tangent_space() {
        // Cross-polytope adjacent normals
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let basis = compute_exit_basis(&n_entry, &n_exit).unwrap();

        // Basis vectors must be perpendicular to BOTH normals
        for b in &basis {
            assert_relative_eq!(b.dot(&n_entry), 0.0, epsilon = 1e-10);
            assert_relative_eq!(b.dot(&n_exit), 0.0, epsilon = 1e-10);
        }
    }

    #[test]
    fn test_exit_basis_trivialization_property() {
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let basis = compute_exit_basis(&n_entry, &n_exit).unwrap();

        // τ_{n_exit}(basis[0]) should be (1, 0)
        let t0 = trivialize(&n_exit, &basis[0]);
        assert_relative_eq!(t0[0], 1.0, epsilon = 1e-10);
        assert_relative_eq!(t0[1], 0.0, epsilon = 1e-10);

        // τ_{n_exit}(basis[1]) should be (0, 1)
        let t1 = trivialize(&n_exit, &basis[1]);
        assert_relative_eq!(t1[0], 0.0, epsilon = 1e-10);
        assert_relative_eq!(t1[1], 1.0, epsilon = 1e-10);
    }

    #[test]
    fn test_round_trip_trivialize_untrivialize() {
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let basis = compute_exit_basis(&n_entry, &n_exit).unwrap();

        // Create a vector in the tangent space
        let v = 0.3 * basis[0] + 0.7 * basis[1];

        // Trivialize
        let coords = trivialize(&n_exit, &v);

        // Untrivialize
        let v_recovered = untrivialize_with_basis(&coords, &basis);

        assert_relative_eq!(v_recovered, v, epsilon = 1e-10);
    }

    #[test]
    fn test_symplectic_preservation() {
        // Per CH2021 Lemma 2.16: ω(V₁, V₂) = ω_std(τ(V₁), τ(V₂)) for V₁, V₂ ∈ TF
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let basis = compute_exit_basis(&n_entry, &n_exit).unwrap();

        // Create two vectors in TF
        let v1 = 0.5 * basis[0] + 0.3 * basis[1];
        let v2 = -0.2 * basis[0] + 0.8 * basis[1];

        // Compute 4D symplectic form
        let omega_4d = symplectic_form(&v1, &v2);

        // Compute 2D symplectic form on trivialized vectors
        let t1 = trivialize(&n_exit, &v1);
        let t2 = trivialize(&n_exit, &v2);
        let omega_2d = symplectic_form_2d(&t1, &t2);

        assert_relative_eq!(omega_4d, omega_2d, epsilon = 1e-10);
    }

    #[test]
    fn test_cross_polytope_trivialization() {
        // This is the regression test from the spec (§4.5.5)
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let b_exit = compute_exit_basis(&n_entry, &n_exit).unwrap();
        let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();

        // Basis vectors must lie in 2-face tangent space
        for b in &b_exit {
            assert!(b.dot(&n_entry).abs() < EPS, "bExit not perp to n_entry");
            assert!(b.dot(&n_exit).abs() < EPS, "bExit not perp to n_exit");
        }
        for b in &b_entry {
            assert!(b.dot(&n_entry).abs() < EPS, "bEntry not perp to n_entry");
            assert!(b.dot(&n_exit).abs() < EPS, "bEntry not perp to n_exit");
        }
    }
}
