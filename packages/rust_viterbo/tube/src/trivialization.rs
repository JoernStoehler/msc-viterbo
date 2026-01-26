//! Trivialization of 2-face tangent spaces using the quaternion structure.
//!
//! Based on CH2021 Definition 2.15 and Lemma 2.16.

use nalgebra::{Matrix2, Vector2, Vector4};

use crate::geom::{symplectic_form, J_MATRIX, K_MATRIX};
use crate::tol::EPS;

/// Trivialize a 4D vector tangent to the facet with normal `n`.
///
/// τ_n(V) = (⟨V, Jn⟩, ⟨V, Kn⟩)
///
/// Note: This function can be applied to any V ∈ ℝ⁴, but its geometric meaning
/// requires V tangent to the facet (i.e., ⟨V, n⟩ = 0).
pub fn trivialize(n: &Vector4<f64>, v: &Vector4<f64>) -> Vector2<f64> {
    let jn = J_MATRIX * n;
    let kn = K_MATRIX * n;
    Vector2::new(v.dot(&jn), v.dot(&kn))
}

/// Inverse trivialization: convert 2D coordinates back to 4D.
///
/// τ_n⁻¹(a, b) = a · Jn + b · Kn
pub fn untrivialize(n: &Vector4<f64>, coords: &Vector2<f64>) -> Vector4<f64> {
    let jn = J_MATRIX * n;
    let kn = K_MATRIX * n;
    jn * coords[0] + kn * coords[1]
}

/// Compute the transition matrix ψ between two trivializations.
///
/// ψ = τ_{n_to} ∘ τ_{n_from}⁻¹
///
/// Column k of ψ is τ_{n_to}(τ_{n_from}⁻¹(e_k))
pub fn compute_transition_matrix(n_from: &Vector4<f64>, n_to: &Vector4<f64>) -> Matrix2<f64> {
    let e1 = Vector2::new(1.0, 0.0);
    let e2 = Vector2::new(0.0, 1.0);

    let v1 = untrivialize(n_from, &e1); // Jn_from
    let v2 = untrivialize(n_from, &e2); // Kn_from

    let col1 = trivialize(n_to, &v1);
    let col2 = trivialize(n_to, &v2);

    Matrix2::from_columns(&[col1, col2])
}

/// Compute the rotation number of a 2×2 symplectic matrix.
///
/// ρ = (1/2π) · arccos(tr(ψ)/2)
///
/// For non-Lagrangian 2-faces, ρ ∈ (0, 0.5).
pub fn compute_rotation_number(psi: &Matrix2<f64>) -> f64 {
    let trace = psi.trace();
    // Clamp to [-2, 2] to handle floating point errors
    let half_trace_clamped = (0.5 * trace).clamp(-1.0, 1.0);
    half_trace_clamped.acos() / (2.0 * std::f64::consts::PI)
}

/// Verify that a transition matrix is symplectic (det = 1).
pub fn is_symplectic(psi: &Matrix2<f64>) -> bool {
    (psi.determinant() - 1.0).abs() < EPS
}

/// Check if a 2-face is Lagrangian based on the trace of its transition matrix.
///
/// |tr(ψ)| = 2 indicates parabolic (Lagrangian).
/// This should agree with ω(n_i, n_j) = 0.
pub fn is_lagrangian_by_trace(psi: &Matrix2<f64>) -> bool {
    (psi.trace().abs() - 2.0).abs() < EPS
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    #[test]
    fn test_trivialize_untrivialize_roundtrip() {
        let n = Vector4::new(1.0, 0.0, 0.0, 0.0);

        // A vector in span{Jn, Kn} - not just perpendicular to n
        // Jn = (0, 0, 1, 0), Kn = (0, 1, 0, 0)
        // So v_tangent = 0.5 * Jn + 0.3 * Kn = (0, 0.3, 0.5, 0)
        let v_tangent = Vector4::new(0.0, 0.3, 0.5, 0.0);

        let coords = trivialize(&n, &v_tangent);
        let v_recovered = untrivialize(&n, &coords);

        assert_relative_eq!(v_recovered, v_tangent, epsilon = 1e-10);
    }

    #[test]
    fn test_jn_kn_orthonormal() {
        // For unit normal n, Jn and Kn should be orthonormal and perpendicular to n
        let n = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let jn = J_MATRIX * n;
        let kn = K_MATRIX * n;

        // Orthogonal
        assert_relative_eq!(jn.dot(&kn), 0.0, epsilon = 1e-10);

        // Unit length
        assert_relative_eq!(jn.norm(), 1.0, epsilon = 1e-10);
        assert_relative_eq!(kn.norm(), 1.0, epsilon = 1e-10);

        // Perpendicular to n
        assert_relative_eq!(jn.dot(&n), 0.0, epsilon = 1e-10);
        assert_relative_eq!(kn.dot(&n), 0.0, epsilon = 1e-10);
    }

    #[test]
    fn test_transition_matrix_symplectic() {
        // Use cross-polytope normals that form a NON-LAGRANGIAN 2-face
        // Per implementation-notes: n_i = (1,1,1,1)/2, n_j = (1,1,1,-1)/2 gives ω = -0.5 ≠ 0
        let n1 = Vector4::new(1.0, 1.0, 1.0, 1.0) / 2.0;
        let n2 = Vector4::new(1.0, 1.0, 1.0, -1.0) / 2.0;

        // Verify unit length
        let n1_norm: f64 = n1.norm();
        let n2_norm: f64 = n2.norm();
        assert!((n1_norm - 1.0).abs() < EPS, "n1 should be unit");
        assert!((n2_norm - 1.0).abs() < EPS, "n2 should be unit");

        // Verify it's non-Lagrangian
        let omega = symplectic_form(&n1, &n2);
        println!("ω(n1, n2) = {}", omega);
        assert!(
            omega.abs() > EPS,
            "Should be non-Lagrangian, got ω = {}",
            omega
        );

        // Debug: print basis vectors
        let jn1 = J_MATRIX * n1;
        let kn1 = K_MATRIX * n1;
        let jn2 = J_MATRIX * n2;
        let kn2 = K_MATRIX * n2;
        println!("Jn1 = {:?}", jn1);
        println!("Kn1 = {:?}", kn1);
        println!("Jn2 = {:?}", jn2);
        println!("Kn2 = {:?}", kn2);

        let psi = compute_transition_matrix(&n1, &n2);
        println!("Transition matrix: {:?}", psi);
        println!("Determinant: {}", psi.determinant());
        println!("Trace: {}", psi.trace());

        // Should be symplectic (det = 1)
        assert!(
            is_symplectic(&psi),
            "det = {} should be 1",
            psi.determinant()
        );
    }

    #[test]
    fn test_symplectic_form_preservation() {
        // CH2021 Lemma 2.16: trivialization preserves symplectic form for tangent vectors
        let n = Vector4::new(1.0 / 2.0_f64.sqrt(), 1.0 / 2.0_f64.sqrt(), 0.0, 0.0);

        // Two vectors tangent to the facet (perpendicular to n)
        let v1 = Vector4::new(-1.0 / 2.0_f64.sqrt(), 1.0 / 2.0_f64.sqrt(), 0.0, 0.0);
        let v2 = Vector4::new(0.0, 0.0, 1.0, 0.0);

        // Verify they're tangent
        assert!(v1.dot(&n).abs() < EPS);
        assert!(v2.dot(&n).abs() < EPS);

        let omega_4d = symplectic_form(&v1, &v2);
        let t1 = trivialize(&n, &v1);
        let t2 = trivialize(&n, &v2);
        let omega_2d = crate::geom::symplectic_form_2d(&t1, &t2);

        assert_relative_eq!(omega_4d, omega_2d, epsilon = 1e-10);
    }

    #[test]
    fn test_rotation_number_range() {
        // For non-Lagrangian 2-faces, rotation should be in (0, 0.5)
        let n1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let n2 = Vector4::new(0.0, 0.0, 1.0, 0.0);

        let omega = symplectic_form(&n1, &n2);
        assert!(omega.abs() > EPS, "Should be non-Lagrangian");

        let psi = compute_transition_matrix(&n1, &n2);
        let rho = compute_rotation_number(&psi);

        assert!(rho > 0.0);
        assert!(rho < 0.5);
    }
}
