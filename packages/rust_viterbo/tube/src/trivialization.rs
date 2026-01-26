//! Trivialization of 2-face tangent spaces using the quaternion structure.
//!
//! The orthonormal basis for R^4 w.r.t. normal n is {n, Jn, Kn, In} where I = JK.
//! - n: normal to facet
//! - Jn: Reeb flow direction (R = 2/h · Jn)
//! - Kn, In: transverse directions (the 2D plane we trivialize to)
//!
//! The trivialization captures the 2D plane transverse to both the normal and the flow.

use nalgebra::{Matrix2, Matrix4, Vector2, Vector4};

use crate::geom::{J_MATRIX, K_MATRIX};
use crate::tol::EPS;

/// I = JK (the third imaginary quaternion, completing the basis {1, I, J, K})
pub const I_MATRIX: Matrix4<f64> = {
    // I = J * K computed manually
    // J = [[0,0,-1,0], [0,0,0,-1], [1,0,0,0], [0,1,0,0]]
    // K = [[0,-1,0,0], [1,0,0,0], [0,0,0,1], [0,0,-1,0]]
    // I[i,j] = sum_k J[i,k] * K[k,j]
    Matrix4::new(
        0.0, 0.0, 0.0, -1.0, // row 0
        0.0, 0.0, 1.0, 0.0,  // row 1
        0.0, -1.0, 0.0, 0.0, // row 2
        1.0, 0.0, 0.0, 0.0,  // row 3
    )
};

/// Trivialize a 4D vector to the 2D plane transverse to n and Jn.
///
/// τ_n(V) = (⟨V, Kn⟩, ⟨V, In⟩) where I = JK
///
/// This captures the 2D subspace perpendicular to both the facet normal n
/// and the Reeb flow direction Jn.
pub fn trivialize(n: &Vector4<f64>, v: &Vector4<f64>) -> Vector2<f64> {
    let kn = K_MATRIX * n;
    let i_n = I_MATRIX * n;
    Vector2::new(v.dot(&kn), v.dot(&i_n))
}

/// Inverse trivialization: convert 2D coordinates back to 4D.
///
/// τ_n⁻¹(a, b) = a · Kn + b · In
pub fn untrivialize(n: &Vector4<f64>, coords: &Vector2<f64>) -> Vector4<f64> {
    let kn = K_MATRIX * n;
    let i_n = I_MATRIX * n;
    kn * coords[0] + i_n * coords[1]
}

/// Compute the transition matrix ψ between two trivializations.
///
/// ψ = τ_{n_to} ∘ τ_{n_from}⁻¹
///
/// Column k of ψ is τ_{n_to}(τ_{n_from}⁻¹(e_k))
pub fn compute_transition_matrix(n_from: &Vector4<f64>, n_to: &Vector4<f64>) -> Matrix2<f64> {
    let e1 = Vector2::new(1.0, 0.0);
    let e2 = Vector2::new(0.0, 1.0);

    let v1 = untrivialize(n_from, &e1); // Kn_from
    let v2 = untrivialize(n_from, &e2); // Mn_from

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
    use crate::geom::symplectic_form;
    use approx::assert_relative_eq;

    #[test]
    fn test_trivialize_untrivialize_roundtrip() {
        let n = Vector4::new(1.0, 0.0, 0.0, 0.0);

        // For n = (1,0,0,0):
        // Kn = K * n = (0, 1, 0, 0)
        // In = I * n = JK * n = (0, 0, 0, 1)
        // So a vector in span{Kn, In} is (0, a, 0, b)
        let v_tangent = Vector4::new(0.0, 0.5, 0.0, 0.3);

        let coords = trivialize(&n, &v_tangent);
        let v_recovered = untrivialize(&n, &coords);

        assert_relative_eq!(v_recovered, v_tangent, epsilon = 1e-10);
    }

    #[test]
    fn test_quaternion_basis_orthonormal() {
        // For unit normal n, {n, Jn, Kn, In} should be orthonormal
        let n = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let jn = J_MATRIX * n;
        let kn = K_MATRIX * n;
        let i_n = I_MATRIX * n;

        // All unit length
        assert_relative_eq!(jn.norm(), 1.0, epsilon = 1e-10);
        assert_relative_eq!(kn.norm(), 1.0, epsilon = 1e-10);
        assert_relative_eq!(i_n.norm(), 1.0, epsilon = 1e-10);

        // All pairwise orthogonal
        assert_relative_eq!(n.dot(&jn), 0.0, epsilon = 1e-10);
        assert_relative_eq!(n.dot(&kn), 0.0, epsilon = 1e-10);
        assert_relative_eq!(n.dot(&i_n), 0.0, epsilon = 1e-10);
        assert_relative_eq!(jn.dot(&kn), 0.0, epsilon = 1e-10);
        assert_relative_eq!(jn.dot(&i_n), 0.0, epsilon = 1e-10);
        assert_relative_eq!(kn.dot(&i_n), 0.0, epsilon = 1e-10);
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

        // Debug: print basis vectors (trivialization uses Kn, In)
        let kn1 = K_MATRIX * n1;
        let i_n1 = I_MATRIX * n1;
        let kn2 = K_MATRIX * n2;
        let i_n2 = I_MATRIX * n2;
        println!("Kn1 = {:?}", kn1);
        println!("In1 = {:?}", i_n1);
        println!("Kn2 = {:?}", kn2);
        println!("In2 = {:?}", i_n2);

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
