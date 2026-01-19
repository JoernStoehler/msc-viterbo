//! Core symplectic algebra for ℝ⁴.
//!
//! This module contains the mathematical building blocks for symplectic geometry:
//! - Almost complex structure J and symplectic form ω
//! - Trivialization maps τ_n for projecting to 2-faces
//! - Transition matrices between trivializations
//! - Sp(2) classification and rotation numbers
//!
//! Conventions (locked): coordinates (q₁, q₂, p₁, p₂) and J(q,p) = (-p, q).

use crate::types::{Matrix2f, Matrix4f, SymplecticVector, Vector2f};

/// Quaternion structure matrices for trivializations.
/// Satisfy i² = j² = k² = -I and ij = k, jk = i, ki = j.
/// Convention: i = J (our almost complex structure).
///
/// In (q₁, q₂, p₁, p₂) coordinates:
pub mod quaternion {
    use super::Matrix4f;

    /// i = J: the almost complex structure J(q,p) = (-p, q)
    #[rustfmt::skip]
    pub fn mat_i() -> Matrix4f {
        Matrix4f::new(
            0.0, 0.0, -1.0, 0.0,
            0.0, 0.0, 0.0, -1.0,
            1.0, 0.0, 0.0, 0.0,
            0.0, 1.0, 0.0, 0.0,
        )
    }

    /// j: second quaternion basis element
    #[rustfmt::skip]
    pub fn mat_j() -> Matrix4f {
        Matrix4f::new(
            0.0, -1.0, 0.0, 0.0,
            1.0, 0.0, 0.0, 0.0,
            0.0, 0.0, 0.0, 1.0,
            0.0, 0.0, -1.0, 0.0,
        )
    }

    /// k: third quaternion basis element, k = ij
    #[rustfmt::skip]
    pub fn mat_k() -> Matrix4f {
        Matrix4f::new(
            0.0, 0.0, 0.0, -1.0,
            0.0, 0.0, 1.0, 0.0,
            0.0, -1.0, 0.0, 0.0,
            1.0, 0.0, 0.0, 0.0,
        )
    }
}

/// Apply the almost complex structure J(q,p) = (-p, q).
pub fn apply_j(v: SymplecticVector) -> SymplecticVector {
    SymplecticVector::new(-v.z, -v.w, v.x, v.y)
}

/// Compute the standard symplectic form ω(x,y) = ⟨Jx, y⟩.
pub fn symplectic_form(x: SymplecticVector, y: SymplecticVector) -> f64 {
    apply_j(x).dot(&y)
}

/// Standard symplectic form on ℝ²: ω₀(u, v) = u₁v₂ - u₂v₁
pub fn symplectic_form_2d(u: Vector2f, v: Vector2f) -> f64 {
    u.x * v.y - u.y * v.x
}

/// Trivialization τ_n: maps V ∈ ℝ⁴ to (⟨V, jn⟩, ⟨V, kn⟩) ∈ ℝ².
/// This uses the quaternion matrices j, k applied to normal n.
pub fn trivialization(v: SymplecticVector, n: SymplecticVector) -> Vector2f {
    let j = quaternion::mat_j();
    let k = quaternion::mat_k();
    let jn = j * n;
    let kn = k * n;
    Vector2f::new(v.dot(&jn), v.dot(&kn))
}

/// Compute the transition matrix ψ = τ_n₂ ∘ (τ_n₁)⁻¹.
///
/// Given two normals n₁ (exit facet) and n₂ (entry facet), this computes
/// the 2×2 matrix that transforms coordinates from τ_n₁ to τ_n₂.
///
/// For a 2-face F with ω(n₁, n₂) > 0 (flow from E₁ to E₂):
/// - n₁ is the "exit" normal (τ'_F uses this)
/// - n₂ is the "entry" normal (τ_F uses this)
/// - ψ_F = τ_F ∘ (τ'_F)⁻¹ = transition_matrix(n₁, n₂)
pub fn transition_matrix(n1: SymplecticVector, n2: SymplecticVector) -> Matrix2f {
    let j = quaternion::mat_j();
    let k = quaternion::mat_k();

    let jn1 = j * n1;
    let kn1 = k * n1;
    let jn2 = j * n2;
    let kn2 = k * n2;

    // ψ[i,j] = ⟨basis_i of τ_n2, basis_j of τ_n1⟩
    Matrix2f::new(
        jn2.dot(&jn1),
        jn2.dot(&kn1),
        kn2.dot(&jn1),
        kn2.dot(&kn1),
    )
}

/// Classification of elements of Sp(2) by trace.
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Sp2Class {
    PositiveHyperbolic, // Tr > 2
    PositiveShear,      // Tr = 2, A ≠ I
    NegativeHyperbolic, // Tr < -2
    NegativeShear,      // Tr = -2
    PositiveElliptic,   // |Tr| < 2, positive orientation
    NegativeElliptic,   // |Tr| < 2, negative orientation
    Identity,           // A = I
}

/// Classify a 2×2 matrix as an element of Sp(2).
pub fn classify_sp2(m: Matrix2f) -> Sp2Class {
    let tr = m.trace();
    let eps = 1e-10;

    if (m - Matrix2f::identity()).norm() < eps {
        return Sp2Class::Identity;
    }

    if tr > 2.0 + eps {
        Sp2Class::PositiveHyperbolic
    } else if tr < -2.0 - eps {
        Sp2Class::NegativeHyperbolic
    } else if (tr - 2.0).abs() <= eps {
        Sp2Class::PositiveShear
    } else if (tr + 2.0).abs() <= eps {
        Sp2Class::NegativeShear
    } else {
        let v = Vector2f::new(1.0, 0.0);
        let av = m * v;
        let det = v.x * av.y - v.y * av.x;
        if det > 0.0 {
            Sp2Class::PositiveElliptic
        } else {
            Sp2Class::NegativeElliptic
        }
    }
}

/// Compute the rotation number for a positive elliptic matrix.
/// Returns θ ∈ (0, 0.5) such that eigenvalues are e^{±2πiθ}.
///
/// For non-positive-elliptic matrices, returns None.
pub fn rotation_number(m: Matrix2f) -> Option<f64> {
    if classify_sp2(m) != Sp2Class::PositiveElliptic {
        return None;
    }

    let tr = m.trace();
    let cos_val = (tr / 2.0).clamp(-1.0, 1.0);
    let theta = cos_val.acos() / (2.0 * std::f64::consts::PI);

    Some(theta)
}

/// Compute the rotation increment for a 2-face with given normals.
///
/// n1: normal of exit facet (flow leaving)
/// n2: normal of entry facet (flow entering)
///
/// Returns ρ ∈ (0, 0.5) for non-Lagrangian 2-faces, None for Lagrangian.
pub fn two_face_rotation(n1: SymplecticVector, n2: SymplecticVector) -> Option<f64> {
    let omega = symplectic_form(n1, n2);
    if omega.abs() < 1e-10 {
        return None; // Lagrangian
    }

    let psi = transition_matrix(n1, n2);
    rotation_number(psi)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn j_squared_is_minus_identity() {
        let v = SymplecticVector::new(1.5, -2.0, 3.0, 4.5);
        let jj = apply_j(apply_j(v));
        let expected = SymplecticVector::new(-v.x, -v.y, -v.z, -v.w);
        assert_eq!(jj, expected);
    }

    #[test]
    fn omega_is_antisymmetric() {
        let x = SymplecticVector::new(1.0, 2.0, 3.0, 4.0);
        let y = SymplecticVector::new(-2.0, 1.5, -1.0, 0.5);
        let sum = symplectic_form(x, y) + symplectic_form(y, x);
        assert!(sum.abs() < 1e-12);
    }

    #[test]
    fn omega_matches_coordinate_formula() {
        let x = SymplecticVector::new(1.0, -2.0, 3.0, -4.0);
        let y = SymplecticVector::new(-0.5, 1.5, 2.0, -3.0);
        let omega = symplectic_form(x, y);
        let q_dot_p = x.x * y.z + x.y * y.w;
        let p_dot_q = x.z * y.x + x.w * y.y;
        assert!((omega - (q_dot_p - p_dot_q)).abs() < 1e-12);
    }

    #[test]
    fn omega_standard_basis_positive() {
        let e1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let e3 = SymplecticVector::new(0.0, 0.0, 1.0, 0.0);
        assert!((symplectic_form(e1, e3) - 1.0).abs() < 1e-12);
    }

    #[test]
    fn omega_standard_basis_negative() {
        let e1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let e3 = SymplecticVector::new(0.0, 0.0, 1.0, 0.0);
        assert!((symplectic_form(e3, e1) + 1.0).abs() < 1e-12);
    }

    #[test]
    fn omega_lagrangian_pairs() {
        let e1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let e2 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);
        assert!(symplectic_form(e1, e2).abs() < 1e-12);
    }

    pub mod quaternion_tests {
        use super::*;

        fn identity() -> Matrix4f {
            Matrix4f::identity()
        }

        #[test]
        fn i_squared_is_minus_identity() {
            let i = quaternion::mat_i();
            let result = i * i;
            assert!((result + identity()).norm() < 1e-12);
        }

        #[test]
        fn j_squared_is_minus_identity() {
            let j = quaternion::mat_j();
            let result = j * j;
            assert!((result + identity()).norm() < 1e-12);
        }

        #[test]
        fn k_squared_is_minus_identity() {
            let k = quaternion::mat_k();
            let result = k * k;
            assert!((result + identity()).norm() < 1e-12);
        }

        #[test]
        fn ij_equals_k() {
            let i = quaternion::mat_i();
            let j = quaternion::mat_j();
            let k = quaternion::mat_k();
            assert!((i * j - k).norm() < 1e-12);
        }

        #[test]
        fn jk_equals_i() {
            let i = quaternion::mat_i();
            let j = quaternion::mat_j();
            let k = quaternion::mat_k();
            assert!((j * k - i).norm() < 1e-12);
        }

        #[test]
        fn ki_equals_j() {
            let i = quaternion::mat_i();
            let j = quaternion::mat_j();
            let k = quaternion::mat_k();
            assert!((k * i - j).norm() < 1e-12);
        }

        #[test]
        fn anticommutator_relations() {
            let i = quaternion::mat_i();
            let j = quaternion::mat_j();
            let k = quaternion::mat_k();
            assert!((i * j + j * i).norm() < 1e-12);
            assert!((j * k + k * j).norm() < 1e-12);
            assert!((k * i + i * k).norm() < 1e-12);
        }

        #[test]
        fn all_matrices_are_orthogonal() {
            for m in [quaternion::mat_i(), quaternion::mat_j(), quaternion::mat_k()] {
                let mt = m.transpose();
                assert!((m * mt - identity()).norm() < 1e-12);
            }
        }

        #[test]
        fn i_equals_j_matrix() {
            let i = quaternion::mat_i();
            let v = SymplecticVector::new(1.0, 2.0, 3.0, 4.0);
            let iv = i * v;
            let jv = apply_j(v);
            assert!((iv - jv).norm() < 1e-12);
        }
    }

    pub mod trivialization_tests {
        use super::*;

        #[test]
        fn trivialization_preserves_symplectic_form() {
            let n = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
            let v1 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);
            let v2 = SymplecticVector::new(0.0, 0.0, 0.0, 1.0);

            let t1 = trivialization(v1, n);
            let t2 = trivialization(v2, n);

            let omega_4d = symplectic_form(v1, v2);
            let omega_2d = symplectic_form_2d(t1, t2);

            assert!(
                (omega_4d - omega_2d).abs() < 1e-10,
                "ω(v₁,v₂)={omega_4d}, ω₀(τv₁,τv₂)={omega_2d}"
            );
        }

        #[test]
        fn trivialization_preserves_symplectic_form_various_normals() {
            let normals = [
                SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
                SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
                SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
                SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
                SymplecticVector::new(1.0, 1.0, 0.0, 0.0).normalize(),
            ];

            for n in &normals {
                let j = quaternion::mat_j();
                let k = quaternion::mat_k();
                let jn = j * n;
                let kn = k * n;

                let omega_4d = symplectic_form(jn, kn);
                let t_jn = trivialization(jn, *n);
                let t_kn = trivialization(kn, *n);
                let omega_2d = symplectic_form_2d(t_jn, t_kn);

                assert!(
                    (omega_4d - omega_2d).abs() < 1e-10,
                    "normal={n:?}: ω(jn,kn)={omega_4d}, ω₀(τjn,τkn)={omega_2d}"
                );
            }
        }
    }

    pub mod sp2_tests {
        use super::*;

        #[test]
        fn symplectic_form_2d_antisymmetric() {
            let u = Vector2f::new(1.0, 2.0);
            let v = Vector2f::new(3.0, -1.0);
            assert!((symplectic_form_2d(u, v) + symplectic_form_2d(v, u)).abs() < 1e-12);
        }

        #[test]
        fn symplectic_form_2d_standard_basis() {
            let e1 = Vector2f::new(1.0, 0.0);
            let e2 = Vector2f::new(0.0, 1.0);
            assert!((symplectic_form_2d(e1, e2) - 1.0).abs() < 1e-12);
        }
    }

    pub mod rotation_tests {
        use super::*;
        use std::f64::consts::PI;

        #[test]
        fn rotation_in_valid_range() {
            let theta = PI / 6.0;
            let c = theta.cos();
            let s = theta.sin();
            let m = Matrix2f::new(c, -s, s, c);
            if let Some(rot) = rotation_number(m) {
                assert!(rot > 0.0 && rot < 0.5);
            }
        }

        #[test]
        fn rotation_number_for_standard_rotations() {
            for angle_deg in [30.0, 45.0, 60.0, 90.0, 120.0] {
                let theta = angle_deg * PI / 180.0;
                let c = theta.cos();
                let s = theta.sin();
                let m = Matrix2f::new(c, -s, s, c);
                let expected = angle_deg / 360.0;

                if let Some(rot) = rotation_number(m) {
                    assert!(
                        (rot - expected).abs() < 1e-10,
                        "angle={angle_deg}°: expected {expected}, got {rot}"
                    );
                }
            }
        }

        #[test]
        fn rotation_orthogonal_normals_is_quarter_turn() {
            let n1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
            let n2 = SymplecticVector::new(0.0, 0.0, 1.0, 0.0);

            if let Some(rot) = two_face_rotation(n1, n2) {
                assert!(
                    (rot - 0.25).abs() < 1e-10,
                    "expected 0.25 turn, got {rot}"
                );
            }
        }

        #[test]
        fn rotation_returns_none_for_lagrangian() {
            let n1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
            let n2 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);
            assert!(two_face_rotation(n1, n2).is_none());
        }

        #[test]
        fn sp2_classification_by_trace() {
            let tests = [
                (Matrix2f::new(2.0, 1.0, 0.0, 2.0), Sp2Class::PositiveHyperbolic),
                (Matrix2f::new(-2.0, 1.0, 0.0, -2.0), Sp2Class::NegativeHyperbolic),
                (Matrix2f::identity(), Sp2Class::Identity),
            ];
            for (m, expected) in tests {
                let class = classify_sp2(m);
                assert_eq!(
                    class, expected,
                    "matrix with trace {} should be {:?}, got {:?}",
                    m.trace(),
                    expected,
                    class
                );
            }
        }
    }

    pub mod transition_matrix_tests {
        use super::*;

        #[test]
        fn transition_is_identity_for_same_normal() {
            let n = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
            let psi = transition_matrix(n, n);
            assert!((psi - Matrix2f::identity()).norm() < 1e-10);
        }

        #[test]
        fn transition_matrix_is_symplectic() {
            let n1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
            let n2 = SymplecticVector::new(0.0, 0.0, 1.0, 0.0);
            let psi = transition_matrix(n1, n2);

            let e1 = Vector2f::new(1.0, 0.0);
            let e2 = Vector2f::new(0.0, 1.0);
            let omega_before = symplectic_form_2d(e1, e2);
            let omega_after = symplectic_form_2d(psi * e1, psi * e2);

            assert!(
                (omega_before - omega_after).abs() < 1e-10,
                "ω₀(e₁,e₂)={omega_before}, ω₀(ψe₁,ψe₂)={omega_after}"
            );
        }

        #[test]
        fn transition_matrix_is_positive_elliptic_for_non_lagrangian() {
            let n1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
            let n2 = SymplecticVector::new(0.0, 0.0, 1.0, 0.0);
            let psi = transition_matrix(n1, n2);
            assert_eq!(classify_sp2(psi), Sp2Class::PositiveElliptic);
        }

        #[test]
        fn transition_matrix_trace_less_than_2() {
            let n1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
            let n2 = SymplecticVector::new(0.0, 0.0, 1.0, 0.0);
            let psi = transition_matrix(n1, n2);
            assert!(psi.trace().abs() < 2.0);
        }
    }
}
