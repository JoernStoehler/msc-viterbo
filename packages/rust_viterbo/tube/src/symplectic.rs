//! Symplectic geometry primitives for R^4.
//!
//! This module provides:
//! - The quaternion matrices QUAT_I, QUAT_J, QUAT_K (from CH2021 §2.3)
//! - The symplectic form ω(x, y) = ⟨Ix, y⟩
//! - The 2D symplectic form ω_std(x, y) = x₁y₂ - x₂y₁
//!
//! # Coordinate convention
//!
//! We use coordinates (q₁, q₂, p₁, p₂) where (q₁, q₂) is configuration space
//! and (p₁, p₂) is momentum space.

use nalgebra::{Matrix2, Matrix4, Vector2, Vector4};

use crate::consts::EPS;

/// QUAT_I: The standard almost complex structure J.
///
/// In coordinates (x₁, x₂, y₁, y₂) = (q₁, q₂, p₁, p₂):
/// I(q₁, q₂, p₁, p₂) = (-p₁, -p₂, q₁, q₂)
///
/// This is the symplectic J matrix: ω(x, y) = ⟨Ix, y⟩
pub fn quat_i() -> Matrix4<f64> {
    Matrix4::new(
        0.0, 0.0, -1.0, 0.0,
        0.0, 0.0, 0.0, -1.0,
        1.0, 0.0, 0.0, 0.0,
        0.0, 1.0, 0.0, 0.0,
    )
}

/// QUAT_J: Second quaternion matrix.
///
/// J(q₁, q₂, p₁, p₂) = (-q₂, q₁, p₂, -p₁)
pub fn quat_j() -> Matrix4<f64> {
    Matrix4::new(
        0.0, -1.0, 0.0, 0.0,
        1.0, 0.0, 0.0, 0.0,
        0.0, 0.0, 0.0, 1.0,
        0.0, 0.0, -1.0, 0.0,
    )
}

/// QUAT_K: Third quaternion matrix.
///
/// K(q₁, q₂, p₁, p₂) = (-p₂, p₁, -q₂, q₁)
pub fn quat_k() -> Matrix4<f64> {
    Matrix4::new(
        0.0, 0.0, 0.0, -1.0,
        0.0, 0.0, 1.0, 0.0,
        0.0, -1.0, 0.0, 0.0,
        1.0, 0.0, 0.0, 0.0,
    )
}

/// Apply the quaternion I (complex structure J) to a vector.
///
/// I(q₁, q₂, p₁, p₂) = (-p₁, -p₂, q₁, q₂)
#[inline]
pub fn apply_i(v: &Vector4<f64>) -> Vector4<f64> {
    Vector4::new(-v[2], -v[3], v[0], v[1])
}

/// Apply the quaternion J to a vector.
///
/// J(q₁, q₂, p₁, p₂) = (-q₂, q₁, p₂, -p₁)
#[inline]
pub fn apply_j(v: &Vector4<f64>) -> Vector4<f64> {
    Vector4::new(-v[1], v[0], v[3], -v[2])
}

/// Apply the quaternion K to a vector.
///
/// K(q₁, q₂, p₁, p₂) = (-p₂, p₁, -q₂, q₁)
#[inline]
pub fn apply_k(v: &Vector4<f64>) -> Vector4<f64> {
    Vector4::new(-v[3], v[2], -v[1], v[0])
}

/// The standard symplectic form on R^4.
///
/// ω(x, y) = ⟨Ix, y⟩ = q₁p₁' + q₂p₂' - p₁q₁' - p₂q₂'
///
/// Properties:
/// - Antisymmetric: ω(x, y) = -ω(y, x)
/// - Bilinear
/// - Non-degenerate
#[inline]
pub fn symplectic_form(x: &Vector4<f64>, y: &Vector4<f64>) -> f64 {
    // ω(x, y) = ⟨Ix, y⟩ where I = QUAT_I
    // = -x[2]*y[0] - x[3]*y[1] + x[0]*y[2] + x[1]*y[3]
    x[0] * y[2] + x[1] * y[3] - x[2] * y[0] - x[3] * y[1]
}

/// The standard 2D symplectic form.
///
/// ω_std(x, y) = x₁y₂ - x₂y₁
#[inline]
pub fn symplectic_form_2d(x: &Vector2<f64>, y: &Vector2<f64>) -> f64 {
    x[0] * y[1] - x[1] * y[0]
}

/// The Reeb vector on a facet.
///
/// R_i = (2/h_i) * I * n_i
///
/// # Arguments
/// - `normal`: Unit outward normal n_i
/// - `height`: Distance h_i > 0 from origin to facet
#[inline]
pub fn reeb_vector(normal: &Vector4<f64>, height: f64) -> Vector4<f64> {
    debug_assert!(height > 0.0, "Height must be positive");
    apply_i(normal) * (2.0 / height)
}

/// Check if a 2x2 matrix is symplectic (det = 1).
#[inline]
pub fn is_symplectic_2d(m: &Matrix2<f64>) -> bool {
    (m.determinant() - 1.0).abs() < EPS
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    #[test]
    fn test_quaternion_i_squared() {
        let i = quat_i();
        let i2 = i * i;
        assert_relative_eq!(i2, -Matrix4::identity(), epsilon = 1e-14);
    }

    #[test]
    fn test_quaternion_j_squared() {
        let j = quat_j();
        let j2 = j * j;
        assert_relative_eq!(j2, -Matrix4::identity(), epsilon = 1e-14);
    }

    #[test]
    fn test_quaternion_k_squared() {
        let k = quat_k();
        let k2 = k * k;
        assert_relative_eq!(k2, -Matrix4::identity(), epsilon = 1e-14);
    }

    #[test]
    fn test_quaternion_relations() {
        let i = quat_i();
        let j = quat_j();
        let k = quat_k();

        // ij = k
        assert_relative_eq!(i * j, k, epsilon = 1e-14);
        // jk = i
        assert_relative_eq!(j * k, i, epsilon = 1e-14);
        // ki = j
        assert_relative_eq!(k * i, j, epsilon = 1e-14);
    }

    #[test]
    fn test_apply_functions_match_matrices() {
        let v = Vector4::new(1.0, 2.0, 3.0, 4.0);

        assert_relative_eq!(apply_i(&v), quat_i() * v, epsilon = 1e-14);
        assert_relative_eq!(apply_j(&v), quat_j() * v, epsilon = 1e-14);
        assert_relative_eq!(apply_k(&v), quat_k() * v, epsilon = 1e-14);
    }

    #[test]
    fn test_symplectic_form_antisymmetric() {
        let x = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let y = Vector4::new(5.0, 6.0, 7.0, 8.0);

        assert_relative_eq!(
            symplectic_form(&x, &y),
            -symplectic_form(&y, &x),
            epsilon = 1e-14
        );
    }

    #[test]
    fn test_symplectic_form_standard_basis() {
        let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let e2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
        let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
        let e4 = Vector4::new(0.0, 0.0, 0.0, 1.0);

        // ω(e₁, e₃) = 1
        assert_relative_eq!(symplectic_form(&e1, &e3), 1.0, epsilon = 1e-14);
        // ω(e₂, e₄) = 1
        assert_relative_eq!(symplectic_form(&e2, &e4), 1.0, epsilon = 1e-14);
        // ω(e₁, e₂) = 0 (Lagrangian)
        assert_relative_eq!(symplectic_form(&e1, &e2), 0.0, epsilon = 1e-14);
        // ω(e₃, e₄) = 0 (Lagrangian)
        assert_relative_eq!(symplectic_form(&e3, &e4), 0.0, epsilon = 1e-14);
    }

    #[test]
    fn test_jn_kn_symplectic_property() {
        // For any unit vector n: ω(Jn, Kn) = 1
        let n = Vector4::new(0.5, 0.5, 0.5, 0.5);
        let jn = apply_j(&n);
        let kn = apply_k(&n);

        assert_relative_eq!(symplectic_form(&jn, &kn), 1.0, epsilon = 1e-14);
    }

    #[test]
    fn test_in_jn_kn_orthonormal() {
        // For any unit vector n: {In, Jn, Kn} is orthonormal
        let n = Vector4::new(0.5, 0.5, 0.5, 0.5);
        let in_ = apply_i(&n);
        let jn = apply_j(&n);
        let kn = apply_k(&n);

        // Orthogonality
        assert_relative_eq!(in_.dot(&jn), 0.0, epsilon = 1e-14);
        assert_relative_eq!(in_.dot(&kn), 0.0, epsilon = 1e-14);
        assert_relative_eq!(jn.dot(&kn), 0.0, epsilon = 1e-14);

        // Normality (same norm as n)
        assert_relative_eq!(in_.norm(), n.norm(), epsilon = 1e-14);
        assert_relative_eq!(jn.norm(), n.norm(), epsilon = 1e-14);
        assert_relative_eq!(kn.norm(), n.norm(), epsilon = 1e-14);
    }

    #[test]
    fn test_reeb_vector_perpendicular_to_normal() {
        let n = Vector4::new(0.6, 0.8, 0.0, 0.0);
        let r = reeb_vector(&n, 1.0);

        // R = 2*I*n is perpendicular to n because ⟨In, n⟩ = ω(n, n) = 0
        assert_relative_eq!(r.dot(&n), 0.0, epsilon = 1e-14);
    }

    #[test]
    fn test_symplectic_form_2d() {
        let x = Vector2::new(1.0, 2.0);
        let y = Vector2::new(3.0, 4.0);

        // ω(x, y) = 1*4 - 2*3 = -2
        assert_relative_eq!(symplectic_form_2d(&x, &y), -2.0, epsilon = 1e-14);
    }
}
