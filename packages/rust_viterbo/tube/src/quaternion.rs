//! Quaternion matrices for the trivialization.
//!
//! Source: CH2021 §2.3 (quaternionic trivialization).
//!
//! The quaternion matrices i, j, k ∈ SO(4) satisfy the quaternion relations:
//! - i² = j² = k² = ijk = -I
//! - ij = k, jk = i, ki = j
//!
//! In coordinates (x₁, x₂, y₁, y₂) = (q₁, q₂, p₁, p₂):
//! - QUAT_I is the standard almost complex structure (symplectic J)
//! - QUAT_J and QUAT_K complete the quaternion structure

#[cfg(test)]
use nalgebra::Matrix4;
use nalgebra::Vector4;

/// QUAT_I = standard almost complex structure (symplectic J).
///
/// Acts as: i(q₁, q₂, p₁, p₂) = (-p₁, -p₂, q₁, q₂)
///
/// Properties:
/// - i² = -I
/// - ω(x, y) = ⟨ix, y⟩ (defines symplectic form)
#[cfg(test)]
#[rustfmt::skip]
pub fn quat_i() -> Matrix4<f64> {
    Matrix4::new(
        0.0,  0.0, -1.0,  0.0,
        0.0,  0.0,  0.0, -1.0,
        1.0,  0.0,  0.0,  0.0,
        0.0,  1.0,  0.0,  0.0,
    )
}

/// QUAT_J quaternion matrix.
///
/// Acts as: j(q₁, q₂, p₁, p₂) = (-q₂, q₁, p₂, -p₁)
///
/// Properties:
/// - j² = -I
/// - ij = k
#[cfg(test)]
#[rustfmt::skip]
pub fn quat_j() -> Matrix4<f64> {
    Matrix4::new(
        0.0, -1.0,  0.0,  0.0,
        1.0,  0.0,  0.0,  0.0,
        0.0,  0.0,  0.0,  1.0,
        0.0,  0.0, -1.0,  0.0,
    )
}

/// QUAT_K quaternion matrix.
///
/// Acts as: k(q₁, q₂, p₁, p₂) = (-p₂, p₁, -q₂, q₁)
///
/// Properties:
/// - k² = -I
/// - ij = k, jk = i, ki = j
#[cfg(test)]
#[rustfmt::skip]
pub fn quat_k() -> Matrix4<f64> {
    Matrix4::new(
        0.0,  0.0,  0.0, -1.0,
        0.0,  0.0,  1.0,  0.0,
        0.0, -1.0,  0.0,  0.0,
        1.0,  0.0,  0.0,  0.0,
    )
}

/// Apply QUAT_I to a vector (optimized direct computation).
#[inline]
pub fn apply_quat_i(v: &Vector4<f64>) -> Vector4<f64> {
    Vector4::new(-v[2], -v[3], v[0], v[1])
}

/// Apply QUAT_J to a vector (optimized direct computation).
#[inline]
pub fn apply_quat_j(v: &Vector4<f64>) -> Vector4<f64> {
    Vector4::new(-v[1], v[0], v[3], -v[2])
}

/// Apply QUAT_K to a vector (optimized direct computation).
#[inline]
pub fn apply_quat_k(v: &Vector4<f64>) -> Vector4<f64> {
    Vector4::new(-v[3], v[2], -v[1], v[0])
}

/// Apply the symplectic structure J to a vector.
///
/// In the standard symplectic coordinates (q₁, q₂, p₁, p₂), the matrix J is:
/// J = [[0, 0, -1, 0],
///      [0, 0, 0, -1],
///      [1, 0, 0, 0],
///      [0, 1, 0, 0]]
///
/// This maps (q₁, q₂, p₁, p₂) → (-p₁, -p₂, q₁, q₂).
///
/// Note: This is mathematically identical to quaternion multiplication by i,
/// but named separately for clarity in symplectic geometry contexts.
#[inline]
pub fn symplectic_j(v: &Vector4<f64>) -> Vector4<f64> {
    Vector4::new(-v[2], -v[3], v[0], v[1])
}

/// The standard symplectic form on ℝ⁴.
///
/// ω(x, y) = ⟨Jx, y⟩ = q₁p₁' + q₂p₂' - p₁q₁' - p₂q₂'
///
/// Properties:
/// - Antisymmetric: ω(x, y) = -ω(y, x)
/// - Non-degenerate: ω(x, y) = 0 for all y implies x = 0
#[inline]
pub fn symplectic_form(x: &Vector4<f64>, y: &Vector4<f64>) -> f64 {
    symplectic_j(x).dot(y)
}

/// Compute the Reeb vector for a facet.
///
/// R_i = (2/h_i) * J * n_i
///
/// The Reeb vector is tangent to the facet (perpendicular to normal)
/// and has magnitude 2/h_i.
#[inline]
pub fn reeb_vector(normal: &Vector4<f64>, height: f64) -> Vector4<f64> {
    assert!(height > 0.0, "Height must be positive");
    symplectic_j(normal) * (2.0 / height)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::EPS;
    use approx::assert_relative_eq;

    #[test]
    fn test_quat_i_squared_is_minus_identity() {
        let i = quat_i();
        let i_squared = i * i;
        let minus_id = -Matrix4::identity();
        assert_relative_eq!(i_squared, minus_id, epsilon = EPS);
    }

    #[test]
    fn test_quat_j_squared_is_minus_identity() {
        let j = quat_j();
        let j_squared = j * j;
        let minus_id = -Matrix4::identity();
        assert_relative_eq!(j_squared, minus_id, epsilon = EPS);
    }

    #[test]
    fn test_quat_k_squared_is_minus_identity() {
        let k = quat_k();
        let k_squared = k * k;
        let minus_id = -Matrix4::identity();
        assert_relative_eq!(k_squared, minus_id, epsilon = EPS);
    }

    #[test]
    fn test_quaternion_relation_ij_equals_k() {
        let i = quat_i();
        let j = quat_j();
        let k = quat_k();
        let ij = i * j;
        assert_relative_eq!(ij, k, epsilon = EPS);
    }

    #[test]
    fn test_quaternion_relation_jk_equals_i() {
        let i = quat_i();
        let j = quat_j();
        let k = quat_k();
        let jk = j * k;
        assert_relative_eq!(jk, i, epsilon = EPS);
    }

    #[test]
    fn test_quaternion_relation_ki_equals_j() {
        let i = quat_i();
        let j = quat_j();
        let k = quat_k();
        let ki = k * i;
        assert_relative_eq!(ki, j, epsilon = EPS);
    }

    #[test]
    fn test_apply_quat_i_matches_matrix() {
        let v = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let direct = apply_quat_i(&v);
        let matrix = quat_i() * v;
        assert_relative_eq!(direct, matrix, epsilon = EPS);
    }

    #[test]
    fn test_apply_quat_j_matches_matrix() {
        let v = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let direct = apply_quat_j(&v);
        let matrix = quat_j() * v;
        assert_relative_eq!(direct, matrix, epsilon = EPS);
    }

    #[test]
    fn test_apply_quat_k_matches_matrix() {
        let v = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let direct = apply_quat_k(&v);
        let matrix = quat_k() * v;
        assert_relative_eq!(direct, matrix, epsilon = EPS);
    }

    #[test]
    fn test_orthonormal_frame_from_unit_normal() {
        // For any unit normal n, {in, jn, kn} should be orthonormal
        let n = Vector4::new(1.0, 2.0, 3.0, 4.0).normalize();
        let in_ = apply_quat_i(&n);
        let jn = apply_quat_j(&n);
        let kn = apply_quat_k(&n);

        // Orthogonality
        assert_relative_eq!(in_.dot(&jn), 0.0, epsilon = EPS);
        assert_relative_eq!(in_.dot(&kn), 0.0, epsilon = EPS);
        assert_relative_eq!(jn.dot(&kn), 0.0, epsilon = EPS);

        // Unit length
        assert_relative_eq!(in_.norm(), 1.0, epsilon = EPS);
        assert_relative_eq!(jn.norm(), 1.0, epsilon = EPS);
        assert_relative_eq!(kn.norm(), 1.0, epsilon = EPS);
    }

    #[test]
    fn test_symplectic_property_omega_jn_kn_equals_1() {
        // ω(jn, kn) = 1 for any unit normal n (CH2021 property)
        let n = Vector4::new(1.0, 2.0, 3.0, 4.0).normalize();
        let jn = apply_quat_j(&n);
        let kn = apply_quat_k(&n);
        let omega = symplectic_form(&jn, &kn);
        assert_relative_eq!(omega, 1.0, epsilon = EPS);
    }

    #[test]
    fn test_symplectic_form_antisymmetric() {
        let x = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let y = Vector4::new(5.0, 6.0, 7.0, 8.0);
        let omega_xy = symplectic_form(&x, &y);
        let omega_yx = symplectic_form(&y, &x);
        assert_relative_eq!(omega_xy, -omega_yx, epsilon = EPS);
    }

    #[test]
    fn test_symplectic_form_standard_basis() {
        let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let e2 = Vector4::new(0.0, 1.0, 0.0, 0.0);
        let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0);
        let e4 = Vector4::new(0.0, 0.0, 0.0, 1.0);

        assert_relative_eq!(symplectic_form(&e1, &e3), 1.0, epsilon = EPS);
        assert_relative_eq!(symplectic_form(&e2, &e4), 1.0, epsilon = EPS);
        assert_relative_eq!(symplectic_form(&e1, &e2), 0.0, epsilon = EPS);
        assert_relative_eq!(symplectic_form(&e3, &e4), 0.0, epsilon = EPS);
    }

    #[test]
    fn test_reeb_vector_perpendicular_to_normal() {
        let normal = Vector4::new(0.6, 0.8, 0.0, 0.0);
        let height = 1.0;
        let reeb = reeb_vector(&normal, height);
        assert_relative_eq!(reeb.dot(&normal), 0.0, epsilon = EPS);
    }

    #[test]
    fn test_reeb_vector_magnitude() {
        let normal = Vector4::new(0.6, 0.8, 0.0, 0.0);
        let height = 2.0;
        let reeb = reeb_vector(&normal, height);
        // |R| = 2/h * |Jn| = 2/h * |n| = 2/h (since n is unit)
        assert_relative_eq!(reeb.norm(), 2.0 / height, epsilon = EPS);
    }
}
