//! Symplectic geometry primitives for R^4.
//!
//! This module provides the standard symplectic structure on R^4:
//! - The complex structure J
//! - The symplectic form omega(x, y) = <Jx, y>
//! - Reeb vector computation

use nalgebra::{Matrix4, Vector4};

/// The standard complex structure J on R^4.
///
/// J acts as: J(q1, q2, p1, p2) = (-p1, -p2, q1, q2)
///
/// In matrix form:
/// ```text
/// J = | 0  0 -1  0 |
///     | 0  0  0 -1 |
///     | 1  0  0  0 |
///     | 0  1  0  0 |
/// ```
///
/// Properties:
/// - J^2 = -I (complex structure)
/// - J^T = -J (antisymmetric)
/// - omega(x, y) = <Jx, y> defines the standard symplectic form
#[inline]
pub fn j_matrix() -> Matrix4<f64> {
    #[rustfmt::skip]
    let j = Matrix4::new(
        0.0,  0.0, -1.0,  0.0,
        0.0,  0.0,  0.0, -1.0,
        1.0,  0.0,  0.0,  0.0,
        0.0,  1.0,  0.0,  0.0,
    );
    j
}

/// Apply J to a vector: J * v.
///
/// J(q1, q2, p1, p2) = (-p1, -p2, q1, q2)
#[inline]
pub fn apply_j(v: &Vector4<f64>) -> Vector4<f64> {
    // Direct computation is faster than matrix multiply
    Vector4::new(-v[2], -v[3], v[0], v[1])
}

/// The standard symplectic form on R^4.
///
/// omega(x, y) = <Jx, y> = x1*y3 + x2*y4 - x3*y1 - x4*y2
///
/// where x = (x1, x2, x3, x4) = (q1, q2, p1, p2).
///
/// Properties:
/// - Bilinear
/// - Antisymmetric: omega(x, y) = -omega(y, x)
/// - Non-degenerate
#[inline]
pub fn symplectic_form(x: &Vector4<f64>, y: &Vector4<f64>) -> f64 {
    // omega(x, y) = <Jx, y> = -x3*y1 - x4*y2 + x1*y3 + x2*y4
    // Using (q1, q2, p1, p2) indexing: x[0]=q1, x[1]=q2, x[2]=p1, x[3]=p2
    x[0] * y[2] + x[1] * y[3] - x[2] * y[0] - x[3] * y[1]
}

/// Compute the Reeb vector for a facet.
///
/// The Reeb vector p_i = (2/h_i) * J * n_i determines the direction of
/// Hamiltonian flow on facet i.
///
/// # Arguments
/// - `normal`: Unit outward normal n_i to the facet
/// - `height`: Distance h_i from origin to the facet (must be > 0)
///
/// # Returns
/// The Reeb vector p_i
#[inline]
pub fn reeb_vector(normal: &Vector4<f64>, height: f64) -> Vector4<f64> {
    debug_assert!(height > 0.0, "Height must be positive");
    apply_j(normal) * (2.0 / height)
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    #[test]
    fn test_j_matrix_squared_is_minus_identity() {
        let j = j_matrix();
        let j_squared = j * j;
        let minus_i = -Matrix4::identity();
        assert_relative_eq!(j_squared, minus_i, epsilon = 1e-15);
    }

    #[test]
    fn test_j_matrix_is_antisymmetric() {
        let j = j_matrix();
        assert_relative_eq!(j, -j.transpose(), epsilon = 1e-15);
    }

    #[test]
    fn test_apply_j() {
        let v = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let jv = apply_j(&v);
        // J(1, 2, 3, 4) = (-3, -4, 1, 2)
        assert_relative_eq!(jv, Vector4::new(-3.0, -4.0, 1.0, 2.0), epsilon = 1e-15);
    }

    #[test]
    fn test_apply_j_matches_matrix() {
        let v = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let jv_direct = apply_j(&v);
        let jv_matrix = j_matrix() * v;
        assert_relative_eq!(jv_direct, jv_matrix, epsilon = 1e-15);
    }

    #[test]
    fn test_symplectic_form_antisymmetric() {
        let x = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let y = Vector4::new(5.0, 6.0, 7.0, 8.0);
        let omega_xy = symplectic_form(&x, &y);
        let omega_yx = symplectic_form(&y, &x);
        assert_relative_eq!(omega_xy, -omega_yx, epsilon = 1e-15);
    }

    #[test]
    fn test_symplectic_form_zero_on_same() {
        let x = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let omega_xx = symplectic_form(&x, &x);
        assert_relative_eq!(omega_xx, 0.0, epsilon = 1e-15);
    }

    #[test]
    fn test_symplectic_form_bilinear() {
        let x = Vector4::new(1.0, 2.0, 3.0, 4.0);
        let y = Vector4::new(5.0, 6.0, 7.0, 8.0);
        let z = Vector4::new(0.1, 0.2, 0.3, 0.4);
        let a = 2.5;

        // omega(ax, y) = a * omega(x, y)
        assert_relative_eq!(
            symplectic_form(&(x * a), &y),
            a * symplectic_form(&x, &y),
            epsilon = 1e-14
        );

        // omega(x + z, y) = omega(x, y) + omega(z, y)
        assert_relative_eq!(
            symplectic_form(&(x + z), &y),
            symplectic_form(&x, &y) + symplectic_form(&z, &y),
            epsilon = 1e-14
        );
    }

    #[test]
    fn test_symplectic_form_standard_basis() {
        // The standard symplectic basis: (e1, e2, e3, e4) = (dq1, dq2, dp1, dp2)
        // omega(dq_i, dp_j) = delta_ij
        // omega(dq_i, dq_j) = 0
        // omega(dp_i, dp_j) = 0
        let e1 = Vector4::new(1.0, 0.0, 0.0, 0.0); // dq1
        let e2 = Vector4::new(0.0, 1.0, 0.0, 0.0); // dq2
        let e3 = Vector4::new(0.0, 0.0, 1.0, 0.0); // dp1
        let e4 = Vector4::new(0.0, 0.0, 0.0, 1.0); // dp2

        // omega(dq1, dp1) = 1
        assert_relative_eq!(symplectic_form(&e1, &e3), 1.0, epsilon = 1e-15);
        // omega(dq2, dp2) = 1
        assert_relative_eq!(symplectic_form(&e2, &e4), 1.0, epsilon = 1e-15);
        // omega(dq1, dp2) = 0
        assert_relative_eq!(symplectic_form(&e1, &e4), 0.0, epsilon = 1e-15);
        // omega(dq2, dp1) = 0
        assert_relative_eq!(symplectic_form(&e2, &e3), 0.0, epsilon = 1e-15);
        // omega(dq1, dq2) = 0
        assert_relative_eq!(symplectic_form(&e1, &e2), 0.0, epsilon = 1e-15);
        // omega(dp1, dp2) = 0
        assert_relative_eq!(symplectic_form(&e3, &e4), 0.0, epsilon = 1e-15);
    }

    #[test]
    fn test_reeb_vector_perpendicular_to_normal() {
        let normal = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let height = 1.0;
        let reeb = reeb_vector(&normal, height);

        // J*n is perpendicular to n because <Jn, n> = omega(n, n) = 0
        assert_relative_eq!(reeb.dot(&normal), 0.0, epsilon = 1e-15);
    }

    #[test]
    fn test_reeb_vector_scaling() {
        let normal = Vector4::new(0.6, 0.8, 0.0, 0.0);
        let h1 = 1.0;
        let h2 = 2.0;
        let reeb1 = reeb_vector(&normal, h1);
        let reeb2 = reeb_vector(&normal, h2);

        // p(h2) = (h1/h2) * p(h1)
        assert_relative_eq!(reeb2, reeb1 * (h1 / h2), epsilon = 1e-15);
    }
}
