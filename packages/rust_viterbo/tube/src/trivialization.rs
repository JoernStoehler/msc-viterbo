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
use crate::quaternion::{quat_frame_j, quat_frame_k};

/// Trivialize a 4D vector using normal n.
///
/// τ_n(V) = (⟨V, jn⟩, ⟨V, kn⟩)
///
/// IMPORTANT: This maps 4D vectors to 2D coordinates. It is an isomorphism
/// when restricted to a 2-face tangent space, but does NOT have a simple
/// inverse formula. Use explicit basis vectors for reconstruction.
#[inline]
pub fn trivialize(n: &Vector4<f64>, v: &Vector4<f64>) -> Vector2<f64> {
    let jn = quat_frame_j(n);
    let kn = quat_frame_k(n);
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
    let jn_exit = quat_frame_j(n_exit);
    let kn_exit = quat_frame_k(n_exit);

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
    let jn_entry = quat_frame_j(n_entry);
    let kn_entry = quat_frame_k(n_entry);

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
    let jn_exit = quat_frame_j(n_exit);
    let kn_exit = quat_frame_k(n_exit);

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
    let a3 = quat_frame_j(n_entry).dot(n_exit);
    let a4 = quat_frame_k(n_entry).dot(n_exit);

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
/// **Derivation:** For a 2×2 symplectic matrix ψ (det = 1), the trace satisfies
/// tr(ψ) = 2cos(2πρ) where ρ is the rotation number. For polytope 2-faces,
/// tr(ψ) = 2⟨n_entry, n_exit⟩ (see developer-spec-v2.md §1.12 and thesis §4.5).
/// Inverting: ρ = arccos(tr(ψ)/2) / 2π.
pub fn rotation_number_from_trace(trace: f64) -> f64 {
    // Trace should be in (-2, 2) for non-Lagrangian 2-faces
    debug_assert!(
        trace.abs() <= 2.0 + EPS,
        "trace out of valid range: {}",
        trace
    );
    // Clamp for numerical robustness
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
    use crate::quaternion::symplectic_form;
    use approx::assert_relative_eq;

    // =========================================================================
    // R1: Entry/Exit Basis Duality
    // =========================================================================

    /// Swapping entry/exit roles should produce inverse transition matrices.
    ///
    /// If ψ_{AB} = τ_B ∘ τ_A^{-1}, then ψ_{BA} = τ_A ∘ τ_B^{-1} = ψ_{AB}^{-1}.
    #[test]
    fn test_entry_exit_basis_duality() {
        let n_a = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_b = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        // Forward: A → B
        let b_entry_ab = compute_entry_basis(&n_a, &n_b).unwrap();
        let psi_ab = compute_transition_matrix_basis(&b_entry_ab, &n_b);

        // Backward: B → A
        let b_entry_ba = compute_entry_basis(&n_b, &n_a).unwrap();
        let psi_ba = compute_transition_matrix_basis(&b_entry_ba, &n_a);

        // ψ_{BA} should be inverse of ψ_{AB}
        let product = psi_ab * psi_ba;
        assert_relative_eq!(product, Matrix2::identity(), epsilon = EPS);

        // Alternative check: ψ_{AB}^{-1} = ψ_{BA}
        let psi_ab_inv = psi_ab.try_inverse().unwrap();
        assert_relative_eq!(psi_ab_inv, psi_ba, epsilon = EPS);
    }

    // =========================================================================
    // R2: Trivialization Kernel
    // =========================================================================

    /// τ_n(n) = (0, 0) and τ_n(Jn) = (0, 0) since n and Jn are perpendicular to TF.
    ///
    /// The trivialization τ_n projects onto the 2-face tangent space using
    /// {jn, kn} as coordinate axes. Both n and in = Jn are perpendicular to
    /// jn and kn (quaternion orthogonality), so they map to zero.
    #[test]
    fn test_trivialization_kernel() {
        let n = Vector4::new(1.0, 2.0, 3.0, 4.0).normalize();

        // τ_n(n) = (⟨n, jn⟩, ⟨n, kn⟩) = (0, 0)
        let tau_n = trivialize(&n, &n);
        assert_relative_eq!(tau_n, Vector2::zeros(), epsilon = EPS);

        // τ_n(Jn) = τ_n(in) = (⟨in, jn⟩, ⟨in, kn⟩) = (0, 0)
        let jn = apply_quat_i(&n); // Symplectic J = quaternion i
        let tau_jn = trivialize(&n, &jn);
        assert_relative_eq!(tau_jn, Vector2::zeros(), epsilon = EPS);
    }

    // =========================================================================
    // R3: Near-Lagrangian Handling
    // =========================================================================

    /// Test that near-Lagrangian cases (a₂ ≈ 0) are handled gracefully.
    ///
    /// A 2-face is Lagrangian when ω(n_entry, n_exit) = ⟨in_entry, n_exit⟩ = a₂ ≈ 0.
    /// The CH2021 formula divides by a₂, so this should return an error.
    #[test]
    fn test_ch2021_near_lagrangian() {
        // Construct normals where a₂ = ⟨i·n_entry, n_exit⟩ ≈ 0
        // For n_entry = (1,0,0,0), i·n_entry = (0,0,1,0)
        // For n_exit perpendicular to (0,0,1,0) in the {x,z} plane: (a,0,0,b)
        let n_entry = Vector4::new(1.0, 0.0, 0.0, 0.0);
        let n_exit = Vector4::new(0.5, 0.0, 0.0, (3.0_f64).sqrt() / 2.0); // a₂ = 0

        // Verify a₂ is indeed near zero
        let a2 = apply_quat_i(&n_entry).dot(&n_exit);
        assert!(a2.abs() < EPS, "Setup error: a2 = {} should be near 0", a2);

        // CH2021 formula should fail gracefully
        let result = compute_transition_matrix_ch2021(&n_entry, &n_exit);
        assert!(result.is_err());
        assert!(result
            .unwrap_err()
            .contains("a2 ≈ 0 indicates Lagrangian 2-face"));
    }

    // =========================================================================
    // R4: Exit Basis Symplectic Normalization
    // =========================================================================

    /// The exit basis should satisfy ω(b₁, b₂) = 1.
    ///
    /// This ensures the trivialization preserves the symplectic structure.
    #[test]
    fn test_exit_basis_symplectic() {
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let b_exit = compute_exit_basis(&n_entry, &n_exit).unwrap();

        // ω(b₁, b₂) = 1 for symplectically normalized basis
        let omega = symplectic_form(&b_exit[0], &b_exit[1]);
        assert_relative_eq!(omega, 1.0, epsilon = EPS);
    }

    /// Entry basis should also satisfy ω(b₁, b₂) = 1.
    #[test]
    fn test_entry_basis_symplectic() {
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();

        let omega = symplectic_form(&b_entry[0], &b_entry[1]);
        assert_relative_eq!(omega, 1.0, epsilon = EPS);
    }

    // =========================================================================
    // R5: Rotation Number Geometric Bounds
    // =========================================================================

    /// Rotation number ρ → 0 as normals become parallel, → 0.5 as antiparallel.
    ///
    /// ρ = arccos(⟨n_entry, n_exit⟩) / (2π)
    /// - Parallel (n·m = 1): ρ = 0
    /// - Perpendicular (n·m = 0): ρ = 0.25
    /// - Antiparallel (n·m = -1): ρ = 0.5
    #[test]
    fn test_rotation_geometric_bounds() {
        let n = Vector4::new(1.0, 0.0, 0.0, 0.0);

        // Nearly parallel: ρ → 0
        let m_parallel = Vector4::new(1.0, 1e-6, 0.0, 0.0).normalize();
        let rho_parallel = rotation_number_direct(&n, &m_parallel);
        assert!(
            rho_parallel < 0.01,
            "ρ_parallel = {} should be near 0",
            rho_parallel
        );

        // Perpendicular: ρ = 0.25
        let m_perp = Vector4::new(0.0, 1.0, 0.0, 0.0);
        let rho_perp = rotation_number_direct(&n, &m_perp);
        assert_relative_eq!(rho_perp, 0.25, epsilon = 1e-6);

        // Nearly antiparallel: ρ → 0.5
        let m_anti = Vector4::new(-1.0, 1e-6, 0.0, 0.0).normalize();
        let rho_anti = rotation_number_direct(&n, &m_anti);
        assert!(rho_anti > 0.49, "ρ_anti = {} should be near 0.5", rho_anti);
    }

    /// Test rotation bounds using trace formula.
    #[test]
    fn test_rotation_from_trace_bounds() {
        // trace = 2 → ρ = 0 (parallel)
        let rho_parallel = rotation_number_from_trace(2.0 - EPS);
        assert!(rho_parallel < 0.01, "ρ = {} for trace ≈ 2", rho_parallel);

        // trace = 0 → ρ = 0.25 (perpendicular)
        let rho_perp = rotation_number_from_trace(0.0);
        assert_relative_eq!(rho_perp, 0.25, epsilon = 1e-6);

        // trace = -2 → ρ = 0.5 (antiparallel)
        let rho_anti = rotation_number_from_trace(-2.0 + EPS);
        assert!(rho_anti > 0.49, "ρ = {} for trace ≈ -2", rho_anti);
    }

    // =========================================================================
    // R6: Basis Linear Independence
    // =========================================================================

    /// Basis vectors must be linearly independent (Gram determinant > EPS).
    ///
    /// The Gram matrix G_ij = ⟨b_i, b_j⟩ has det(G) > 0 iff linearly independent.
    #[test]
    fn test_basis_linear_independence() {
        let n_entry = Vector4::new(1.0, 1.0, 1.0, 1.0).normalize();
        let n_exit = Vector4::new(1.0, 1.0, 1.0, -1.0).normalize();

        let b_exit = compute_exit_basis(&n_entry, &n_exit).unwrap();
        let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();

        // Gram matrix for exit basis
        let g_exit = Matrix2::new(
            b_exit[0].dot(&b_exit[0]),
            b_exit[0].dot(&b_exit[1]),
            b_exit[1].dot(&b_exit[0]),
            b_exit[1].dot(&b_exit[1]),
        );
        assert!(
            g_exit.determinant() > EPS,
            "Exit basis Gram det = {} should be > EPS",
            g_exit.determinant()
        );

        // Gram matrix for entry basis
        let g_entry = Matrix2::new(
            b_entry[0].dot(&b_entry[0]),
            b_entry[0].dot(&b_entry[1]),
            b_entry[1].dot(&b_entry[0]),
            b_entry[1].dot(&b_entry[1]),
        );
        assert!(
            g_entry.determinant() > EPS,
            "Entry basis Gram det = {} should be > EPS",
            g_entry.determinant()
        );
    }

    // =========================================================================
    // R7: Random Normals Trivialization
    // =========================================================================

    /// Test trivialization with random unit normals sampled from S³.
    ///
    /// Uses proptest for deterministic random testing.
    mod random_normals {
        use super::*;
        use proptest::prelude::*;

        /// Strategy to generate random unit vectors on S³.
        fn unit_vector_s3() -> impl Strategy<Value = Vector4<f64>> {
            // Generate 4 components, then normalize
            (
                prop::num::f64::NORMAL,
                prop::num::f64::NORMAL,
                prop::num::f64::NORMAL,
                prop::num::f64::NORMAL,
            )
                .prop_filter_map("non-zero vector", |(a, b, c, d)| {
                    let v = Vector4::new(a, b, c, d);
                    let norm = v.norm();
                    if norm > 1e-10 {
                        Some(v.normalize())
                    } else {
                        None
                    }
                })
        }

        /// Strategy to generate two non-parallel, non-Lagrangian normals.
        fn valid_normal_pair() -> impl Strategy<Value = (Vector4<f64>, Vector4<f64>)> {
            (unit_vector_s3(), unit_vector_s3()).prop_filter(
                "normals must be non-parallel and non-Lagrangian",
                |(n1, n2)| {
                    let dot = n1.dot(n2).abs();
                    let a2 = apply_quat_i(n1).dot(n2).abs();
                    // Reject if too parallel (|dot| > 0.999) or too Lagrangian (|a2| < 0.01)
                    dot < 0.999 && a2 > 0.01
                },
            )
        }

        proptest! {
            /// Transition matrix should be symplectic (det = 1) for random normals.
            #[test]
            fn test_random_normals_symplectic((n_entry, n_exit) in valid_normal_pair()) {
                let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();
                let psi = compute_transition_matrix_basis(&b_entry, &n_exit);

                // Symplectic implies det = 1
                prop_assert!((psi.determinant() - 1.0).abs() < 1e-9,
                    "det(ψ) = {} should be 1", psi.determinant());
            }

            /// Trace formula should match for random normals.
            #[test]
            fn test_random_normals_trace((n_entry, n_exit) in valid_normal_pair()) {
                let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();
                let psi = compute_transition_matrix_basis(&b_entry, &n_exit);

                let expected_trace = 2.0 * n_entry.dot(&n_exit);
                prop_assert!((psi.trace() - expected_trace).abs() < 1e-9,
                    "tr(ψ) = {} should equal 2⟨n_entry, n_exit⟩ = {}",
                    psi.trace(), expected_trace);
            }

            /// Exit basis should be symplectically normalized for random normals.
            #[test]
            fn test_random_normals_exit_basis_symplectic((n_entry, n_exit) in valid_normal_pair()) {
                let b_exit = compute_exit_basis(&n_entry, &n_exit).unwrap();
                let omega = symplectic_form(&b_exit[0], &b_exit[1]);

                prop_assert!((omega - 1.0).abs() < 1e-9,
                    "ω(b₁, b₂) = {} should be 1", omega);
            }

            /// Basis vectors should lie in the 2-face tangent space.
            #[test]
            fn test_random_normals_basis_in_tf((n_entry, n_exit) in valid_normal_pair()) {
                let b_exit = compute_exit_basis(&n_entry, &n_exit).unwrap();
                let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();

                prop_assert!(validate_basis_in_tf(&b_exit, &n_entry, &n_exit),
                    "Exit basis not in TF");
                prop_assert!(validate_basis_in_tf(&b_entry, &n_entry, &n_exit),
                    "Entry basis not in TF");
            }

            /// Rotation number should be in valid range (0, 0.5) for non-degenerate cases.
            #[test]
            fn test_random_normals_rotation_range((n_entry, n_exit) in valid_normal_pair()) {
                let rho = rotation_number_direct(&n_entry, &n_exit);

                prop_assert!(rho > 0.0 && rho < 0.5,
                    "ρ = {} should be in (0, 0.5)", rho);
            }

            /// Basis method and CH2021 formula should agree for random normals.
            #[test]
            fn test_random_normals_methods_agree((n_entry, n_exit) in valid_normal_pair()) {
                let b_entry = compute_entry_basis(&n_entry, &n_exit).unwrap();
                let psi_basis = compute_transition_matrix_basis(&b_entry, &n_exit);
                let psi_ch2021 = compute_transition_matrix_ch2021(&n_entry, &n_exit).unwrap();

                for i in 0..2 {
                    for j in 0..2 {
                        prop_assert!((psi_basis[(i, j)] - psi_ch2021[(i, j)]).abs() < 1e-8,
                            "ψ_basis != ψ_ch2021 at ({}, {}): {} vs {}",
                            i, j, psi_basis[(i, j)], psi_ch2021[(i, j)]);
                    }
                }
            }
        }
    }

    // =========================================================================
    // Existing Tests (preserved)
    // =========================================================================

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
        let jn_exit = quat_frame_j(&n_exit);
        let kn_exit = quat_frame_k(&n_exit);
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
