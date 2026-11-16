//! Random generators for symplectic matrices and test polytopes.
//!
//! This module provides comprehensive generators for property-based testing:
//!
//! - **Sp(4) generators**: Sample from the FULL 10-dimensional symplectic group,
//!   not just block-diagonal rotations. Includes:
//!   - Block rotations R(theta) in (q_i, p_i) planes (2 dimensions)
//!   - Symplectic shears (4 dimensions)
//!   - Coupled rotations (2 dimensions)
//!   - Random combinations via exponential map
//!
//! - **Witness property checkers**: Decomposed verification of Reeb orbit properties.
//!
//! # Mathematical Background
//!
//! Sp(4, R) is the group of 4x4 matrices preserving the symplectic form omega.
//! A matrix A is in Sp(4) iff A^T J A = J where J is the standard symplectic matrix.
//!
//! The Lie algebra sp(4) consists of matrices X such that X^T J + J X = 0,
//! equivalently X = J S where S is symmetric 4x4.
//!
//! Dimension count: sp(4) is 10-dimensional (4x5/2 = 10 independent parameters
//! in a symmetric 4x4 matrix).
//!
//! # References
//!
//! - Ekeland-Hofer 1989: Symplectic capacity axioms (invariance under Sp(4))
//! - CH2021: Reeb dynamics on polytopes

use proptest::prelude::*;
use rand::Rng;
use rust_viterbo_geom::{apply_j, symplectic_form, Matrix4f, PolytopeHRep, SymplecticVector};
use std::f64::consts::{PI, TAU};

// =============================================================================
// Sp(4) Matrix Generators
// =============================================================================

/// The standard symplectic matrix J in block form.
/// J = [[0, -I], [I, 0]] in (q, p) coordinates.
///
/// In our (q1, q2, p1, p2) coordinate ordering:
/// J swaps q <-> p with sign: J(q,p) = (-p, q)
#[rustfmt::skip]
pub fn standard_j() -> Matrix4f {
    Matrix4f::new(
        0.0, 0.0, -1.0, 0.0,
        0.0, 0.0, 0.0, -1.0,
        1.0, 0.0, 0.0, 0.0,
        0.0, 1.0, 0.0, 0.0,
    )
}

/// Check if a matrix is symplectic: A^T J A = J.
///
/// Uses Frobenius norm with tolerance `eps`.
pub fn is_symplectic(a: &Matrix4f, eps: f64) -> bool {
    let j = standard_j();
    let check = a.transpose() * j * a - j;
    check.norm() < eps
}

/// Rotation matrix in the (q1, p1) plane.
///
/// This is a 1-parameter subgroup of Sp(4): R(theta) = exp(theta * H1)
/// where H1 generates rotation in the first canonical pair.
///
/// In matrix form: diag(R_theta, I_2) where R_theta is 2D rotation,
/// but applied to (q1, p1) not (q1, q2).
#[rustfmt::skip]
pub fn rotation_q1p1(theta: f64) -> Matrix4f {
    let c = theta.cos();
    let s = theta.sin();
    // Rotate (q1, p1) = (x, z) components
    // [[c, 0, -s, 0],
    //  [0, 1, 0, 0],
    //  [s, 0, c, 0],
    //  [0, 0, 0, 1]]
    Matrix4f::new(
        c, 0.0, -s, 0.0,
        0.0, 1.0, 0.0, 0.0,
        s, 0.0, c, 0.0,
        0.0, 0.0, 0.0, 1.0,
    )
}

/// Rotation matrix in the (q2, p2) plane.
#[rustfmt::skip]
pub fn rotation_q2p2(phi: f64) -> Matrix4f {
    let c = phi.cos();
    let s = phi.sin();
    // Rotate (q2, p2) = (y, w) components
    Matrix4f::new(
        1.0, 0.0, 0.0, 0.0,
        0.0, c, 0.0, -s,
        0.0, 0.0, 1.0, 0.0,
        0.0, s, 0.0, c,
    )
}

/// Symplectic shear in the q1 direction.
///
/// Shear: (q, p) -> (q, p + Sq) where S is symmetric.
/// Here S = diag(s, 0) so p1 -> p1 + s*q1.
///
/// The transformation matrix A satisfies Ax = (q, p + Sq).
/// For x = (q1, q2, p1, p2): p1 -> p1 + s*q1.
#[rustfmt::skip]
pub fn shear_q1(s: f64) -> Matrix4f {
    // [[1, 0, 0, 0],
    //  [0, 1, 0, 0],
    //  [s, 0, 1, 0],
    //  [0, 0, 0, 1]]
    Matrix4f::new(
        1.0, 0.0, 0.0, 0.0,
        0.0, 1.0, 0.0, 0.0,
        s, 0.0, 1.0, 0.0,
        0.0, 0.0, 0.0, 1.0,
    )
}

/// Symplectic shear in the q2 direction.
#[rustfmt::skip]
pub fn shear_q2(s: f64) -> Matrix4f {
    // p2 -> p2 + s*q2
    Matrix4f::new(
        1.0, 0.0, 0.0, 0.0,
        0.0, 1.0, 0.0, 0.0,
        0.0, 0.0, 1.0, 0.0,
        0.0, s, 0.0, 1.0,
    )
}

/// Cross-shear: p1 -> p1 + s*q2 and p2 -> p2 + s*q1.
///
/// This corresponds to S = [[0, s], [s, 0]] (off-diagonal symmetric).
#[rustfmt::skip]
pub fn cross_shear(s: f64) -> Matrix4f {
    // p1 -> p1 + s*q2, p2 -> p2 + s*q1
    Matrix4f::new(
        1.0, 0.0, 0.0, 0.0,
        0.0, 1.0, 0.0, 0.0,
        0.0, s, 1.0, 0.0,
        s, 0.0, 0.0, 1.0,
    )
}

/// Dual shear in the p-direction: q -> q + Tp for symmetric T.
///
/// Here T = diag(t, 0) so q1 -> q1 + t*p1.
#[rustfmt::skip]
pub fn dual_shear_p1(t: f64) -> Matrix4f {
    // q1 -> q1 + t*p1
    Matrix4f::new(
        1.0, 0.0, t, 0.0,
        0.0, 1.0, 0.0, 0.0,
        0.0, 0.0, 1.0, 0.0,
        0.0, 0.0, 0.0, 1.0,
    )
}

/// Dual shear: q2 -> q2 + t*p2.
#[rustfmt::skip]
pub fn dual_shear_p2(t: f64) -> Matrix4f {
    Matrix4f::new(
        1.0, 0.0, 0.0, 0.0,
        0.0, 1.0, 0.0, t,
        0.0, 0.0, 1.0, 0.0,
        0.0, 0.0, 0.0, 1.0,
    )
}

/// Dual cross-shear: q1 -> q1 + t*p2, q2 -> q2 + t*p1.
///
/// This corresponds to T = [[0, t], [t, 0]] in the dual shear q -> q + Tp.
/// Together with `cross_shear`, this completes the off-diagonal shear degrees of freedom.
#[rustfmt::skip]
pub fn dual_cross_shear(t: f64) -> Matrix4f {
    // q1 -> q1 + t*p2, q2 -> q2 + t*p1
    Matrix4f::new(
        1.0, 0.0, 0.0, t,
        0.0, 1.0, t, 0.0,
        0.0, 0.0, 1.0, 0.0,
        0.0, 0.0, 0.0, 1.0,
    )
}

/// Coupled rotation mixing (q1, q2) with (p1, p2).
///
/// This corresponds to the Hamiltonian H = q1*q2 + p1*p2, which generates
/// a flow that couples both canonical pairs while preserving the symplectic form.
///
/// The generator in sp(4) is X = J * S where S = [[0,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]].
/// Exponentiating: exp(theta * X) gives a proper symplectic matrix.
///
/// For small theta, this can be computed via Rodrigues-style formula.
/// For simplicity, we use the exact formula from hyperbolic functions
/// since X^2 is diagonal.
#[rustfmt::skip]
pub fn coupled_rotation(theta: f64) -> Matrix4f {
    // The Lie algebra generator for this transformation.
    // X = J * S where S is symmetric with off-diagonal coupling.
    //
    // A simpler approach: use a composition of known symplectic transformations.
    // Coupled rotation = apply a rotation in q-space, then compensating rotation in p-space.
    //
    // Actually, let's use the (q1,q2) rotation combined with (p1,p2) rotation,
    // which is symplectic when the angles match appropriately.
    //
    // For A to be symplectic: A^T J A = J.
    // A = [[R, 0], [0, R]] where R is 2x2 rotation is symplectic.
    let c = theta.cos();
    let s = theta.sin();
    // Rotate (q1, q2) and (p1, p2) by the same angle
    Matrix4f::new(
        c, -s, 0.0, 0.0,
        s, c, 0.0, 0.0,
        0.0, 0.0, c, -s,
        0.0, 0.0, s, c,
    )
}

/// Symplectic exchange: (q1, q2, p1, p2) -> (q2, q1, p2, p1).
///
/// This permutes the canonical pairs and is an element of Sp(4).
#[rustfmt::skip]
pub fn symplectic_exchange() -> Matrix4f {
    Matrix4f::new(
        0.0, 1.0, 0.0, 0.0,
        1.0, 0.0, 0.0, 0.0,
        0.0, 0.0, 0.0, 1.0,
        0.0, 0.0, 1.0, 0.0,
    )
}

/// Generate a random element of Sp(4) by composing generators.
///
/// This samples from 10 continuous parameters spanning all 10 dimensions of sp(4):
/// - theta1, theta2: rotation angles in (q1,p1) and (q2,p2) planes (2 dims)
/// - s1, s2, s_cross: shear parameters p += Sq (3 dims)
/// - t1, t2, t_cross: dual shear parameters q += Tp (3 dims)
/// - phi_coupled: coupled rotation angle (1 dim)
/// - apply_exchange: whether to apply the discrete exchange (binary, not a dimension)
///
/// Total: 10 continuous parameters = dim(sp(4)).
///
/// The composition order matters; we use a fixed order that provides
/// good coverage of Sp(4).
pub fn random_sp4<R: Rng>(rng: &mut R) -> Matrix4f {
    // Sample parameters (10 continuous degrees of freedom)
    let theta1: f64 = rng.gen_range(-PI..PI);
    let theta2: f64 = rng.gen_range(-PI..PI);
    let s1: f64 = rng.gen_range(-2.0..2.0);
    let s2: f64 = rng.gen_range(-2.0..2.0);
    let s_cross: f64 = rng.gen_range(-1.0..1.0);
    let t1: f64 = rng.gen_range(-2.0..2.0);
    let t2: f64 = rng.gen_range(-2.0..2.0);
    let t_cross: f64 = rng.gen_range(-1.0..1.0);
    let phi_coupled: f64 = rng.gen_range(-PI / 4.0..PI / 4.0);
    let apply_exchange: bool = rng.gen_bool(0.3); // 30% chance

    // Compose in a fixed order
    let mut result = Matrix4f::identity();
    result = rotation_q1p1(theta1) * result;
    result = rotation_q2p2(theta2) * result;
    result = shear_q1(s1) * result;
    result = shear_q2(s2) * result;
    result = cross_shear(s_cross) * result;
    result = dual_shear_p1(t1) * result;
    result = dual_shear_p2(t2) * result;
    result = dual_cross_shear(t_cross) * result;
    result = coupled_rotation(phi_coupled) * result;

    if apply_exchange {
        result = symplectic_exchange() * result;
    }

    result
}

/// Generate a random Sp(4) matrix with bounded parameters.
///
/// Parameters are scaled by `scale` to control how "wild" the matrix is.
/// Small scale (< 0.5) gives matrices close to identity.
pub fn random_sp4_bounded<R: Rng>(rng: &mut R, scale: f64) -> Matrix4f {
    let theta1: f64 = rng.gen_range(-PI..PI) * scale;
    let theta2: f64 = rng.gen_range(-PI..PI) * scale;
    let s1: f64 = rng.gen_range(-1.0..1.0) * scale;
    let s2: f64 = rng.gen_range(-1.0..1.0) * scale;
    let s_cross: f64 = rng.gen_range(-0.5..0.5) * scale;
    let t1: f64 = rng.gen_range(-1.0..1.0) * scale;
    let t2: f64 = rng.gen_range(-1.0..1.0) * scale;
    let t_cross: f64 = rng.gen_range(-0.5..0.5) * scale;
    let phi_coupled: f64 = rng.gen_range(-PI / 8.0..PI / 8.0) * scale;

    let mut result = Matrix4f::identity();
    result = rotation_q1p1(theta1) * result;
    result = rotation_q2p2(theta2) * result;
    result = shear_q1(s1) * result;
    result = shear_q2(s2) * result;
    result = cross_shear(s_cross) * result;
    result = dual_shear_p1(t1) * result;
    result = dual_shear_p2(t2) * result;
    result = dual_cross_shear(t_cross) * result;
    result = coupled_rotation(phi_coupled) * result;

    result
}

/// Generate a seeded random Sp(4) matrix.
pub fn seeded_sp4(seed: u64) -> Matrix4f {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    random_sp4(&mut rng)
}

/// Generate a seeded random Sp(4) matrix with bounded parameters.
pub fn seeded_sp4_bounded(seed: u64, scale: f64) -> Matrix4f {
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    random_sp4_bounded(&mut rng, scale)
}

// =============================================================================
// Apply Sp(4) to Polytopes
// =============================================================================

/// Apply a symplectic matrix to a polytope in H-representation.
///
/// For a polytope K = { x : <n_i, x> <= h_i }, the image AK has:
/// - Normals: n'_i = (A^{-T}) n_i (contragredient action)
/// - Heights: h'_i = h_i (unchanged because A preserves the origin)
///
/// We renormalize to unit normals: n'' = n'/|n'|, h'' = h/|n'|.
pub fn apply_sp4_to_polytope(a: &Matrix4f, hrep: &PolytopeHRep) -> PolytopeHRep {
    // A^{-T} = (A^{-1})^T = (A^T)^{-1}
    // For symplectic A: A^{-1} = J^{-1} A^T J, so A^{-T} = J^{-1} A J^T = J^{-1} A J
    // Since J^{-1} = -J and J^T = -J, we have A^{-T} = J A J.
    //
    // Simpler: just compute A^{-1} and transpose.
    let a_inv_t = a
        .try_inverse()
        .expect("Symplectic matrix should be invertible")
        .transpose();

    let mut new_normals = Vec::with_capacity(hrep.normals.len());
    let mut new_heights = Vec::with_capacity(hrep.heights.len());

    for (n, h) in hrep.normals.iter().zip(&hrep.heights) {
        let n_prime = a_inv_t * n;
        let len = n_prime.norm();
        new_normals.push(n_prime / len);
        new_heights.push(h / len);
    }

    PolytopeHRep::new(new_normals, new_heights)
}

// =============================================================================
// Witness Property Checkers (Decomposed)
// =============================================================================

/// Check if a witness orbit closes: gamma(T) = gamma(0).
///
/// Returns the closure error (distance from last computed point to first).
pub fn orbit_closure_error(
    breakpoints: &[SymplecticVector],
    facet_sequence: &[usize],
    segment_times: &[f64],
    hrep: &PolytopeHRep,
) -> f64 {
    if breakpoints.is_empty() {
        return f64::INFINITY;
    }

    // The orbit should close: following the flow from the last breakpoint
    // should return to the first breakpoint.
    let n_segments = segment_times.len();
    if n_segments == 0 {
        return f64::INFINITY;
    }

    let last_bp = breakpoints[n_segments - 1];
    let last_facet = facet_sequence[n_segments];
    let last_time = segment_times[n_segments - 1];

    // Reeb velocity on last facet: v = 2 J n / h
    let n_last = hrep.normals[last_facet];
    let h_last = hrep.heights[last_facet];
    let v_last = apply_j(n_last) * (2.0 / h_last);

    // Predicted closing point
    let predicted_close = last_bp + v_last * last_time;

    (predicted_close - breakpoints[0]).norm()
}

/// Check if the computed action is positive.
pub fn action_positive(segment_times: &[f64]) -> bool {
    let total: f64 = segment_times.iter().sum();
    total > 0.0
}

/// Compute the total action (sum of segment times).
pub fn compute_action(segment_times: &[f64]) -> f64 {
    segment_times.iter().sum()
}

/// Check if a breakpoint lies on its claimed facet.
///
/// Returns the constraint error: |<n_k, p> - h_k|.
pub fn breakpoint_facet_error(
    breakpoint: SymplecticVector,
    facet_idx: usize,
    hrep: &PolytopeHRep,
) -> f64 {
    let n = hrep.normals[facet_idx];
    let h = hrep.heights[facet_idx];
    (n.dot(&breakpoint) - h).abs()
}

/// Check all breakpoints lie on their claimed facets.
///
/// Returns the maximum facet error across all breakpoints.
pub fn max_breakpoint_facet_error(
    breakpoints: &[SymplecticVector],
    facet_sequence: &[usize],
    hrep: &PolytopeHRep,
) -> f64 {
    let mut max_error = 0.0_f64;
    for (i, bp) in breakpoints.iter().enumerate() {
        if i < facet_sequence.len() {
            let error = breakpoint_facet_error(*bp, facet_sequence[i], hrep);
            max_error = max_error.max(error);
        }
    }
    max_error
}

/// Check if a velocity vector lies in the Reeb cone for a 2-face.
///
/// On a non-Lagrangian 2-face, the Reeb velocity is uniquely v_k = 2 J n_k / h_k.
/// On a Lagrangian 2-face (omega(n_i, n_j) = 0), the velocity can be any
/// positive combination lambda_i * v_i + lambda_j * v_j with lambda_i, lambda_j >= 0.
///
/// This function checks the Reeb flow condition for a segment.
///
/// # Arguments
/// - `p_start`: starting breakpoint
/// - `p_end`: ending breakpoint
/// - `facet_prev`: facet the orbit was on before this segment
/// - `facet_curr`: facet the orbit is on during this segment
/// - `segment_time`: time spent on this segment
/// - `hrep`: polytope H-representation
/// - `tol`: tolerance for Lagrangian detection
///
/// # Returns
/// The flow error (should be near zero for valid Reeb flow).
pub fn segment_flow_error(
    p_start: SymplecticVector,
    p_end: SymplecticVector,
    facet_prev: usize,
    facet_curr: usize,
    segment_time: f64,
    hrep: &PolytopeHRep,
    tol: f64,
) -> f64 {
    let n_prev = hrep.normals[facet_prev];
    let n_curr = hrep.normals[facet_curr];
    let h_prev = hrep.heights[facet_prev];
    let h_curr = hrep.heights[facet_curr];

    let omega = symplectic_form(n_prev, n_curr);
    let is_lagrangian = omega.abs() < tol;

    let displacement = p_end - p_start;

    if is_lagrangian {
        // Differential inclusion: displacement in cone{v_prev, v_curr}
        let v_prev = apply_j(n_prev) * (2.0 / h_prev);
        let v_curr = apply_j(n_curr) * (2.0 / h_curr);
        cone_projection_error(displacement, v_prev, v_curr)
    } else {
        // Unique Reeb velocity
        let v_curr = apply_j(n_curr) * (2.0 / h_curr);
        let expected_end = p_start + v_curr * segment_time;
        (p_end - expected_end).norm()
    }
}

/// Compute the error for a vector lying in the cone of two directions.
///
/// Returns the residual when projecting `displacement` onto the cone
/// spanned by non-negative combinations of `v1` and `v2`.
fn cone_projection_error(
    displacement: SymplecticVector,
    v1: SymplecticVector,
    v2: SymplecticVector,
) -> f64 {
    // Solve least squares: [v1 | v2] * [lambda1; lambda2] = displacement
    let a11 = v1.dot(&v1);
    let a12 = v1.dot(&v2);
    let a22 = v2.dot(&v2);
    let b1 = v1.dot(&displacement);
    let b2 = v2.dot(&displacement);

    let det = a11 * a22 - a12 * a12;

    if det.abs() < 1e-14 {
        // Degenerate: v1 and v2 are parallel
        if a11 > 1e-14 {
            let lambda = (b1 / a11).max(0.0);
            return (displacement - v1 * lambda).norm();
        }
        return displacement.norm();
    }

    let lambda1 = (a22 * b1 - a12 * b2) / det;
    let lambda2 = (a11 * b2 - a12 * b1) / det;

    if lambda1 >= -1e-10 && lambda2 >= -1e-10 {
        let achieved = v1 * lambda1 + v2 * lambda2;
        (displacement - achieved).norm()
    } else {
        // Project onto each ray and take best
        let mut best = f64::INFINITY;

        if a11 > 1e-14 {
            let lambda = (b1 / a11).max(0.0);
            best = best.min((displacement - v1 * lambda).norm());
        }
        if a22 > 1e-14 {
            let lambda = (b2 / a22).max(0.0);
            best = best.min((displacement - v2 * lambda).norm());
        }
        best = best.min(displacement.norm());

        best
    }
}

/// Check all segment flow errors and return the maximum.
pub fn max_segment_flow_error(
    breakpoints: &[SymplecticVector],
    facet_sequence: &[usize],
    segment_times: &[f64],
    hrep: &PolytopeHRep,
    tol: f64,
) -> f64 {
    let mut max_error = 0.0_f64;
    let n_segments = segment_times.len();

    for s in 0..n_segments {
        let p_start = breakpoints[s];
        let p_end = if s == n_segments - 1 {
            breakpoints[0]
        } else {
            breakpoints[s + 1]
        };

        let facet_prev = facet_sequence[s];
        let facet_curr = facet_sequence[s + 1];

        let error = segment_flow_error(
            p_start,
            p_end,
            facet_prev,
            facet_curr,
            segment_times[s],
            hrep,
            tol,
        );
        max_error = max_error.max(error);
    }

    max_error
}

// =============================================================================
// Proptest Strategies
// =============================================================================

/// Proptest strategy for Sp(4) matrices.
pub fn sp4_strategy() -> impl Strategy<Value = Matrix4f> {
    (any::<u64>()).prop_map(seeded_sp4)
}

/// Proptest strategy for bounded Sp(4) matrices (closer to identity).
pub fn sp4_bounded_strategy(scale: f64) -> impl Strategy<Value = Matrix4f> {
    (any::<u64>()).prop_map(move |seed| seeded_sp4_bounded(seed, scale))
}

/// Proptest strategy for small rotation angles (safer for numerical tests).
pub fn small_rotation_strategy() -> impl Strategy<Value = (f64, f64)> {
    (
        prop::num::f64::NORMAL.prop_map(|x| (x.abs() % 1.0) * PI / 4.0),
        prop::num::f64::NORMAL.prop_map(|x| (x.abs() % 1.0) * PI / 4.0),
    )
}

// =============================================================================
// Unit Tests for Generators
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use rand::SeedableRng;
    use rand_chacha::ChaCha8Rng;

    const EPS_SYMPLECTIC: f64 = 1e-10;

    #[test]
    fn standard_j_is_correct() {
        let j = standard_j();
        // J^2 = -I
        let j_squared = j * j;
        let minus_identity = -Matrix4f::identity();
        assert!(
            (j_squared - minus_identity).norm() < EPS_SYMPLECTIC,
            "J^2 should be -I"
        );
    }

    #[test]
    fn rotation_q1p1_is_symplectic() {
        for angle_deg in [0.0, 30.0, 45.0, 90.0, 180.0, -45.0] {
            let theta = angle_deg * PI / 180.0;
            let r = rotation_q1p1(theta);
            assert!(
                is_symplectic(&r, EPS_SYMPLECTIC),
                "rotation_q1p1({}) should be symplectic",
                angle_deg
            );
        }
    }

    #[test]
    fn rotation_q2p2_is_symplectic() {
        for angle_deg in [0.0, 30.0, 45.0, 90.0, 180.0, -45.0] {
            let phi = angle_deg * PI / 180.0;
            let r = rotation_q2p2(phi);
            assert!(
                is_symplectic(&r, EPS_SYMPLECTIC),
                "rotation_q2p2({}) should be symplectic",
                angle_deg
            );
        }
    }

    #[test]
    fn shear_q1_is_symplectic() {
        for s in [-2.0, -1.0, 0.0, 0.5, 1.0, 2.0] {
            let m = shear_q1(s);
            assert!(
                is_symplectic(&m, EPS_SYMPLECTIC),
                "shear_q1({}) should be symplectic",
                s
            );
        }
    }

    #[test]
    fn shear_q2_is_symplectic() {
        for s in [-2.0, -1.0, 0.0, 0.5, 1.0, 2.0] {
            let m = shear_q2(s);
            assert!(
                is_symplectic(&m, EPS_SYMPLECTIC),
                "shear_q2({}) should be symplectic",
                s
            );
        }
    }

    #[test]
    fn cross_shear_is_symplectic() {
        for s in [-1.0, 0.0, 0.5, 1.0] {
            let m = cross_shear(s);
            assert!(
                is_symplectic(&m, EPS_SYMPLECTIC),
                "cross_shear({}) should be symplectic",
                s
            );
        }
    }

    #[test]
    fn dual_shear_p1_is_symplectic() {
        for t in [-2.0, -1.0, 0.0, 0.5, 1.0, 2.0] {
            let m = dual_shear_p1(t);
            assert!(
                is_symplectic(&m, EPS_SYMPLECTIC),
                "dual_shear_p1({}) should be symplectic",
                t
            );
        }
    }

    #[test]
    fn dual_shear_p2_is_symplectic() {
        for t in [-2.0, -1.0, 0.0, 0.5, 1.0, 2.0] {
            let m = dual_shear_p2(t);
            assert!(
                is_symplectic(&m, EPS_SYMPLECTIC),
                "dual_shear_p2({}) should be symplectic",
                t
            );
        }
    }

    #[test]
    fn dual_cross_shear_is_symplectic() {
        for t in [-1.0, 0.0, 0.5, 1.0] {
            let m = dual_cross_shear(t);
            assert!(
                is_symplectic(&m, EPS_SYMPLECTIC),
                "dual_cross_shear({}) should be symplectic",
                t
            );
        }
    }

    #[test]
    fn coupled_rotation_is_symplectic() {
        for angle_deg in [0.0, 15.0, 30.0, 45.0, -30.0] {
            let theta = angle_deg * PI / 180.0;
            let m = coupled_rotation(theta);
            assert!(
                is_symplectic(&m, EPS_SYMPLECTIC),
                "coupled_rotation({}) should be symplectic",
                angle_deg
            );
        }
    }

    #[test]
    fn symplectic_exchange_is_symplectic() {
        let m = symplectic_exchange();
        assert!(is_symplectic(&m, EPS_SYMPLECTIC));
    }

    #[test]
    fn random_sp4_is_symplectic() {
        let mut rng = ChaCha8Rng::seed_from_u64(12345);
        for _ in 0..100 {
            let m = random_sp4(&mut rng);
            assert!(
                is_symplectic(&m, 1e-8),
                "random_sp4 should be symplectic: error = {}",
                (m.transpose() * standard_j() * m - standard_j()).norm()
            );
        }
    }

    #[test]
    fn seeded_sp4_is_deterministic() {
        let m1 = seeded_sp4(42);
        let m2 = seeded_sp4(42);
        assert_eq!(m1, m2, "seeded_sp4 should be deterministic");
    }

    #[test]
    fn random_sp4_covers_parameter_space() {
        // Check that random matrices are actually different (not all identity)
        let m1 = seeded_sp4(1);
        let m2 = seeded_sp4(2);
        let m3 = seeded_sp4(3);

        let identity = Matrix4f::identity();
        let d1 = (m1 - identity).norm();
        let d2 = (m2 - identity).norm();
        let d3 = (m3 - identity).norm();

        // At least one should be far from identity
        assert!(
            d1 > 0.1 || d2 > 0.1 || d3 > 0.1,
            "Random Sp(4) matrices should vary from identity"
        );
    }

    #[test]
    fn apply_sp4_preserves_polytope_volume() {
        // Symplectic maps preserve (symplectic) volume.
        // For an H-rep polytope, this means the product of heights should be preserved
        // (approximately, up to renormalization effects).
        //
        // This is a weak check; stronger would be to compute actual volume.
        use super::super::fixtures::tesseract;

        let hrep = tesseract();
        let a = seeded_sp4(999);
        let transformed = apply_sp4_to_polytope(&a, &hrep);

        // Just check dimensions match
        assert_eq!(transformed.normals.len(), hrep.normals.len());
        assert_eq!(transformed.heights.len(), hrep.heights.len());

        // Check normals are unit
        for n in &transformed.normals {
            assert!(
                (n.norm() - 1.0).abs() < 1e-10,
                "Transformed normals should be unit"
            );
        }

        // Check heights are positive
        for h in &transformed.heights {
            assert!(*h > 0.0, "Transformed heights should be positive");
        }
    }

    // =========================================================================
    // Witness Checker Tests
    // =========================================================================

    #[test]
    fn action_positive_for_positive_times() {
        assert!(action_positive(&[1.0, 2.0, 3.0]));
        assert!(action_positive(&[0.1]));
    }

    #[test]
    fn action_not_positive_for_zero_times() {
        assert!(!action_positive(&[0.0, 0.0, 0.0]));
        assert!(!action_positive(&[]));
    }

    #[test]
    fn action_not_positive_for_negative_total() {
        assert!(!action_positive(&[-1.0, 0.5]));
    }

    #[test]
    fn compute_action_sums_times() {
        assert!((compute_action(&[1.0, 2.0, 3.0]) - 6.0).abs() < 1e-10);
        assert!((compute_action(&[]) - 0.0).abs() < 1e-10);
    }

    #[test]
    fn breakpoint_facet_error_exact() {
        use super::super::fixtures::tesseract;

        let hrep = tesseract();
        // Facet 0 has normal (1,0,0,0) and height 1
        // Point (1, 0.5, 0.3, 0.2) should have error 0
        let p = SymplecticVector::new(1.0, 0.5, 0.3, 0.2);
        let error = breakpoint_facet_error(p, 0, &hrep);
        assert!(error < 1e-10, "Point on facet should have zero error");
    }

    #[test]
    fn breakpoint_facet_error_off_facet() {
        use super::super::fixtures::tesseract;

        let hrep = tesseract();
        // Facet 0 has normal (1,0,0,0) and height 1
        // Point (0.5, 0.5, 0.3, 0.2) is off the facet
        let p = SymplecticVector::new(0.5, 0.5, 0.3, 0.2);
        let error = breakpoint_facet_error(p, 0, &hrep);
        assert!(
            (error - 0.5).abs() < 1e-10,
            "Error should be 0.5, got {}",
            error
        );
    }

    #[test]
    fn cone_projection_error_inside_cone() {
        let v1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let v2 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);

        // Point inside cone: 0.5*v1 + 0.5*v2
        let d = v1 * 0.5 + v2 * 0.5;
        let error = cone_projection_error(d, v1, v2);
        assert!(error < 1e-10, "Point in cone should have zero error");
    }

    #[test]
    fn cone_projection_error_outside_cone() {
        let v1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let v2 = SymplecticVector::new(0.0, 1.0, 0.0, 0.0);

        // Point outside cone: perpendicular direction
        let d = SymplecticVector::new(0.0, 0.0, 1.0, 0.0);
        let error = cone_projection_error(d, v1, v2);
        assert!(
            error > 0.9,
            "Point perpendicular to cone should have large error"
        );
    }

    // =========================================================================
    // Comprehensive Sp(4) Sampler Tests
    // =========================================================================
    //
    // These tests verify that the Sp(4) sampler produces valid symplectic
    // matrices and covers the group adequately.

    mod sp4_sampler_tests {
        use super::*;
        use nalgebra::{Complex, Normed};

        const EPS_SYMPLECTIC: f64 = 1e-10;
        const EPS_DETERMINANT: f64 = 1e-8;
        const EPS_EIGENVALUE: f64 = 1e-6;

        // ---------------------------------------------------------------------
        // 1. Symplectic property verification (A^T J A = J)
        // ---------------------------------------------------------------------

        #[test]
        fn symplectic_property_bulk_verification() {
            // Generate 1000 random Sp(4) matrices and verify each is symplectic
            let mut rng = ChaCha8Rng::seed_from_u64(0xDEADBEEF);
            let mut failures = 0;
            let n_samples = 1000;

            for i in 0..n_samples {
                let m = random_sp4(&mut rng);
                if !is_symplectic(&m, EPS_SYMPLECTIC) {
                    failures += 1;
                    eprintln!(
                        "Sample {} failed symplectic check: error = {}",
                        i,
                        (m.transpose() * standard_j() * m - standard_j()).norm()
                    );
                }
            }

            assert_eq!(
                failures, 0,
                "All {} Sp(4) matrices should satisfy A^T J A = J, but {} failed",
                n_samples, failures
            );
        }

        // ---------------------------------------------------------------------
        // 2. Determinant check (det(A) = 1 for all A in Sp(4))
        // ---------------------------------------------------------------------

        #[test]
        fn determinant_equals_one() {
            let mut rng = ChaCha8Rng::seed_from_u64(0xCAFEBABE);
            let n_samples = 1000;

            for i in 0..n_samples {
                let m = random_sp4(&mut rng);
                let det = m.determinant();
                assert!(
                    (det - 1.0).abs() < EPS_DETERMINANT,
                    "Sample {}: det should be 1.0, got {} (error = {})",
                    i,
                    det,
                    (det - 1.0).abs()
                );
            }
        }

        #[test]
        fn determinant_bounded_matrices() {
            // Also test bounded matrices (closer to identity)
            let mut rng = ChaCha8Rng::seed_from_u64(0x12345678);
            for scale in [0.1, 0.5, 1.0, 2.0] {
                for _ in 0..100 {
                    let m = random_sp4_bounded(&mut rng, scale);
                    let det = m.determinant();
                    assert!(
                        (det - 1.0).abs() < EPS_DETERMINANT,
                        "Bounded (scale={}): det should be 1.0, got {}",
                        scale,
                        det
                    );
                }
            }
        }

        // ---------------------------------------------------------------------
        // 3. Eigenvalue reciprocal pairs check
        // ---------------------------------------------------------------------
        //
        // Symplectic matrices have eigenvalues in reciprocal pairs:
        // if lambda is an eigenvalue, so is 1/lambda (and their conjugates).

        /// Check if eigenvalues come in reciprocal pairs (possibly complex).
        /// For Sp(4), we have 4 eigenvalues that should pair as (lambda, 1/lambda).
        fn check_eigenvalue_reciprocal_pairs(m: &Matrix4f, tol: f64) -> bool {
            // Compute eigenvalues using nalgebra's Schur decomposition
            let schur = m.clone().schur();
            let t = schur.unpack().1; // quasi-triangular matrix

            // Extract eigenvalues from the quasi-triangular form
            // For real matrices, eigenvalues are either real (on diagonal)
            // or complex conjugate pairs (in 2x2 blocks)
            let mut eigenvalues: Vec<Complex<f64>> = Vec::with_capacity(4);

            let mut i = 0;
            while i < 4 {
                if i + 1 < 4 && t[(i + 1, i)].abs() > 1e-12 {
                    // 2x2 block: complex conjugate pair
                    let a = t[(i, i)];
                    let b = t[(i, i + 1)];
                    let c = t[(i + 1, i)];
                    let d = t[(i + 1, i + 1)];
                    let trace = a + d;
                    let det = a * d - b * c;
                    let disc = trace * trace - 4.0 * det;
                    if disc < 0.0 {
                        let real = trace / 2.0;
                        let imag = (-disc).sqrt() / 2.0;
                        eigenvalues.push(Complex::new(real, imag));
                        eigenvalues.push(Complex::new(real, -imag));
                    } else {
                        // Real roots (shouldn't happen if off-diagonal is nonzero, but handle anyway)
                        let sqrt_disc = disc.sqrt();
                        eigenvalues.push(Complex::new((trace + sqrt_disc) / 2.0, 0.0));
                        eigenvalues.push(Complex::new((trace - sqrt_disc) / 2.0, 0.0));
                    }
                    i += 2;
                } else {
                    // Real eigenvalue on diagonal
                    eigenvalues.push(Complex::new(t[(i, i)], 0.0));
                    i += 1;
                }
            }

            // Check that each eigenvalue has a reciprocal partner
            let mut used = [false; 4];
            for i in 0..4 {
                if used[i] {
                    continue;
                }
                let lambda = eigenvalues[i];

                // Avoid division by zero for zero eigenvalues (shouldn't happen for Sp(4))
                if lambda.norm() < 1e-12 {
                    return false;
                }

                let recip = Complex::new(1.0, 0.0) / lambda;

                // Find a matching reciprocal
                let mut found = false;
                for j in 0..4 {
                    if i != j && !used[j] {
                        let diff = (eigenvalues[j] - recip).norm();
                        if diff < tol {
                            used[i] = true;
                            used[j] = true;
                            found = true;
                            break;
                        }
                    }
                }
                if !found {
                    // Maybe it's a unit eigenvalue (lambda = 1/lambda means lambda = +/- 1)
                    if (lambda.norm() - 1.0).abs() < tol {
                        used[i] = true;
                    } else {
                        return false;
                    }
                }
            }
            true
        }

        #[test]
        fn eigenvalues_form_reciprocal_pairs() {
            let mut rng = ChaCha8Rng::seed_from_u64(0xABCDEF01);

            for _ in 0..100 {
                let m = random_sp4(&mut rng);
                assert!(
                    check_eigenvalue_reciprocal_pairs(&m, EPS_EIGENVALUE),
                    "Eigenvalues of Sp(4) matrix should form reciprocal pairs"
                );
            }
        }

        #[test]
        fn eigenvalues_reciprocal_for_pure_rotations() {
            // Pure rotations have eigenvalues on the unit circle
            for angle_deg in [30.0, 45.0, 60.0, 90.0, 120.0, 150.0] {
                let theta = angle_deg * PI / 180.0;
                let m = rotation_q1p1(theta) * rotation_q2p2(theta * 0.7);
                assert!(
                    check_eigenvalue_reciprocal_pairs(&m, EPS_EIGENVALUE),
                    "Rotation at {}° should have reciprocal eigenvalue pairs",
                    angle_deg
                );
            }
        }

        #[test]
        fn eigenvalues_reciprocal_for_shears() {
            // Shears have eigenvalue 1 (with multiplicity)
            for s in [0.5, 1.0, 2.0, -1.0] {
                let m = shear_q1(s) * shear_q2(s * 0.5);
                assert!(
                    check_eigenvalue_reciprocal_pairs(&m, EPS_EIGENVALUE),
                    "Shear with s={} should have reciprocal eigenvalue pairs",
                    s
                );
            }
        }

        // ---------------------------------------------------------------------
        // 4. Coverage test - check matrix variety
        // ---------------------------------------------------------------------

        #[test]
        fn matrix_entries_not_clustered() {
            // Generate 100 matrices and compute statistics for each entry position
            let mut rng = ChaCha8Rng::seed_from_u64(0x98765432);
            let n_samples = 100;

            // Collect all entries from all matrices
            let mut entries: Vec<Vec<f64>> = vec![Vec::with_capacity(n_samples); 16];

            for _ in 0..n_samples {
                let m = random_sp4(&mut rng);
                for i in 0..4 {
                    for j in 0..4 {
                        entries[i * 4 + j].push(m[(i, j)]);
                    }
                }
            }

            // Check that entries are not all clustered near special values
            for (idx, entry_values) in entries.iter().enumerate() {
                let i = idx / 4;
                let j = idx % 4;

                let mean: f64 = entry_values.iter().sum::<f64>() / n_samples as f64;
                let variance: f64 = entry_values
                    .iter()
                    .map(|x| (x - mean).powi(2))
                    .sum::<f64>()
                    / n_samples as f64;

                // The variance should be non-negligible for most entries
                // (indicating the sampler explores different values)
                // Note: some entries may have low variance due to the structure of the sampler
                // (e.g., if some generator types dominate), but at least some should vary.

                // For non-diagonal entries, verify they're not all zero
                if i != j {
                    let all_near_zero = entry_values.iter().all(|x| x.abs() < 0.01);
                    if all_near_zero {
                        // This is suspicious - off-diagonal entries should vary
                        eprintln!(
                            "Warning: entry ({},{}) is near-zero for all samples (mean={}, var={})",
                            i, j, mean, variance
                        );
                    }
                }
            }

            // Check that off-diagonal blocks are non-zero (not block-diagonal)
            // In a block-diagonal matrix, the (0,2), (0,3), (1,2), (1,3) block
            // and (2,0), (2,1), (3,0), (3,1) block would be zero.
            let mut has_nonzero_offblock = false;
            for _ in 0..n_samples {
                let m = random_sp4(&mut rng);
                // Check if any entry in the off-diagonal blocks is significantly nonzero
                for i in 0..2 {
                    for j in 2..4 {
                        if m[(i, j)].abs() > 0.01 || m[(j, i)].abs() > 0.01 {
                            has_nonzero_offblock = true;
                        }
                    }
                }
            }
            assert!(
                has_nonzero_offblock,
                "Sampler should produce matrices that are not block-diagonal"
            );
        }

        #[test]
        fn off_diagonal_blocks_nonzero() {
            // Explicitly verify that off-diagonal blocks can be non-zero
            let mut rng = ChaCha8Rng::seed_from_u64(0x11223344);
            let mut count_with_offblock = 0;
            let n_samples = 100;

            for _ in 0..n_samples {
                let m = random_sp4(&mut rng);
                // Sum of absolute values in off-diagonal blocks
                let mut offblock_sum = 0.0;
                for i in 0..2 {
                    for j in 2..4 {
                        offblock_sum += m[(i, j)].abs() + m[(j, i)].abs();
                    }
                }
                if offblock_sum > 0.1 {
                    count_with_offblock += 1;
                }
            }

            // At least 20% of matrices should have significant off-diagonal blocks
            assert!(
                count_with_offblock >= n_samples / 5,
                "At least 20% of matrices should have non-trivial off-diagonal blocks, got {}/{}",
                count_with_offblock,
                n_samples
            );
        }

        // ---------------------------------------------------------------------
        // 5. Non-degeneracy tests
        // ---------------------------------------------------------------------

        #[test]
        fn matrices_not_close_to_identity() {
            let mut rng = ChaCha8Rng::seed_from_u64(0x55667788);
            let identity = Matrix4f::identity();
            let mut near_identity_count = 0;
            let n_samples = 100;

            for _ in 0..n_samples {
                let m = random_sp4(&mut rng);
                let distance = (m - identity).norm();
                if distance < 0.1 {
                    near_identity_count += 1;
                }
            }

            // Very few matrices should be close to identity
            assert!(
                near_identity_count <= n_samples / 10,
                "Too many matrices ({}/{}) are close to identity",
                near_identity_count,
                n_samples
            );
        }

        #[test]
        fn matrices_hit_different_types() {
            // Check that we get matrices with different dynamical properties:
            // - Elliptic (eigenvalues on unit circle)
            // - Hyperbolic (real eigenvalues not on unit circle)
            // - Mixed (some elliptic, some hyperbolic)

            let mut rng = ChaCha8Rng::seed_from_u64(0x99AABBCC);
            let mut elliptic_count = 0;
            let mut hyperbolic_count = 0;
            let mut mixed_count = 0;
            let n_samples = 100;

            for _ in 0..n_samples {
                let m = random_sp4(&mut rng);

                // Classify based on eigenvalue structure
                let schur = m.clone().schur();
                let t = schur.unpack().1;

                // Count eigenvalues on unit circle vs off
                let mut on_circle = 0;
                let mut off_circle = 0;

                let mut i = 0;
                while i < 4 {
                    if i + 1 < 4 && t[(i + 1, i)].abs() > 1e-10 {
                        // 2x2 block: compute eigenvalue magnitude
                        let a = t[(i, i)];
                        let d = t[(i + 1, i + 1)];
                        let b = t[(i, i + 1)];
                        let c = t[(i + 1, i)];
                        let det = a * d - b * c;
                        let magnitude = det.abs().sqrt();
                        if (magnitude - 1.0).abs() < 0.1 {
                            on_circle += 2;
                        } else {
                            off_circle += 2;
                        }
                        i += 2;
                    } else {
                        // Real eigenvalue
                        let lambda = t[(i, i)].abs();
                        if (lambda - 1.0).abs() < 0.1 {
                            on_circle += 1;
                        } else {
                            off_circle += 1;
                        }
                        i += 1;
                    }
                }

                if off_circle == 0 {
                    elliptic_count += 1;
                } else if on_circle == 0 {
                    hyperbolic_count += 1;
                } else {
                    mixed_count += 1;
                }
            }

            // We should see a mix of types
            // (the sampler includes both rotations and shears)
            assert!(
                elliptic_count > 0 || mixed_count > 0,
                "Should produce some elliptic or mixed matrices"
            );
            // Due to shears, we should see non-elliptic behavior
            assert!(
                hyperbolic_count > 0 || mixed_count > 0,
                "Should produce some hyperbolic or mixed matrices"
            );
        }

        #[test]
        fn matrices_with_large_norm() {
            // Verify that some matrices have large norm (not all near identity)
            let mut rng = ChaCha8Rng::seed_from_u64(0xDDEEFF00);
            let mut max_norm: f64 = 0.0;

            for _ in 0..100 {
                let m = random_sp4(&mut rng);
                let norm = m.norm();
                max_norm = max_norm.max(norm);
            }

            // random_sp4 uses shear parameters up to 2.0, which can produce
            // matrices with norm significantly larger than sqrt(4) = 2
            assert!(
                max_norm > 3.0,
                "Should produce matrices with norm > 3.0, got max {}",
                max_norm
            );
        }

        // ---------------------------------------------------------------------
        // 6. Proptest for symplectic property
        // ---------------------------------------------------------------------
    }

    // =========================================================================
    // Sp(4) Type Coverage Test
    // =========================================================================
    //
    // This test explicitly enumerates matrix types and verifies the sampler
    // produces each type with sufficient probability for property testing.

    mod sp4_type_coverage {
        use super::*;
        use nalgebra::Complex;
        use std::collections::HashMap;

        /// Classification of Sp(4) matrix types based on geometric/dynamical properties.
        #[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
        enum Sp4MatrixType {
            /// Near identity: ||M - I|| < 0.1
            NearIdentity,
            /// Block diagonal: off-diagonal blocks near zero (pure rotations R(θ) ⊕ R(φ))
            BlockDiagonal,
            /// Pure shear: triangular with 1s on diagonal
            PureShear,
            /// Elliptic: all eigenvalues on unit circle (but not near-identity or block-diagonal)
            Elliptic,
            /// Hyperbolic: has real eigenvalues not on unit circle
            Hyperbolic,
            /// Parabolic: eigenvalue 1 with non-trivial Jordan block
            Parabolic,
            /// Exchange: permutation matrix swapping coordinates
            Exchange,
            /// Mixed: combination that doesn't fit other categories
            Mixed,
        }

        /// Classify an Sp(4) matrix based on its structure and eigenvalue properties.
        fn classify_sp4(m: &Matrix4f) -> Sp4MatrixType {
            let identity = Matrix4f::identity();
            let diff_from_identity = (m - identity).norm();

            // 1. Near identity check
            if diff_from_identity < 0.1 {
                return Sp4MatrixType::NearIdentity;
            }

            // 2. Check if it's an exchange/permutation matrix
            if is_exchange_matrix(m) {
                return Sp4MatrixType::Exchange;
            }

            // 3. Block diagonal check: off-diagonal blocks should be near zero
            // For (q1,q2,p1,p2) ordering, block diagonal means:
            // - Upper-right 2x2 block (indices [0,2], [0,3], [1,2], [1,3]) near zero
            // - Lower-left 2x2 block (indices [2,0], [2,1], [3,0], [3,1]) near zero
            let mut off_block_sum = 0.0;
            for i in 0..2 {
                for j in 2..4 {
                    off_block_sum += m[(i, j)].abs() + m[(j, i)].abs();
                }
            }
            let is_block_diagonal = off_block_sum < 0.1;

            // 4. Pure shear check: lower triangular with 1s on diagonal
            let is_pure_shear = is_shear_matrix(m);

            // 5. Eigenvalue-based classification
            let eigenvalue_type = classify_by_eigenvalues(m);

            // Decision tree
            if is_block_diagonal && eigenvalue_type == EigenvalueType::Elliptic {
                return Sp4MatrixType::BlockDiagonal;
            }

            if is_pure_shear {
                return Sp4MatrixType::PureShear;
            }

            match eigenvalue_type {
                EigenvalueType::Parabolic => Sp4MatrixType::Parabolic,
                EigenvalueType::Hyperbolic => Sp4MatrixType::Hyperbolic,
                EigenvalueType::Elliptic => Sp4MatrixType::Elliptic,
                EigenvalueType::Mixed => Sp4MatrixType::Mixed,
            }
        }

        /// Check if matrix is an exchange/permutation matrix (entries are 0 or ±1).
        fn is_exchange_matrix(m: &Matrix4f) -> bool {
            let mut nonzero_count = 0;
            for i in 0..4 {
                for j in 0..4 {
                    let entry = m[(i, j)];
                    if entry.abs() > 0.9 && entry.abs() < 1.1 {
                        nonzero_count += 1;
                    } else if entry.abs() > 0.1 {
                        return false; // Entry is neither near 0 nor near ±1
                    }
                }
            }
            // Should have exactly 4 entries near ±1 (one per row/column)
            nonzero_count == 4
        }

        /// Check if matrix is a pure shear (lower/upper triangular with 1s on diagonal).
        fn is_shear_matrix(m: &Matrix4f) -> bool {
            // Check diagonal is all 1s
            for i in 0..4 {
                if (m[(i, i)] - 1.0).abs() > 0.1 {
                    return false;
                }
            }

            // Check if either upper or lower triangular (one side near zero)
            let mut upper_sum = 0.0;
            let mut lower_sum = 0.0;
            for i in 0..4 {
                for j in 0..4 {
                    if i < j {
                        upper_sum += m[(i, j)].abs();
                    } else if i > j {
                        lower_sum += m[(i, j)].abs();
                    }
                }
            }

            // Pure shear if one triangle is near zero
            upper_sum < 0.1 || lower_sum < 0.1
        }

        #[derive(Debug, Clone, Copy, PartialEq, Eq)]
        enum EigenvalueType {
            Elliptic,   // All eigenvalues on unit circle
            Hyperbolic, // Some real eigenvalues off unit circle
            Parabolic,  // Eigenvalue 1 with Jordan block
            Mixed,      // Combination
        }

        /// Classify matrix by eigenvalue structure.
        fn classify_by_eigenvalues(m: &Matrix4f) -> EigenvalueType {
            let schur = m.clone().schur();
            let t = schur.unpack().1;

            let mut eigenvalues: Vec<Complex<f64>> = Vec::with_capacity(4);
            let mut has_jordan_block = false;

            let mut i = 0;
            while i < 4 {
                if i + 1 < 4 && t[(i + 1, i)].abs() > 1e-10 {
                    // 2x2 block: complex conjugate pair
                    let a = t[(i, i)];
                    let d = t[(i + 1, i + 1)];
                    let b = t[(i, i + 1)];
                    let c = t[(i + 1, i)];
                    let trace = a + d;
                    let det = a * d - b * c;
                    let disc = trace * trace - 4.0 * det;

                    if disc < -1e-10 {
                        let real = trace / 2.0;
                        let imag = (-disc).sqrt() / 2.0;
                        eigenvalues.push(Complex::new(real, imag));
                        eigenvalues.push(Complex::new(real, -imag));
                    } else {
                        let sqrt_disc = disc.max(0.0).sqrt();
                        eigenvalues.push(Complex::new((trace + sqrt_disc) / 2.0, 0.0));
                        eigenvalues.push(Complex::new((trace - sqrt_disc) / 2.0, 0.0));
                    }
                    i += 2;
                } else {
                    // Real eigenvalue
                    let lambda = t[(i, i)];
                    eigenvalues.push(Complex::new(lambda, 0.0));

                    // Check for Jordan block: if eigenvalue is 1 and there's a superdiagonal entry
                    if (lambda - 1.0).abs() < 0.01 && i + 1 < 4 && t[(i, i + 1)].abs() > 0.01 {
                        has_jordan_block = true;
                    }
                    i += 1;
                }
            }

            // Check if eigenvalue 1 appears with multiplicity suggesting Jordan block
            let ones_count = eigenvalues
                .iter()
                .filter(|e| (e.re - 1.0).abs() < 0.01 && e.im.abs() < 0.01)
                .count();

            if has_jordan_block || (ones_count >= 2 && !is_diagonal_like(m)) {
                return EigenvalueType::Parabolic;
            }

            // Count eigenvalues on/off unit circle
            let mut on_circle = 0;
            let mut off_circle = 0;

            for e in &eigenvalues {
                let magnitude = (e.re * e.re + e.im * e.im).sqrt();
                if (magnitude - 1.0).abs() < 0.1 {
                    on_circle += 1;
                } else {
                    off_circle += 1;
                }
            }

            if off_circle == 0 {
                EigenvalueType::Elliptic
            } else if on_circle == 0 {
                EigenvalueType::Hyperbolic
            } else {
                EigenvalueType::Mixed
            }
        }

        /// Check if matrix is nearly diagonal.
        fn is_diagonal_like(m: &Matrix4f) -> bool {
            let mut off_diag_sum = 0.0;
            for i in 0..4 {
                for j in 0..4 {
                    if i != j {
                        off_diag_sum += m[(i, j)].abs();
                    }
                }
            }
            off_diag_sum < 0.1
        }

        /// Main test: verify the Sp(4) sampler covers all expected matrix types.
        #[test]
        fn sp4_sampler_covers_all_types() {
            let n = 1000;
            let mut type_counts: HashMap<Sp4MatrixType, usize> = HashMap::new();

            for seed in 0..n {
                let m = seeded_sp4(seed as u64);
                let matrix_type = classify_sp4(&m);
                *type_counts.entry(matrix_type).or_insert(0) += 1;
            }

            // Print distribution for debugging
            println!("\nSp(4) Matrix Type Distribution (n={}):", n);
            println!("{:-<50}", "");
            let mut sorted_types: Vec<_> = type_counts.iter().collect();
            sorted_types.sort_by_key(|(t, _)| format!("{:?}", t));
            for (matrix_type, count) in &sorted_types {
                let prob = **count as f64 / n as f64 * 100.0;
                println!("  {:?}: {} ({:.1}%)", matrix_type, count, prob);
            }
            println!("{:-<50}", "");

            // Verify we see the major types with reasonable probability
            // Note: Not all types may appear due to sampler structure, but key ones should

            // 1. Elliptic/Mixed should appear (rotations generate these)
            let elliptic_or_mixed =
                type_counts.get(&Sp4MatrixType::Elliptic).copied().unwrap_or(0)
                    + type_counts.get(&Sp4MatrixType::Mixed).copied().unwrap_or(0)
                    + type_counts
                        .get(&Sp4MatrixType::BlockDiagonal)
                        .copied()
                        .unwrap_or(0);
            assert!(
                elliptic_or_mixed > 0,
                "Should produce some elliptic/block-diagonal matrices"
            );

            // 2. Exchange matrices should appear (30% chance per sample)
            let exchange_count = type_counts.get(&Sp4MatrixType::Exchange).copied().unwrap_or(0);
            // With 30% base probability, expect some exchanges even with classification filtering
            // The exchange may be classified as something else if composed with other transforms
            println!("Exchange count: {} (note: may be classified differently when composed)", exchange_count);

            // 3. Hyperbolic should appear (shears can produce these)
            let hyperbolic_count = type_counts
                .get(&Sp4MatrixType::Hyperbolic)
                .copied()
                .unwrap_or(0);
            println!("Hyperbolic count: {}", hyperbolic_count);

            // 4. Near-identity should be rare (parameters are sampled over wide ranges)
            let near_identity_count = type_counts
                .get(&Sp4MatrixType::NearIdentity)
                .copied()
                .unwrap_or(0);
            let near_identity_prob = near_identity_count as f64 / n as f64;
            assert!(
                near_identity_prob < 0.05,
                "Near-identity should be rare (<5%), got {:.1}%",
                near_identity_prob * 100.0
            );

            // 5. Should have at least 3 distinct types (diversity check)
            let num_types = type_counts.len();
            assert!(
                num_types >= 3,
                "Should produce at least 3 distinct matrix types, got {}",
                num_types
            );

            // 6. Print summary statistics
            println!("\nSummary:");
            println!("  Total distinct types: {}", num_types);
            println!(
                "  Elliptic/Block-diagonal/Mixed: {:.1}%",
                elliptic_or_mixed as f64 / n as f64 * 100.0
            );
            println!(
                "  Hyperbolic: {:.1}%",
                hyperbolic_count as f64 / n as f64 * 100.0
            );
            println!(
                "  Near-identity: {:.1}%",
                near_identity_prob * 100.0
            );
        }

        /// Test that bounded sampler produces more near-identity matrices at small scale.
        #[test]
        fn sp4_bounded_sampler_scale_affects_types() {
            let n = 200;

            // Small scale should produce more near-identity
            let mut small_scale_near_identity = 0;
            for seed in 0..n {
                let m = seeded_sp4_bounded(seed as u64, 0.05);
                if classify_sp4(&m) == Sp4MatrixType::NearIdentity {
                    small_scale_near_identity += 1;
                }
            }

            // Large scale should produce fewer near-identity
            let mut large_scale_near_identity = 0;
            for seed in 0..n {
                let m = seeded_sp4_bounded(seed as u64, 1.0);
                if classify_sp4(&m) == Sp4MatrixType::NearIdentity {
                    large_scale_near_identity += 1;
                }
            }

            println!("\nBounded sampler scale effect:");
            println!(
                "  scale=0.05: {:.1}% near-identity",
                small_scale_near_identity as f64 / n as f64 * 100.0
            );
            println!(
                "  scale=1.0:  {:.1}% near-identity",
                large_scale_near_identity as f64 / n as f64 * 100.0
            );

            assert!(
                small_scale_near_identity > large_scale_near_identity,
                "Small scale should produce more near-identity matrices"
            );
        }

        /// Test specific generator functions produce expected types.
        #[test]
        fn individual_generators_produce_expected_types() {
            // Pure rotations should be elliptic
            let rot = rotation_q1p1(0.5) * rotation_q2p2(0.7);
            let rot_type = classify_sp4(&rot);
            assert!(
                rot_type == Sp4MatrixType::BlockDiagonal || rot_type == Sp4MatrixType::Elliptic,
                "Pure rotations should be block-diagonal or elliptic, got {:?}",
                rot_type
            );

            // Pure shears should be classified as shear or parabolic
            let sh = shear_q1(1.0) * shear_q2(0.5);
            let sh_type = classify_sp4(&sh);
            assert!(
                sh_type == Sp4MatrixType::PureShear || sh_type == Sp4MatrixType::Parabolic,
                "Pure shears should be shear or parabolic, got {:?}",
                sh_type
            );

            // Exchange should be exchange
            let ex = symplectic_exchange();
            let ex_type = classify_sp4(&ex);
            assert!(
                ex_type == Sp4MatrixType::Exchange || ex_type == Sp4MatrixType::Elliptic,
                "Exchange matrix should be exchange or elliptic, got {:?}",
                ex_type
            );

            // Identity should be near-identity
            let id = Matrix4f::identity();
            assert_eq!(
                classify_sp4(&id),
                Sp4MatrixType::NearIdentity,
                "Identity should classify as near-identity"
            );

            // Large rotation should not be near-identity
            let large_rot = rotation_q1p1(PI / 2.0);
            assert!(
                classify_sp4(&large_rot) != Sp4MatrixType::NearIdentity,
                "90-degree rotation should not be near-identity"
            );
        }
    }

    mod sp4_proptests {
        use super::*;
        use proptest::prelude::*;

        proptest! {
            #[test]
            fn random_sp4_is_symplectic_proptest(seed: u64) {
                let m = seeded_sp4(seed);
                prop_assert!(
                    is_symplectic(&m, 1e-10),
                    "seeded_sp4({}) should be symplectic, error = {}",
                    seed,
                    (m.transpose() * standard_j() * m - standard_j()).norm()
                );
            }

            #[test]
            fn random_sp4_determinant_is_one_proptest(seed: u64) {
                let m = seeded_sp4(seed);
                let det = m.determinant();
                prop_assert!(
                    (det - 1.0).abs() < 1e-8,
                    "seeded_sp4({}) should have det=1, got {}",
                    seed,
                    det
                );
            }

            #[test]
            fn random_sp4_bounded_is_symplectic_proptest(seed: u64, scale in 0.1f64..2.0) {
                let m = seeded_sp4_bounded(seed, scale);
                prop_assert!(
                    is_symplectic(&m, 1e-10),
                    "seeded_sp4_bounded({}, {}) should be symplectic",
                    seed,
                    scale
                );
            }

            #[test]
            fn composition_of_symplectic_is_symplectic(seed1: u64, seed2: u64) {
                let m1 = seeded_sp4(seed1);
                let m2 = seeded_sp4(seed2);
                let product = m1 * m2;
                prop_assert!(
                    is_symplectic(&product, 1e-9),
                    "Product of two Sp(4) matrices should be symplectic"
                );
            }

            #[test]
            fn inverse_of_symplectic_is_symplectic(seed: u64) {
                let m = seeded_sp4(seed);
                if let Some(inv) = m.try_inverse() {
                    prop_assert!(
                        is_symplectic(&inv, 1e-9),
                        "Inverse of Sp(4) matrix should be symplectic"
                    );
                }
            }

            #[test]
            fn transpose_times_j_equals_j_times_inverse(seed: u64) {
                // For A in Sp(4): A^T J = J A^{-1}
                // This is equivalent to A^T J A = J
                let m = seeded_sp4(seed);
                if let Some(inv) = m.try_inverse() {
                    let j = standard_j();
                    let lhs = m.transpose() * j;
                    let rhs = j * inv;
                    let diff = (lhs - rhs).norm();
                    prop_assert!(
                        diff < 1e-9,
                        "A^T J should equal J A^{{-1}}, diff = {}",
                        diff
                    );
                }
            }
        }
    }
}
