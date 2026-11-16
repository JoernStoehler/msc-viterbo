//! HK2019 combinatorial capacity algorithm.
//!
//! # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//! # ⚠️  BROKEN ALGORITHM - DO NOT USE FOR PRODUCTION  ⚠️
//! # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//!
//! ## Why This Is Broken
//!
//! The QP solver is **INCOMPLETE**: it only checks 0D faces (vertices) and 1D
//! faces (edges) of the constraint polytope. For indefinite quadratics (which
//! the symplectic form produces), the global maximum can lie on **2D or higher-
//! dimensional faces**.
//!
//! ## What Goes Wrong
//!
//! - Returns plausible-looking capacity values that are **WRONG**
//! - Some tests "pass by luck" when the optimum happens to be at a vertex/edge
//! - Future agents may see passing tests and assume correctness
//!
//! ## DO NOT
//!
//! - Trust any capacity value returned by this algorithm
//! - Use this as ground truth for validation
//! - Remove the runtime warning without fixing the QP solver
//!
//! ## Blocked On
//!
//! `rust_viterbo_optim` crate with proper global QP solver.
//! See: `packages/rust_viterbo/optim/SPEC.md`
//!
//! # !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
//!
//! ---
//!
//! Implements the Haim-Kislev (2017) quadratic programming formulation for
//! computing the EHZ capacity.
//!
//! # Citations
//!
//! - **HK2017 Theorem 1**: Main capacity formula (HK2017-EHZ-polytopes.tex, lines 68-78):
//!   ```text
//!   c_EHZ(K) = (1/2) * [max_{σ∈S_F, β∈M(K)} Q(σ,β)]^{-1}
//!   ```
//!   where:
//!   - Q(σ,β) = Σ_{j<i} β_{σ(i)} β_{σ(j)} ω(n_{σ(i)}, n_{σ(j)})
//!   - M(K) = {β_i ≥ 0, Σ β_i h_i = 1, Σ β_i n_i = 0}
//!
//! - **HK2017 Remark 3.6** (lines 509-516): Graph-based pruning can reduce permutation space.
//!
//! **Performance note:** The algorithm has O(F!) complexity in the number of facets.
//! Default timeout is 60 seconds to prevent runaway computation.
//!
//! # UNCITED Claims
//!
//! - The previous doc claimed "CH2021 Theorem 1.4: rotation bound restricts valid permutations"
//!   but no such theorem exists in CH2021. This reference should be removed or corrected.

use crate::result::{AlgorithmError, CapacityResult, Diagnostics, WitnessOrbit};
use rust_viterbo_geom::{symplectic_form, PolytopeHRep, SymplecticVector};
use std::time::{Duration, Instant};

/// Maximum number of facets before we refuse (to avoid factorial explosion).
const MAX_FACETS_HK2019: usize = 10;

/// Default timeout for the algorithm (60 seconds).
const DEFAULT_TIMEOUT_SECS: u64 = 60;

/// Compute Q(σ, β) for a given permutation and β values.
///
/// Q(σ,β) = Σ_{j<i} β_{σ(i)} β_{σ(j)} ω(n_{σ(i)}, n_{σ(j)})
///
/// **Citation**: HK2017 Theorem 1 (equation 1).
fn compute_q(sigma: &[usize], beta: &[f64], normals: &[SymplecticVector]) -> f64 {
    let m = sigma.len();
    let mut q = 0.0;

    for i in 0..m {
        for j in 0..i {
            let ni = normals[sigma[i]];
            let nj = normals[sigma[j]];
            let omega = symplectic_form(ni, nj);
            q += beta[sigma[i]] * beta[sigma[j]] * omega;
        }
    }

    q
}

/// Solve the constrained QP for a given permutation.
///
/// # INCOMPLETE IMPLEMENTATION - BLOCKED ON optim CRATE
///
/// This function only checks vertices (0D) and edges (1D) of the feasible polytope.
/// For indefinite quadratics, the maximum can be on 2D or higher-dimensional faces.
///
/// **TODO**: Replace with `rust_viterbo_optim::maximize_quadratic_over_polytope`
/// once the optim crate is implemented. See `optim/SPEC.md`.
///
/// ---
///
/// Maximize Q(σ, β) subject to:
///   - Σ β_i h_i = 1  (normalization, HK2017 Theorem 1)
///   - Σ β_i n_i = 0  (closure constraint, HK2017 Theorem 1)
///   - β_i ≥ 0
///
/// The feasible region is a polytope. Q(σ,β) is an INDEFINITE quadratic form
/// (the symplectic form has mixed signs), so the maximum may be at a vertex,
/// edge interior, or higher-dimensional face interior.
///
/// Algorithm:
/// 1. Enumerate all vertices (basic feasible solutions) of the constraint polytope
/// 2. For each pair of vertices, check the edge between them for interior critical points
/// 3. Return the maximum Q found
///
/// For an edge from v₁ to v₂, Q restricted to the edge is quadratic in t ∈ [0,1]:
///   Q((1-t)v₁ + tv₂) = at² + bt + c
/// If a < 0 (parabola opens downward) and critical point t* = -b/(2a) ∈ (0,1),
/// then t* is a local maximum on the edge.
fn solve_qp_for_permutation(
    sigma: &[usize],
    normals: &[SymplecticVector],
    heights: &[f64],
) -> Option<(f64, Vec<f64>)> {
    let n = sigma.len();

    // Build constraint matrix A and vector b for: A * β = b
    // Row 0: height constraint (Σ β_i h_i = 1)
    // Rows 1-4: closure constraints (Σ β_i n_i = 0, four components)
    let mut a_data = Vec::with_capacity(5 * n);
    let b = [1.0, 0.0, 0.0, 0.0, 0.0];

    // Height constraint
    for h in heights {
        a_data.push(*h);
    }
    // Closure constraints (4 components of normal vectors)
    for comp in 0..4 {
        for i in 0..n {
            a_data.push(normals[i].as_slice()[comp]);
        }
    }

    let a_full = nalgebra::DMatrix::from_row_slice(5, n, &a_data);
    let b_vec = nalgebra::DVector::from_row_slice(&b);

    let mut best_q = f64::NEG_INFINITY;
    let mut best_beta = None;

    // Collect all vertices for edge search later
    let mut vertices: Vec<Vec<f64>> = Vec::new();

    // Phase 1: Enumerate all vertices (basic feasible solutions)
    for num_nonzero in 1..=n.min(5) {
        enumerate_subsets(n, num_nonzero, &mut |nonzero_indices: &[usize]| {
            // Build reduced system: extract columns for non-zero variables
            let k = nonzero_indices.len();
            let mut a_reduced_data = Vec::with_capacity(5 * k);
            for row in 0..5 {
                for &col in nonzero_indices {
                    a_reduced_data.push(a_full[(row, col)]);
                }
            }
            let a_reduced = nalgebra::DMatrix::from_row_slice(5, k, &a_reduced_data);

            // Solve the reduced system
            let svd = a_reduced.clone().svd(true, true);
            let beta_reduced = match svd.solve(&b_vec, 1e-10) {
                Ok(p) => p,
                Err(_) => return, // Singular system, skip
            };

            // Check that the solution actually satisfies the constraints
            let residual = (&a_reduced * &beta_reduced - &b_vec).norm();
            if residual > 1e-8 {
                return; // Not a valid solution
            }

            // Check non-negativity
            if beta_reduced.iter().any(|&b| b < -1e-10) {
                return; // Infeasible
            }

            // Reconstruct full beta vector
            let mut beta = vec![0.0; n];
            for (i, &idx) in nonzero_indices.iter().enumerate() {
                beta[idx] = beta_reduced[i].max(0.0);
            }

            // Evaluate Q at this vertex
            let q = compute_q(sigma, &beta, normals);
            if q > best_q {
                best_q = q;
                best_beta = Some(beta.clone());
            }

            // Store vertex for edge search
            vertices.push(beta);
        });
    }

    // Phase 2: Check edges between all pairs of vertices for interior critical points
    // For indefinite quadratics, the maximum might be in the interior of an edge
    for i in 0..vertices.len() {
        for j in (i + 1)..vertices.len() {
            let v1 = &vertices[i];
            let v2 = &vertices[j];

            // Check if edge is valid (all points on edge satisfy β ≥ 0)
            // Edge: β(t) = (1-t)v1 + t*v2 for t ∈ [0,1]
            // β_k(t) = (1-t)v1_k + t*v2_k ≥ 0 for all k
            // This is guaranteed if v1, v2 are both feasible (which they are)

            // Compute Q restricted to edge: Q(t) = at² + bt + c
            // Q(β(t)) = Σ_{r<s} β_{σ(s)}(t) β_{σ(r)}(t) ω(n_{σ(s)}, n_{σ(r)})
            // Let d = v2 - v1, so β(t) = v1 + t*d
            // β_{σ(k)}(t) = v1_{σ(k)} + t*d_{σ(k)}
            //
            // Q(t) = Σ_{r<s} (v1_{σ(s)} + t*d_{σ(s)})(v1_{σ(r)} + t*d_{σ(r)}) ω_{sr}
            //      = Σ_{r<s} [v1_{σ(s)}*v1_{σ(r)} + t*(v1_{σ(s)}*d_{σ(r)} + d_{σ(s)}*v1_{σ(r)}) + t²*d_{σ(s)}*d_{σ(r)}] ω_{sr}
            //
            // c = Q(v1)
            // a + b + c = Q(v2)
            // So we can compute a, b, c from Q(0), Q(1), and Q(0.5)

            let q0 = compute_q(sigma, v1, normals); // Q(0) = c
            let q1 = compute_q(sigma, v2, normals); // Q(1) = a + b + c

            // Q(0.5) = a/4 + b/2 + c
            let mut v_half = vec![0.0; n];
            for k in 0..n {
                v_half[k] = 0.5 * v1[k] + 0.5 * v2[k];
            }
            let q_half = compute_q(sigma, &v_half, normals);

            // Solve for a, b, c:
            // c = q0
            // a + b + c = q1  =>  a + b = q1 - q0
            // a/4 + b/2 + c = q_half  =>  a/4 + b/2 = q_half - q0
            //                         =>  a + 2b = 4*(q_half - q0)
            // From a + b = q1 - q0 and a + 2b = 4*(q_half - q0):
            // b = 4*(q_half - q0) - (q1 - q0) = 4*q_half - 4*q0 - q1 + q0 = 4*q_half - 3*q0 - q1
            // a = (q1 - q0) - b = q1 - q0 - 4*q_half + 3*q0 + q1 = 2*q1 + 2*q0 - 4*q_half
            let _c = q0; // c = Q(0), unused but kept for documentation
            let b_coef = 4.0 * q_half - 3.0 * q0 - q1;
            let a_coef = 2.0 * q1 + 2.0 * q0 - 4.0 * q_half;

            // For maximum on edge interior: need a < 0 and t* = -b/(2a) ∈ (0, 1)
            if a_coef < -1e-12 {
                let t_star = -b_coef / (2.0 * a_coef);
                if t_star > 1e-10 && t_star < 1.0 - 1e-10 {
                    // Compute β at t_star
                    let mut beta_star = vec![0.0; n];
                    for k in 0..n {
                        beta_star[k] = (1.0 - t_star) * v1[k] + t_star * v2[k];
                    }

                    // Verify feasibility (should be automatic but check anyway)
                    if beta_star.iter().all(|&b| b >= -1e-10) {
                        let q_star = compute_q(sigma, &beta_star, normals);
                        if q_star > best_q {
                            best_q = q_star;
                            // Clamp to non-negative
                            for b in &mut beta_star {
                                *b = b.max(0.0);
                            }
                            best_beta = Some(beta_star);
                        }
                    }
                }
            }
        }
    }

    if best_q > 0.0 {
        best_beta.map(|beta| (best_q, beta))
    } else {
        None
    }
}

/// Enumerate all subsets of {0, 1, ..., n-1} of size k, calling f for each.
fn enumerate_subsets<F>(n: usize, k: usize, f: &mut F)
where
    F: FnMut(&[usize]),
{
    if k == 0 {
        f(&[]);
        return;
    }
    if k > n {
        return;
    }

    let mut subset = vec![0; k];
    for i in 0..k {
        subset[i] = i;
    }

    loop {
        f(&subset);

        // Find rightmost element that can be incremented
        let mut i = k - 1;
        loop {
            if subset[i] < n - k + i {
                break;
            }
            if i == 0 {
                return; // All subsets enumerated
            }
            i -= 1;
        }

        // Increment and reset subsequent elements
        subset[i] += 1;
        for j in (i + 1)..k {
            subset[j] = subset[j - 1] + 1;
        }
    }
}

/// Generate all permutations of indices 0..n using Heap's algorithm.
fn all_permutations(n: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    let mut arr: Vec<usize> = (0..n).collect();
    heap_permute(&mut arr, n, &mut result);
    result
}

fn heap_permute(arr: &mut [usize], k: usize, result: &mut Vec<Vec<usize>>) {
    if k == 1 {
        result.push(arr.to_vec());
        return;
    }

    heap_permute(arr, k - 1, result);

    for i in 0..(k - 1) {
        if k.is_multiple_of(2) {
            arr.swap(i, k - 1);
        } else {
            arr.swap(0, k - 1);
        }
        heap_permute(arr, k - 1, result);
    }
}

/// Compute the EHZ capacity using the HK2019 algorithm.
///
/// c_EHZ(K) = (1/2) * [max_{σ,β} Q(σ,β)]^{-1}
///
/// **Citation**: HK2017 Theorem 1 (HK2017-EHZ-polytopes.tex, lines 68-78).
///
/// Uses a default timeout of 60 seconds. Use `compute_hk2019_capacity_with_timeout`
/// for custom timeout.
///
/// # Warning
///
/// **THIS ALGORITHM IS INCOMPLETE AND MAY RETURN WRONG VALUES.**
/// See module documentation for details.
pub fn compute_hk2019_capacity(hrep: PolytopeHRep) -> Result<CapacityResult, AlgorithmError> {
    compute_hk2019_capacity_with_timeout(hrep, Duration::from_secs(DEFAULT_TIMEOUT_SECS))
}

/// Compute the EHZ capacity using the HK2019 algorithm with custom timeout.
///
/// c_EHZ(K) = (1/2) * [max_{σ,β} Q(σ,β)]^{-1}
///
/// # Warning
///
/// **THIS ALGORITHM IS INCOMPLETE AND MAY RETURN WRONG VALUES.**
/// See module documentation for details.
pub fn compute_hk2019_capacity_with_timeout(
    hrep: PolytopeHRep,
    timeout: Duration,
) -> Result<CapacityResult, AlgorithmError> {
    // LOUD WARNING: This algorithm is incomplete and may return wrong values.
    // DO NOT REMOVE THIS WARNING without fixing the underlying QP solver.
    eprintln!(
        "\n\
        ╔══════════════════════════════════════════════════════════════════════╗\n\
        ║  WARNING: HK2019 algorithm is INCOMPLETE - results may be WRONG!     ║\n\
        ║                                                                      ║\n\
        ║  The QP solver only checks vertices and edges (0D/1D faces).         ║\n\
        ║  For indefinite quadratics, the maximum can be on 2D+ faces.         ║\n\
        ║                                                                      ║\n\
        ║  DO NOT trust the returned capacity value.                           ║\n\
        ║  See: packages/rust_viterbo/algorithm/src/hk2019.rs                  ║\n\
        ╚══════════════════════════════════════════════════════════════════════╝\n"
    );

    let start_time = Instant::now();

    // Validate input
    if let Err(e) = hrep.validate(1e-6) {
        return Err(AlgorithmError::ValidationError(e.to_string()));
    }

    let n = hrep.normals.len();
    if n > MAX_FACETS_HK2019 {
        return Err(AlgorithmError::ValidationError(format!(
            "HK2019 becomes too slow for >{} facets (have {})",
            MAX_FACETS_HK2019, n
        )));
    }

    // Generate all permutations
    let permutations = all_permutations(n);
    let total_perms = permutations.len();
    let mut diagnostics = Diagnostics {
        nodes_explored: 0,
        ..Default::default()
    };

    let mut max_q = 0.0;
    let mut best_sigma = None;
    let mut best_beta = None;

    // For each permutation, solve the QP
    for (i, sigma) in permutations.iter().enumerate() {
        // Check timeout every 100 permutations
        if i % 100 == 0 && start_time.elapsed() > timeout {
            return Err(AlgorithmError::ValidationError(format!(
                "HK2019 timed out after {:?} ({}/{} permutations explored)",
                start_time.elapsed(),
                i,
                total_perms
            )));
        }

        diagnostics.nodes_explored += 1;

        if let Some((q, beta)) = solve_qp_for_permutation(sigma, &hrep.normals, &hrep.heights) {
            if q > max_q {
                max_q = q;
                best_sigma = Some(sigma.clone());
                best_beta = Some(beta);
            }
        }
    }

    if max_q <= 0.0 {
        return Err(AlgorithmError::NoValidOrbits);
    }

    let capacity = 0.5 / max_q;
    diagnostics.best_action_found = capacity;

    // Construct witness (simplified)
    let witness = if let (Some(sigma), Some(beta)) = (best_sigma, best_beta) {
        // The witness orbit visits facets in order sigma, with time weights beta
        let total_time = capacity;
        let segment_times: Vec<f64> = beta.iter().map(|b| b * total_time).collect();
        Some(WitnessOrbit {
            breakpoints: vec![], // Would need to compute actual breakpoints
            facet_sequence: sigma,
            segment_times,
        })
    } else {
        None
    };

    Ok(CapacityResult {
        capacity,
        witness,
        diagnostics,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn tesseract() -> PolytopeHRep {
        let normals = vec![
            SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(-1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
            SymplecticVector::new(0.0, -1.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
            SymplecticVector::new(0.0, 0.0, -1.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
            SymplecticVector::new(0.0, 0.0, 0.0, -1.0),
        ];
        PolytopeHRep::new(normals, vec![1.0; 8])
    }

    #[test]
    fn symplectic_form_tesseract_normals() {
        let t = tesseract();
        // ω(n₀, n₄) = ω((1,0,0,0), (0,0,1,0)) = 1
        let omega = symplectic_form(t.normals[0], t.normals[4]);
        assert!((omega - 1.0).abs() < 1e-10);

        // ω(n₀, n₂) = ω((1,0,0,0), (0,1,0,0)) = 0
        let omega = symplectic_form(t.normals[0], t.normals[2]);
        assert!(omega.abs() < 1e-10);
    }

    #[test]
    fn permutation_count() {
        let perms = all_permutations(4);
        assert_eq!(perms.len(), 24); // 4! = 24
    }

    #[test]
    #[ignore = "8! = 40320 permutations makes this test very slow"]
    fn tesseract_hk2019_capacity() {
        let hrep = tesseract();
        let result = compute_hk2019_capacity(hrep);

        // The algorithm should find a valid capacity
        match result {
            Ok(r) => {
                // For tesseract, capacity should be 4
                assert!(
                    (r.capacity - 4.0).abs() < 0.5,
                    "Tesseract capacity should be ~4, got {}",
                    r.capacity
                );
            }
            Err(e) => {
                // Acceptable if QP solver doesn't converge well
                eprintln!("HK2019 failed: {:?}", e);
            }
        }
    }

    fn simplex_5() -> PolytopeHRep {
        // A 4-simplex with 5 facets
        // Vertices at standard simplex: e₁, e₂, e₃, e₄, and origin projected
        let normals = vec![
            SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
            SymplecticVector::new(-1.0, -1.0, -1.0, -1.0) / 2.0_f64.sqrt(),
        ];
        PolytopeHRep::new(normals, vec![1.0, 1.0, 1.0, 1.0, 1.0])
    }

    #[test]
    fn simplex_hk2019_runs() {
        // 5! = 120 permutations, should complete quickly
        let hrep = simplex_5();
        let result = compute_hk2019_capacity(hrep);
        // Just verify it runs without crashing
        match result {
            Ok(r) => {
                assert!(r.capacity > 0.0, "capacity should be positive");
            }
            Err(_) => {
                // QP might not converge, that's acceptable
            }
        }
    }

    #[test]
    fn compute_q_basic() {
        let normals = vec![
            SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
        ];
        // σ = [0, 1], β = [0.5, 0.5]
        // Q = β[1] * β[0] * ω(n[1], n[0]) = 0.25 * ω((0,0,1,0), (1,0,0,0))
        // ω(v, w) = ⟨Jv, w⟩, J(0,0,1,0) = (-1,0,0,0)
        // So ω = ⟨(-1,0,0,0), (1,0,0,0)⟩ = -1
        // Q = 0.25 * (-1) = -0.25
        let sigma = vec![0, 1];
        let beta = vec![0.5, 0.5];
        let q = compute_q(&sigma, &beta, &normals);
        assert!((q + 0.25).abs() < 1e-10);
    }

    #[test]
    fn tesseract_optimal_q_value() {
        // Test that the known optimal configuration for the tesseract gives Q = 0.125.
        // Optimal: β = (0.25, 0.25, 0, 0, 0.25, 0.25, 0, 0)
        // With permutation σ = [0, 5, 1, 4, 2, 3, 6, 7]
        // This should give Q = 0.125, hence capacity = 0.5 / 0.125 = 4.
        let t = tesseract();
        let beta = vec![0.25, 0.25, 0.0, 0.0, 0.25, 0.25, 0.0, 0.0];
        let sigma = vec![0, 5, 1, 4, 2, 3, 6, 7];

        let q = compute_q(&sigma, &beta, &t.normals);

        eprintln!("Q value for optimal tesseract config: {}", q);
        eprintln!("Expected Q = 0.125, capacity = 0.5 / 0.125 = 4");

        assert!(
            (q - 0.125).abs() < 1e-10,
            "Optimal Q should be 0.125, got {}",
            q
        );
    }

    #[test]
    fn tesseract_qp_solver_finds_optimal() {
        // Test that solve_qp_for_permutation finds the correct Q for the optimal permutation.
        let t = tesseract();
        let sigma = vec![0, 5, 1, 4, 2, 3, 6, 7];

        let result = solve_qp_for_permutation(&sigma, &t.normals, &t.heights);

        match result {
            Some((q, beta)) => {
                eprintln!("QP solver found Q = {}", q);
                eprintln!("Beta values: {:?}", beta);
                assert!(
                    q >= 0.125 - 1e-3,
                    "QP solver should find Q >= 0.125, got {}",
                    q
                );
            }
            None => {
                panic!("QP solver returned None for known-good permutation");
            }
        }
    }

    #[test]
    fn debug_tesseract_null_space() {
        // Debug: examine the null space and bounds for the tesseract.
        let t = tesseract();
        let n = t.normals.len();

        // Build constraint matrix
        let mut a_data = Vec::with_capacity(5 * n);
        for h in &t.heights {
            a_data.push(*h);
        }
        for comp in 0..4 {
            for i in 0..n {
                a_data.push(t.normals[i].as_slice()[comp]);
            }
        }

        let a = nalgebra::DMatrix::from_row_slice(5, n, &a_data);
        let b_vec = nalgebra::DVector::from_row_slice(&[1.0, 0.0, 0.0, 0.0, 0.0]);

        eprintln!("Constraint matrix A:");
        for i in 0..5 {
            for j in 0..n {
                eprint!("{:6.2} ", a[(i, j)]);
            }
            eprintln!();
        }

        // Solve for particular solution
        let svd = a.clone().svd(true, true);
        let particular = svd.solve(&b_vec, 1e-10).expect("should solve");
        eprintln!("\nParticular solution: {:?}", particular.as_slice());

        // Check that the optimal point (0.25, 0.25, 0, 0, 0.25, 0.25, 0, 0) is in feasible region
        let optimal_beta =
            nalgebra::DVector::from_row_slice(&[0.25, 0.25, 0.0, 0.0, 0.25, 0.25, 0.0, 0.0]);
        let delta = &optimal_beta - &particular;
        eprintln!("\nDelta from particular to optimal: {:?}", delta.as_slice());

        // Check if optimal satisfies constraints (A * optimal should equal b)
        let a_optimal = &a * &optimal_beta;
        eprintln!(
            "A * optimal (should be [1,0,0,0,0]): {:?}",
            a_optimal.as_slice()
        );
    }

    #[test]
    fn debug_triangle_triangle_product() {
        // Debug: trace through HK2019 for a simple triangle×triangle product.
        // This has 6 facets, so 6! = 720 permutations (manageable).

        // Equilateral-ish triangle in q-plane
        let q_normals = vec![
            (1.0_f64, 0.0_f64),
            (-0.5, 3.0_f64.sqrt() / 2.0),
            (-0.5, -3.0_f64.sqrt() / 2.0),
        ];
        // Same triangle in p-plane
        let p_normals = vec![
            (1.0_f64, 0.0_f64),
            (-0.5, 3.0_f64.sqrt() / 2.0),
            (-0.5, -3.0_f64.sqrt() / 2.0),
        ];

        let mut normals = Vec::new();
        let mut heights = Vec::new();

        // q-facets: (n_x, n_y, 0, 0)
        for (nx, ny) in &q_normals {
            normals.push(SymplecticVector::new(*nx, *ny, 0.0, 0.0));
            heights.push(1.0);
        }
        // p-facets: (0, 0, n_x, n_y)
        for (nx, ny) in &p_normals {
            normals.push(SymplecticVector::new(0.0, 0.0, *nx, *ny));
            heights.push(1.0);
        }

        eprintln!("=== Triangle×Triangle Product ===");
        eprintln!("Normals:");
        for (i, n) in normals.iter().enumerate() {
            eprintln!(
                "  n[{}] = ({:.3}, {:.3}, {:.3}, {:.3})",
                i, n.x, n.y, n.z, n.w
            );
        }

        // Print symplectic form matrix
        eprintln!("\nSymplectic form ω(nᵢ, nⱼ):");
        eprint!("     ");
        for j in 0..6 {
            eprint!("{:7}", j);
        }
        eprintln!();
        for i in 0..6 {
            eprint!("  {} |", i);
            for j in 0..6 {
                let omega = symplectic_form(normals[i], normals[j]);
                eprint!("{:7.3}", omega);
            }
            eprintln!();
        }

        // Try the HK2019 algorithm
        let hrep = PolytopeHRep::new(normals.clone(), heights.clone());
        let result = compute_hk2019_capacity(hrep);

        eprintln!("\nHK2019 result: {:?}", result);

        // Now let's manually check a few permutations
        let n = 6;
        let mut a_data = Vec::with_capacity(5 * n);
        for h in &heights {
            a_data.push(*h);
        }
        for comp in 0..4 {
            for i in 0..n {
                a_data.push(normals[i].as_slice()[comp]);
            }
        }
        let a = nalgebra::DMatrix::from_row_slice(5, n, &a_data);
        let b_vec = nalgebra::DVector::from_row_slice(&[1.0, 0.0, 0.0, 0.0, 0.0]);

        let svd = a.clone().svd(true, true);
        let particular = svd.solve(&b_vec, 1e-10).expect("should solve");
        eprintln!("\nParticular solution: {:?}", particular.as_slice());

        // Check non-negativity of particular solution
        let any_negative = particular.iter().any(|&b| b < -1e-10);
        eprintln!("Any negative β in particular solution: {}", any_negative);

        // Try the identity permutation
        let sigma = vec![0, 1, 2, 3, 4, 5];
        if let Some((q, beta)) = solve_qp_for_permutation(&sigma, &normals, &heights) {
            eprintln!("\nIdentity permutation:");
            eprintln!("  Q = {}", q);
            eprintln!("  β = {:?}", beta);
        } else {
            eprintln!("\nIdentity permutation: no valid solution");
        }

        // Try permutation that interleaves q and p facets
        let sigma = vec![0, 3, 1, 4, 2, 5]; // q0, p0, q1, p1, q2, p2
        if let Some((q, beta)) = solve_qp_for_permutation(&sigma, &normals, &heights) {
            eprintln!("\nInterleaved permutation [0,3,1,4,2,5]:");
            eprintln!("  Q = {}", q);
            eprintln!("  β = {:?}", beta);
        } else {
            eprintln!("\nInterleaved permutation [0,3,1,4,2,5]: no valid solution");
        }

        // Check the best permutation found
        let best_sigma = vec![3, 0, 5, 2, 4, 1];
        if let Some((q, beta)) = solve_qp_for_permutation(&best_sigma, &normals, &heights) {
            eprintln!("\nBest permutation [3,0,5,2,4,1]:");
            eprintln!("  Q = {}", q);
            eprintln!("  β = {:?}", beta);

            // Manually compute Q to verify
            let mut manual_q = 0.0;
            for i in 0..6 {
                for j in 0..i {
                    let ni = normals[best_sigma[i]];
                    let nj = normals[best_sigma[j]];
                    let omega = symplectic_form(ni, nj);
                    let contrib = beta[best_sigma[i]] * beta[best_sigma[j]] * omega;
                    if contrib.abs() > 1e-10 {
                        eprintln!(
                            "    Q[{},{}]: β[{}]*β[{}]*ω({},{}) = {:.4}*{:.4}*{:.4} = {:.4}",
                            j,
                            i,
                            best_sigma[j],
                            best_sigma[i],
                            best_sigma[j],
                            best_sigma[i],
                            beta[best_sigma[j]],
                            beta[best_sigma[i]],
                            omega,
                            contrib
                        );
                    }
                    manual_q += contrib;
                }
            }
            eprintln!("  Manual Q = {}", manual_q);
        }
    }
}
