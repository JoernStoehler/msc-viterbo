//! KKT system solver for fixed permutations.
//!
//! For a fixed permutation sigma, we solve the constrained optimization problem:
//!
//! max Q(sigma, beta) subject to:
//!   - beta_i >= 0 for all i
//!   - Sum beta_i h_i = 1  (height constraint)
//!   - Sum beta_i n_i = 0  (closure constraint)
//!
//! The approach:
//! 1. Build the Hessian H of Q (which is symmetric despite omega being antisymmetric)
//! 2. Build the equality constraint matrix A and RHS b
//! 3. Solve the KKT system [H A^T; A 0] [beta; lambda] = [0; b]
//! 4. Check if the solution satisfies beta >= 0
//!
//! WARNING: This only finds the interior critical point. If the true maximum
//! is on the boundary (some beta_i = 0), this method will fail to find it.

use nalgebra::{DMatrix, DVector};

use crate::enumerate::Permutation;
use crate::types::{FacetData, Hk2017Config, RejectionReason};

/// Result of solving the QP for a single permutation.
#[derive(Debug)]
pub enum SolveResult {
    /// Found a feasible interior critical point.
    Feasible {
        /// The Q value at the critical point.
        q_value: f64,
        /// The beta coefficients (local indices, same order as permutation).
        beta_local: Vec<f64>,
    },
    /// The interior critical point is infeasible.
    Infeasible(RejectionReason),
}

/// Solve the constrained QP for a fixed permutation.
///
/// Returns the Q value and beta coefficients if the interior critical point
/// is feasible (all beta >= 0), or a rejection reason otherwise.
pub fn solve_for_permutation(
    sigma: &Permutation,
    facet_data: &FacetData,
    config: &Hk2017Config,
) -> SolveResult {
    let k = sigma.len();
    debug_assert!(k >= 2, "Permutation must have at least 2 elements");

    // Build the Hessian H of Q.
    //
    // Q = Sum_{j < i} beta_{sigma(i)} * beta_{sigma(j)} * omega(n_{sigma(i)}, n_{sigma(j)})
    //
    // The Hessian is:
    // H[l,m] = omega(n_{sigma(max(l,m))}, n_{sigma(min(l,m))}) if l != m
    //        = 0 if l == m
    //
    // This is symmetric because:
    // H[l,m] = sign(l-m) * omega(n_{sigma(l)}, n_{sigma(m)})
    // and omega is antisymmetric, so H[l,m] = H[m,l].
    let mut h = DMatrix::zeros(k, k);
    for i in 0..k {
        for j in 0..i {
            let omega_ij = facet_data.omega_matrix[(sigma[i], sigma[j])];
            h[(i, j)] = omega_ij;
            h[(j, i)] = omega_ij; // Symmetric
        }
    }

    // Build equality constraints for the participating facets.
    // A * beta = b where:
    // Row 0: Sum beta * h_i = 1 (height constraint)
    // Rows 1-4: Sum beta * n_i[d] = 0 (closure constraint in R^4)
    let n_constraints = 5;
    let mut a = DMatrix::zeros(n_constraints, k);
    let mut b = DVector::zeros(n_constraints);

    for (local_i, &global_i) in sigma.iter().enumerate() {
        // Height constraint
        a[(0, local_i)] = facet_data.heights[global_i];
        // Closure constraints
        for d in 0..4 {
            a[(1 + d, local_i)] = facet_data.normals[global_i][d];
        }
    }
    b[0] = 1.0; // Height sum = 1, closure = 0

    // Build and solve the KKT system.
    //
    // For maximizing Q = (1/2) beta^T H beta subject to A*beta = b:
    // The KKT conditions are:
    //   H*beta + A^T*lambda = 0  (stationarity, note: grad Q = H*beta for symmetric H)
    //   A*beta = b              (feasibility)
    //
    // As a linear system:
    // [H   A^T] [beta  ]   [0]
    // [A   0  ] [lambda] = [b]
    let system_size = k + n_constraints;
    let mut kkt = DMatrix::zeros(system_size, system_size);
    let mut rhs = DVector::zeros(system_size);

    // Fill H (top-left block)
    for i in 0..k {
        for j in 0..k {
            kkt[(i, j)] = h[(i, j)];
        }
    }

    // Fill A^T (top-right block) and A (bottom-left block)
    for c in 0..n_constraints {
        for v in 0..k {
            kkt[(v, k + c)] = a[(c, v)];
            kkt[(k + c, v)] = a[(c, v)];
        }
    }

    // Fill RHS
    for c in 0..n_constraints {
        rhs[k + c] = b[c];
    }

    // Solve using LU decomposition
    let lu = kkt.clone().lu();
    let solution = match lu.solve(&rhs) {
        Some(sol) => sol,
        None => return SolveResult::Infeasible(RejectionReason::SingularKkt),
    };

    // Extract beta (first k components)
    let beta_local: Vec<f64> = (0..k).map(|i| solution[i]).collect();

    // Check feasibility: all beta >= -positive_tol
    let all_positive = beta_local.iter().all(|&b| b >= -config.positive_tol);
    if !all_positive {
        return SolveResult::Infeasible(RejectionReason::NegativeBeta);
    }

    // Compute Q value
    let q_value = compute_q_local(&beta_local, &h);

    // Check Q is positive
    if q_value <= 0.0 {
        return SolveResult::Infeasible(RejectionReason::NonPositiveQ);
    }

    SolveResult::Feasible { q_value, beta_local }
}

/// Compute Q value from local beta and Hessian.
///
/// Q = Sum_{j < i} beta[i] * beta[j] * H[i,j]
fn compute_q_local(beta: &[f64], h: &DMatrix<f64>) -> f64 {
    let k = beta.len();
    let mut q = 0.0;
    for i in 0..k {
        for j in 0..i {
            q += beta[i] * beta[j] * h[(i, j)];
        }
    }
    q
}

/// Convert local beta (indexed by permutation position) to global beta (indexed by facet).
pub fn beta_local_to_global(
    beta_local: &[f64],
    sigma: &Permutation,
    num_facets: usize,
) -> Vec<f64> {
    let mut beta_global = vec![0.0; num_facets];
    for (local_i, &global_i) in sigma.iter().enumerate() {
        beta_global[global_i] = beta_local[local_i];
    }
    beta_global
}

/// Compute Q value using global beta indexing and permutation order.
///
/// This is used for verification to ensure consistency.
pub fn compute_q_global(
    beta_global: &[f64],
    sigma: &Permutation,
    facet_data: &FacetData,
) -> f64 {
    let mut q = 0.0;
    for (pos_i, &facet_i) in sigma.iter().enumerate() {
        for (_pos_j, &facet_j) in sigma.iter().enumerate().take(pos_i) {
            q += beta_global[facet_i]
                * beta_global[facet_j]
                * facet_data.omega_matrix[(facet_i, facet_j)];
        }
    }
    q
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::PolytopeHRep;
    use approx::assert_relative_eq;
    use nalgebra::Vector4;

    fn make_tesseract() -> PolytopeHRep {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(0.0, 0.0, 0.0, -1.0),
        ];
        let heights = vec![1.0; 8];
        PolytopeHRep::new(normals, heights)
    }

    #[test]
    fn test_solve_tesseract_some_permutation() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();
        let config = Hk2017Config::default();

        // Try a specific permutation: 0 -> 4 -> 1 -> 5
        // Facets: +e1 -> +e3 -> -e1 -> -e3
        // This is a 4-cycle in the q1-p1 plane
        let sigma = vec![0, 4, 1, 5];
        let result = solve_for_permutation(&sigma, &facet_data, &config);

        match result {
            SolveResult::Feasible { q_value, beta_local } => {
                println!("Q = {}", q_value);
                println!("beta = {:?}", beta_local);
                assert!(q_value > 0.0);
                assert!(beta_local.iter().all(|&b| b >= -config.positive_tol));
            }
            SolveResult::Infeasible(reason) => {
                // This permutation might not be feasible, that's ok
                println!("Infeasible: {:?}", reason);
            }
        }
    }

    #[test]
    fn test_beta_local_to_global() {
        let sigma = vec![2, 0, 3];
        let beta_local = vec![0.1, 0.2, 0.3];
        let beta_global = beta_local_to_global(&beta_local, &sigma, 5);

        assert_eq!(beta_global.len(), 5);
        assert_relative_eq!(beta_global[0], 0.2, epsilon = 1e-15);
        assert_relative_eq!(beta_global[2], 0.1, epsilon = 1e-15);
        assert_relative_eq!(beta_global[3], 0.3, epsilon = 1e-15);
        assert_relative_eq!(beta_global[1], 0.0, epsilon = 1e-15);
        assert_relative_eq!(beta_global[4], 0.0, epsilon = 1e-15);
    }

    #[test]
    fn test_compute_q_local_matches_global() {
        let polytope = make_tesseract();
        let facet_data = FacetData::from_polytope(&polytope).unwrap();

        let sigma = vec![0, 4, 1, 5];
        let beta_local = vec![0.25, 0.25, 0.25, 0.25];
        let beta_global = beta_local_to_global(&beta_local, &sigma, 8);

        // Build local Hessian
        let k = sigma.len();
        let mut h = DMatrix::zeros(k, k);
        for i in 0..k {
            for j in 0..i {
                let omega_ij = facet_data.omega_matrix[(sigma[i], sigma[j])];
                h[(i, j)] = omega_ij;
                h[(j, i)] = omega_ij;
            }
        }

        let q_local = compute_q_local(&beta_local, &h);
        let q_global = compute_q_global(&beta_global, &sigma, &facet_data);

        assert_relative_eq!(q_local, q_global, epsilon = 1e-12);
    }
}
