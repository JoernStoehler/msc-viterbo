//! Main algorithm orchestration for HK2017.
//!
//! This module contains the main entry point that:
//! 1. Validates and preprocesses the polytope
//! 2. Enumerates permutations using the configured strategy
//! 3. Solves the QP for each permutation
//! 4. Tracks the maximum Q value
//! 5. Computes and verifies the final capacity

use crate::enumerate::{create_enumerator, Permutation};
use crate::solve::{beta_local_to_global, solve_for_permutation, SolveResult};
use crate::types::{
    FacetData, Hk2017Config, Hk2017Error, Hk2017Result, PolytopeHRep, RejectionHistogram,
};

/// Compute the EHZ capacity of a polytope using the HK2017 algorithm.
///
/// # Arguments
///
/// * `polytope` - The polytope in H-representation (normals and heights)
/// * `config` - Algorithm configuration (enumeration strategy, tolerances)
///
/// # Returns
///
/// The computed capacity and associated data, or an error if computation fails.
///
/// # Warning: Uncheckable Assumption
///
/// This implementation assumes the global maximum of Q occurs at an interior
/// point of the feasible region. If the true maximum is on the boundary
/// (some beta_i = 0), the returned capacity will be **incorrect** (too large).
///
/// There is no way to detect this from the output. See the crate documentation
/// for mitigation strategies.
///
/// # Example
///
/// ```
/// use hk2017::{hk2017_capacity, Hk2017Config, PolytopeHRep};
/// use nalgebra::Vector4;
///
/// // Create a tesseract [-1, 1]^4
/// let normals = vec![
///     Vector4::new( 1.0,  0.0,  0.0,  0.0),
///     Vector4::new(-1.0,  0.0,  0.0,  0.0),
///     Vector4::new( 0.0,  1.0,  0.0,  0.0),
///     Vector4::new( 0.0, -1.0,  0.0,  0.0),
///     Vector4::new( 0.0,  0.0,  1.0,  0.0),
///     Vector4::new( 0.0,  0.0, -1.0,  0.0),
///     Vector4::new( 0.0,  0.0,  0.0,  1.0),
///     Vector4::new( 0.0,  0.0,  0.0, -1.0),
/// ];
/// let heights = vec![1.0; 8];
/// let polytope = PolytopeHRep::new(normals, heights);
///
/// let result = hk2017_capacity(&polytope, &Hk2017Config::default()).unwrap();
/// assert!((result.capacity - 4.0).abs() < 1e-6);
/// ```
pub fn hk2017_capacity(
    polytope: &PolytopeHRep,
    config: &Hk2017Config,
) -> Result<Hk2017Result, Hk2017Error> {
    // Step 1: Preprocess
    let facet_data = FacetData::from_polytope(polytope)?;

    // Step 2: Enumerate permutations
    let enumerator = create_enumerator(config.strategy);
    let permutations = enumerator.enumerate(&facet_data);

    // Step 3 & 4: Solve QP for each permutation, track maximum
    let mut best: Option<BestSolution> = None;
    let mut rejection_histogram = RejectionHistogram::default();
    let mut permutations_evaluated = 0;

    for sigma in &permutations {
        permutations_evaluated += 1;

        match solve_for_permutation(sigma, &facet_data, config) {
            SolveResult::Feasible { q_value, beta_local } => {
                let should_update = match &best {
                    None => true,
                    Some(current) => q_value > current.q_value,
                };

                if should_update {
                    best = Some(BestSolution {
                        q_value,
                        beta_local,
                        permutation: sigma.clone(),
                    });
                }
            }
            SolveResult::Infeasible(reason) => {
                rejection_histogram.record(reason);
            }
        }
    }

    // Step 5: Build result
    let best = match best {
        Some(b) => b,
        None => {
            return Err(Hk2017Error::NoFeasibleInteriorPoint {
                checked: permutations_evaluated,
                rejected: rejection_histogram.total(),
                rejection_reasons: rejection_histogram,
            });
        }
    };

    // Compute capacity from Q
    let capacity = 1.0 / (2.0 * best.q_value);

    // Convert local beta to global
    let optimal_beta = beta_local_to_global(
        &best.beta_local,
        &best.permutation,
        facet_data.num_facets,
    );

    let result = Hk2017Result {
        capacity,
        optimal_permutation: best.permutation,
        optimal_beta,
        q_max: best.q_value,
        permutations_evaluated,
        permutations_rejected: rejection_histogram.total(),
        interior_only_assumption: true,
    };

    // Verify result in debug builds
    result.verify(&facet_data);

    Ok(result)
}

/// Temporary storage for the best solution found so far.
struct BestSolution {
    q_value: f64,
    beta_local: Vec<f64>,
    permutation: Permutation,
}

#[cfg(test)]
mod tests {
    use super::*;
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
    fn test_tesseract_capacity_naive() {
        let polytope = make_tesseract();
        let config = Hk2017Config::naive();

        let result = hk2017_capacity(&polytope, &config).unwrap();

        // Tesseract [-1,1]^4 has capacity 4.0 (HK2017 Example 4.6)
        assert_relative_eq!(result.capacity, 4.0, epsilon = 1e-6);
        assert!(result.q_max > 0.0);
        assert!(result.permutations_evaluated > 0);
    }

    #[test]
    fn test_tesseract_capacity_graph_pruned() {
        // Graph pruning uses geometric adjacency (shared vertices) to prune
        // permutations. For the tesseract, this correctly identifies that
        // opposite facets cannot be adjacent in a valid orbit.
        let polytope = make_tesseract();
        let config = Hk2017Config::graph_pruned();

        let result = hk2017_capacity(&polytope, &config).unwrap();

        // Should get same capacity with graph pruning
        assert_relative_eq!(result.capacity, 4.0, epsilon = 1e-6);
    }

    #[test]
    fn test_naive_and_graph_pruned_agree() {
        let polytope = make_tesseract();

        let result_naive = hk2017_capacity(&polytope, &Hk2017Config::naive()).unwrap();
        let result_graph = hk2017_capacity(&polytope, &Hk2017Config::graph_pruned()).unwrap();

        assert_relative_eq!(
            result_naive.capacity,
            result_graph.capacity,
            epsilon = 1e-10
        );
        assert_relative_eq!(result_naive.q_max, result_graph.q_max, epsilon = 1e-10);

        // Graph pruning should check fewer or equal permutations
        assert!(
            result_graph.permutations_evaluated <= result_naive.permutations_evaluated,
            "Graph pruned: {}, Naive: {}",
            result_graph.permutations_evaluated,
            result_naive.permutations_evaluated
        );
    }

    #[test]
    fn test_scaled_tesseract() {
        // Scaling by lambda should scale capacity by lambda^2
        let lambda = 2.0;

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
        let heights_scaled = vec![lambda; 8]; // Scaling heights by lambda
        let polytope_scaled = PolytopeHRep::new(normals, heights_scaled);

        let result = hk2017_capacity(&polytope_scaled, &Hk2017Config::default()).unwrap();

        // c(lambda * K) = lambda^2 * c(K) = 4 * 4 = 16
        assert_relative_eq!(result.capacity, 16.0, epsilon = 1e-6);
    }

    #[test]
    fn test_rectangle_product() {
        // Rectangle [0,a]x[0,b] x [0,c]x[0,d] centered at origin
        // becomes [-a/2, a/2] x [-b/2, b/2] x [-c/2, c/2] x [-d/2, d/2]
        // Capacity = min(a*b, c*d)

        // Let's use a=2, b=1 in the q-plane and c=1, d=1 in the p-plane
        // Centered at origin: heights are a/2, b/2, c/2, d/2
        let a = 2.0;
        let b = 1.0;
        let c = 1.0;
        let d = 1.0;

        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),  // +q1
            Vector4::new(-1.0, 0.0, 0.0, 0.0), // -q1
            Vector4::new(0.0, 1.0, 0.0, 0.0),  // +q2
            Vector4::new(0.0, -1.0, 0.0, 0.0), // -q2
            Vector4::new(0.0, 0.0, 1.0, 0.0),  // +p1
            Vector4::new(0.0, 0.0, -1.0, 0.0), // -p1
            Vector4::new(0.0, 0.0, 0.0, 1.0),  // +p2
            Vector4::new(0.0, 0.0, 0.0, -1.0), // -p2
        ];
        let heights = vec![
            a / 2.0, a / 2.0, // q1 direction
            b / 2.0, b / 2.0, // q2 direction
            c / 2.0, c / 2.0, // p1 direction
            d / 2.0, d / 2.0, // p2 direction
        ];
        let polytope = PolytopeHRep::new(normals, heights);

        let result = hk2017_capacity(&polytope, &Hk2017Config::default()).unwrap();

        // For Lagrangian product B_q x B_p:
        // c_EHZ = min(Area(B_q), Area(B_p)) = min(a*b, c*d) = min(2, 1) = 1
        assert_relative_eq!(result.capacity, 1.0, epsilon = 1e-6);
    }
}
