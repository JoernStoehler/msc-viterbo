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
            SolveResult::Feasible {
                q_value,
                beta_local,
            } => {
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
    let optimal_beta =
        beta_local_to_global(&best.beta_local, &best.permutation, facet_data.num_facets);

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
            a / 2.0,
            a / 2.0, // q1 direction
            b / 2.0,
            b / 2.0, // q2 direction
            c / 2.0,
            c / 2.0, // p1 direction
            d / 2.0,
            d / 2.0, // p2 direction
        ];
        let polytope = PolytopeHRep::new(normals, heights);

        let result = hk2017_capacity(&polytope, &Hk2017Config::default()).unwrap();

        // For Lagrangian product B_q x B_p:
        // c_EHZ = min(Area(B_q), Area(B_p)) = min(a*b, c*d) = min(2, 1) = 1
        assert_relative_eq!(result.capacity, 1.0, epsilon = 1e-6);
    }

    /// Create a 4D simplex with origin in interior.
    /// This is a general-position polytope where naive and graph_pruned
    /// must agree after the constraint verification fix.
    fn make_simplex() -> PolytopeHRep {
        // 5 vertices of a regular simplex centered at origin
        // We use a simple construction: 4 vertices at ±1 on axes, 1 at (1,1,1,1)/2
        let vertices = [
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(-0.5, -0.5, -0.5, -0.5),
        ];

        // Centroid
        let centroid: Vector4<f64> = vertices.iter().sum::<Vector4<f64>>() / 5.0;

        // Shift so centroid is at origin
        let shifted: Vec<Vector4<f64>> = vertices.iter().map(|v| v - centroid).collect();

        // For each facet (omitting one vertex), compute normal
        let mut normals = Vec::new();
        let mut heights = Vec::new();

        for omit in 0..5 {
            // Get 4 vertices (all except omit)
            let face_verts: Vec<&Vector4<f64>> = shifted
                .iter()
                .enumerate()
                .filter(|(i, _)| *i != omit)
                .map(|(_, v)| v)
                .collect();

            // Compute normal via cross product in 4D
            // n = (v1-v0) × (v2-v0) × (v3-v0) in 4D sense
            let e1 = face_verts[1] - face_verts[0];
            let e2 = face_verts[2] - face_verts[0];
            let e3 = face_verts[3] - face_verts[0];

            // 4D "cross product" - compute determinant-based normal
            let n = Vector4::new(
                e1[1] * (e2[2] * e3[3] - e2[3] * e3[2]) - e1[2] * (e2[1] * e3[3] - e2[3] * e3[1])
                    + e1[3] * (e2[1] * e3[2] - e2[2] * e3[1]),
                -(e1[0] * (e2[2] * e3[3] - e2[3] * e3[2])
                    - e1[2] * (e2[0] * e3[3] - e2[3] * e3[0])
                    + e1[3] * (e2[0] * e3[2] - e2[2] * e3[0])),
                e1[0] * (e2[1] * e3[3] - e2[3] * e3[1]) - e1[1] * (e2[0] * e3[3] - e2[3] * e3[0])
                    + e1[3] * (e2[0] * e3[1] - e2[1] * e3[0]),
                -(e1[0] * (e2[1] * e3[2] - e2[2] * e3[1])
                    - e1[1] * (e2[0] * e3[2] - e2[2] * e3[0])
                    + e1[2] * (e2[0] * e3[1] - e2[1] * e3[0])),
            );

            let norm = n.norm();
            if norm < 1e-10 {
                continue;
            }
            let mut normal = n / norm;

            // Ensure outward pointing (away from omitted vertex)
            let omitted = &shifted[omit];
            if normal.dot(omitted) > normal.dot(face_verts[0]) {
                normal = -normal;
            }

            // Height = distance from origin to hyperplane
            let height = normal.dot(face_verts[0]);
            if height < 0.0 {
                normal = -normal;
            }
            let height = height.abs();

            normals.push(normal);
            heights.push(height);
        }

        PolytopeHRep::new(normals, heights)
    }

    #[test]
    fn test_simplex_naive_and_graph_pruned_agree() {
        // This test ensures the constraint verification fix works.
        // Before the fix, naive and graph_pruned gave different results
        // because infeasible permutations (violating constraints) weren't
        // properly rejected.
        let polytope = make_simplex();

        let result_naive = hk2017_capacity(&polytope, &Hk2017Config::naive()).unwrap();
        let result_graph = hk2017_capacity(&polytope, &Hk2017Config::graph_pruned()).unwrap();

        assert_relative_eq!(result_naive.capacity, result_graph.capacity, epsilon = 1e-6);
        assert_relative_eq!(result_naive.q_max, result_graph.q_max, epsilon = 1e-6);
    }

    #[test]
    fn test_result_satisfies_constraints() {
        // Verify that the returned solution actually satisfies the constraints:
        // 1. β_i >= 0
        // 2. Σ β_i h_i = 1
        // 3. Σ β_i n_i = 0
        let polytope = make_simplex();
        let result = hk2017_capacity(&polytope, &Hk2017Config::naive()).unwrap();

        let facet_data = crate::types::FacetData::from_polytope(&polytope).unwrap();

        // Check β >= 0
        for &b in &result.optimal_beta {
            assert!(b >= -1e-9, "β should be non-negative, got {}", b);
        }

        // Check height constraint: Σ β_i h_i = 1
        let height_sum: f64 = result
            .optimal_beta
            .iter()
            .zip(facet_data.heights.iter())
            .map(|(&b, &h)| b * h)
            .sum();
        assert_relative_eq!(height_sum, 1.0, epsilon = 1e-6);

        // Check closure constraint: Σ β_i n_i = 0
        let mut closure = Vector4::zeros();
        for (i, &b) in result.optimal_beta.iter().enumerate() {
            closure += &facet_data.normals[i] * b;
        }
        assert!(
            closure.norm() < 1e-6,
            "Closure should be ~0, got norm {}",
            closure.norm()
        );
    }

    #[test]
    fn test_simplex_rejects_infeasible_permutations() {
        // For a general-position simplex, most small permutations (k < 5)
        // cannot satisfy the closure constraint and should be rejected.
        let polytope = make_simplex();
        let result = hk2017_capacity(&polytope, &Hk2017Config::naive()).unwrap();

        // With 5 facets, naive enumerates 320 permutations
        // Most should be rejected (constraint violations + negative beta + etc)
        assert!(
            result.permutations_rejected > result.permutations_evaluated / 2,
            "Expected most permutations to be rejected for simplex. \
             Evaluated: {}, Rejected: {}",
            result.permutations_evaluated,
            result.permutations_rejected
        );

        // The optimal permutation should use all or most facets
        // (small permutations can't satisfy closure for general position)
        assert!(
            result.optimal_permutation.len() >= 4,
            "Optimal should use at least 4 facets, got {}",
            result.optimal_permutation.len()
        );
    }
}
