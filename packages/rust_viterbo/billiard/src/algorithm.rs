//! Main billiard algorithm for computing EHZ capacity.
//!
//! The algorithm enumerates all edge combinations for 2-bounce and 3-bounce
//! trajectories, and finds the minimum action.

use crate::solve::{build_trajectory, solve_2bounce, solve_3bounce};
use crate::types::{BilliardError, BilliardResult, EdgeCombination, LagrangianProduct, Polygon2D};
use itertools::iproduct;

/// Compute the EHZ capacity of a Lagrangian product using the billiard algorithm.
///
/// This is the main entry point for the billiard algorithm.
pub fn billiard_capacity(product: &LagrangianProduct) -> Result<BilliardResult, BilliardError> {
    billiard_capacity_from_polygons(&product.k_q, &product.k_p)
}

/// Compute the EHZ capacity given two polygons directly.
pub fn billiard_capacity_from_polygons(
    k_q: &Polygon2D,
    k_p: &Polygon2D,
) -> Result<BilliardResult, BilliardError> {
    k_q.validate()?;
    k_p.validate()?;

    let n_q = k_q.num_edges();
    let n_p = k_p.num_edges();

    let mut best_result: Option<BilliardResult> = None;
    let mut combinations_evaluated = 0;

    // Enumerate 2-bounce trajectories
    for (eq0, eq1) in iproduct!(0..n_q, 0..n_q) {
        for (ep0, ep1) in iproduct!(0..n_p, 0..n_p) {
            let combo = EdgeCombination {
                q_edges: vec![eq0, eq1],
                p_edges: vec![ep0, ep1],
            };

            combinations_evaluated += 1;

            if let Some(solve_result) = solve_2bounce(k_q, k_p, &combo) {
                let trajectory = build_trajectory(k_q, k_p, &combo, &solve_result);

                if best_result.is_none()
                    || solve_result.action < best_result.as_ref().unwrap().capacity
                {
                    best_result = Some(BilliardResult {
                        capacity: solve_result.action,
                        witness: trajectory,
                        combinations_evaluated,
                    });
                }
            }
        }
    }

    // Enumerate 3-bounce trajectories
    for (eq0, eq1, eq2) in iproduct!(0..n_q, 0..n_q, 0..n_q) {
        for (ep0, ep1, ep2) in iproduct!(0..n_p, 0..n_p, 0..n_p) {
            let combo = EdgeCombination {
                q_edges: vec![eq0, eq1, eq2],
                p_edges: vec![ep0, ep1, ep2],
            };

            combinations_evaluated += 1;

            if let Some(solve_result) = solve_3bounce(k_q, k_p, &combo) {
                let trajectory = build_trajectory(k_q, k_p, &combo, &solve_result);

                if best_result.is_none()
                    || solve_result.action < best_result.as_ref().unwrap().capacity
                {
                    best_result = Some(BilliardResult {
                        capacity: solve_result.action,
                        witness: trajectory,
                        combinations_evaluated,
                    });
                }
            }
        }
    }

    // Update final combination count
    if let Some(ref mut result) = best_result {
        result.combinations_evaluated = combinations_evaluated;
    }

    best_result.ok_or(BilliardError::NoValidTrajectory)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polygon::Polygon2D;
    use approx::assert_relative_eq;
    use std::f64::consts::PI;

    #[test]
    fn test_tesseract_capacity() {
        // Tesseract [-1,1]^4 = Square × Square
        // Known capacity = 4.0 (HK2017 Example 4.6)
        let square = Polygon2D::square(2.0).unwrap();

        let result = billiard_capacity_from_polygons(&square, &square).unwrap();

        assert_relative_eq!(result.capacity, 4.0, epsilon = 1e-6);
        assert_eq!(result.witness.num_bounces, 2);
    }

    #[test]
    fn test_pentagon_counterexample() {
        // Pentagon × RotatedPentagon(90°)
        // Expected capacity: 2*cos(π/10)*(1 + cos(π/5)) ≈ 3.441
        let pentagon = Polygon2D::regular_pentagon();
        let rotated = pentagon.rotate(PI / 2.0);

        // Debug: manually compute the diagonal action
        let v0 = pentagon.vertices[0];
        let v2 = pentagon.vertices[2];
        let diagonal_action = crate::action::compute_2bounce_action(&v0, &v2, &rotated);
        println!("Manual diagonal action (v0 to v2): {}", diagonal_action);

        // Debug: check what we get for edge combo (0, 2) at t=(0,0)
        let q0 = pentagon.point_on_edge(0, 0.0);
        let q1 = pentagon.point_on_edge(2, 0.0);
        println!("q0 from edge 0, t=0: {:?}", q0);
        println!("q1 from edge 2, t=0: {:?}", q1);
        println!("v0={:?}, v2={:?}", v0, v2);

        // Debug: check Reeb constraint for the edge v0→v1
        let edge_delta = pentagon.vertices[1] - pentagon.vertices[0];
        println!("Edge delta (v0→v1): {:?}", edge_delta);

        // Print the velocity directions from rotated pentagon
        println!("Velocity directions from T (rotated pentagon):");
        for k in 0..5 {
            let n = rotated.normals[k];
            let h = rotated.heights[k];
            let v_k = -n * (2.0 / h);
            println!("  V_{} = {:?} (from n={:?}, h={})", k, v_k, n, h);
        }

        let result = billiard_capacity_from_polygons(&pentagon, &rotated).unwrap();

        println!("Found capacity: {}", result.capacity);
        println!("Witness: {} bounces", result.witness.num_bounces);
        println!("  q_edges: {:?}", result.witness.q_edges);
        println!("  q_params: {:?}", result.witness.q_params);
        println!("  q_positions: {:?}", result.witness.q_positions);

        let expected = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());

        assert_relative_eq!(result.capacity, expected, epsilon = 1e-6);
    }

    #[test]
    fn test_scaling_axiom() {
        // c(λK_q × λK_p) = λ² c(K_q × K_p)
        let square = Polygon2D::square(2.0).unwrap();
        let lambda = 2.0;

        let c_base = billiard_capacity_from_polygons(&square, &square)
            .unwrap()
            .capacity;

        let scaled_q = square.scale(lambda);
        let scaled_p = square.scale(lambda);

        let c_scaled = billiard_capacity_from_polygons(&scaled_q, &scaled_p)
            .unwrap()
            .capacity;

        assert_relative_eq!(c_scaled, lambda * lambda * c_base, epsilon = 1e-6);
    }
}
