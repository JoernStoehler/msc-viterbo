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
        // Pentagon × RotatedPentagon(90°) from HK-O 2024 counterexample paper.
        // The minimum is a 2-bounce diagonal trajectory v0 → v2 → v0.
        // Expected capacity: 2*cos(π/10)*(1 + cos(π/5)) ≈ 3.441
        let pentagon = Polygon2D::regular_pentagon();
        let rotated = pentagon.rotate(PI / 2.0);

        let result = billiard_capacity_from_polygons(&pentagon, &rotated).unwrap();

        let expected = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());
        assert_relative_eq!(result.capacity, expected, epsilon = 1e-6);
        assert_eq!(result.witness.num_bounces, 2);
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

/// Integration tests comparing billiard and HK2017 algorithms.
///
/// These tests verify that both algorithms produce the same capacity
/// for Lagrangian products where both can be applied.
#[cfg(test)]
mod hk2017_comparison_tests {
    use super::*;
    use crate::polygon::Polygon2D;
    use crate::types::LagrangianProduct;
    use approx::assert_relative_eq;
    use hk2017::{hk2017_capacity, Hk2017Config, PolytopeHRep};

    /// Helper to run both algorithms and compare results.
    fn compare_algorithms(k_q: &Polygon2D, k_p: &Polygon2D, tolerance: f64) {
        // Run billiard algorithm
        let billiard_result = billiard_capacity_from_polygons(k_q, k_p)
            .expect("billiard should succeed");

        // Convert to H-rep for HK2017
        let product = LagrangianProduct::new(k_q.clone(), k_p.clone())
            .expect("valid product");
        let (normals, heights) = product.to_hrep();
        let polytope = PolytopeHRep::new(normals, heights);

        // Run HK2017 algorithm
        let hk_result = hk2017_capacity(&polytope, &Hk2017Config::naive())
            .expect("hk2017 should succeed");

        // Compare capacities
        assert_relative_eq!(
            billiard_result.capacity,
            hk_result.capacity,
            epsilon = tolerance,
            max_relative = tolerance
        );
    }

    #[test]
    fn test_tesseract_both_algorithms() {
        // Tesseract = Square × Square, capacity = 4.0
        let square = Polygon2D::square(2.0).unwrap();
        compare_algorithms(&square, &square, 1e-6);
    }

    #[test]
    fn test_rectangle_product_both_algorithms() {
        // Rectangle × Square
        // Rectangle with half-widths (1, 2), Square with half-width 1
        let rect = Polygon2D::from_vertices(vec![
            nalgebra::Vector2::new(-1.0, -2.0),
            nalgebra::Vector2::new(1.0, -2.0),
            nalgebra::Vector2::new(1.0, 2.0),
            nalgebra::Vector2::new(-1.0, 2.0),
        ])
        .unwrap();
        let square = Polygon2D::square(2.0).unwrap();

        compare_algorithms(&rect, &square, 1e-6);
    }

    #[test]
    fn test_square_product_scaled() {
        // Scaled tesseract: (2*Square) × (2*Square)
        // Capacity should be 4 * 4.0 = 16.0 by scaling axiom
        let square = Polygon2D::square(2.0).unwrap();
        let scaled = square.scale(2.0);

        compare_algorithms(&scaled, &scaled, 1e-6);
    }

    #[test]
    fn test_different_squares() {
        // Small Square × Large Square
        let small = Polygon2D::square(1.0).unwrap();
        let large = Polygon2D::square(4.0).unwrap();

        compare_algorithms(&small, &large, 1e-6);
    }
}
