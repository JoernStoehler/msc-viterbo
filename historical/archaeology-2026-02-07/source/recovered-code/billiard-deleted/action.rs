//! Action computation for billiard trajectories using support functions.

use crate::polygon::t_dual_length;
use crate::types::Polygon2D;
use nalgebra::Vector2;

/// Compute the action of a trajectory given q-positions and the p-polygon.
///
/// The action is the sum of T°-lengths of the q-displacements.
pub fn compute_action(q_positions: &[Vector2<f64>], k_p: &Polygon2D) -> f64 {
    let k = q_positions.len();
    if k < 2 {
        return 0.0;
    }

    let mut action = 0.0;
    for i in 0..k {
        let q_i = q_positions[i];
        let q_next = q_positions[(i + 1) % k];
        let displacement = q_next - q_i;
        action += t_dual_length(&displacement, k_p);
    }
    action
}

/// Compute the action for a 2-bounce trajectory.
///
/// A 2-bounce trajectory goes q0 → q1 → q0, so the action is:
/// 2 * ||q1 - q0||_{K_p°}
pub fn compute_2bounce_action(q0: &Vector2<f64>, q1: &Vector2<f64>, k_p: &Polygon2D) -> f64 {
    let displacement = *q1 - *q0;
    // Forward and backward both contribute
    t_dual_length(&displacement, k_p) + t_dual_length(&(-displacement), k_p)
}

/// Compute the action for a 3-bounce trajectory.
pub fn compute_3bounce_action(
    q0: &Vector2<f64>,
    q1: &Vector2<f64>,
    q2: &Vector2<f64>,
    k_p: &Polygon2D,
) -> f64 {
    let d01 = *q1 - *q0;
    let d12 = *q2 - *q1;
    let d20 = *q0 - *q2;
    t_dual_length(&d01, k_p) + t_dual_length(&d12, k_p) + t_dual_length(&d20, k_p)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::Polygon2D;
    use approx::assert_relative_eq;

    #[test]
    fn test_2bounce_action_square() {
        // For a square K_p = [-1,1]², the support function is
        // h(v) = |v_x| + |v_y| (since vertices are at (±1, ±1))
        // Wait, that's not right. For square with vertices at corners,
        // h(v) = max over vertices of ⟨v, vertex⟩
        // For v = (1, 0), max is at (1, 1) or (1, -1), giving 1.
        // For v = (1, 1), max is at (1, 1), giving 2.

        let square = Polygon2D::square(2.0).unwrap(); // [-1,1]²

        // 2-bounce along x-axis: q0 = (-1, 0), q1 = (1, 0)
        let q0 = Vector2::new(-1.0, 0.0);
        let q1 = Vector2::new(1.0, 0.0);

        // displacement = (2, 0)
        // h_{square}((2, 0)) = max(⟨(2,0), v⟩ for v ∈ vertices)
        //                    = max(2*1, 2*(-1), ...) = 2
        // h_{square}((-2, 0)) = max(⟨(-2,0), v⟩) = max(-2, 2, ...) = 2
        // Total action = 2 + 2 = 4

        let action = compute_2bounce_action(&q0, &q1, &square);
        assert_relative_eq!(action, 4.0, epsilon = 1e-9);
    }

    #[test]
    fn test_action_zero_displacement() {
        let square = Polygon2D::square(2.0).unwrap();
        let q = Vector2::new(0.0, 0.0);
        let action = compute_2bounce_action(&q, &q, &square);
        assert_relative_eq!(action, 0.0, epsilon = 1e-9);
    }

    #[test]
    fn test_pentagon_diagonal_action() {
        use std::f64::consts::PI;

        // Pentagon K with vertices at (cos(2πk/5), sin(2πk/5))
        // T = K rotated by 90°
        // The diagonal v0→v2→v0 has action = 2*cos(π/10)*(1 + cos(π/5)) ≈ 3.441
        let pentagon = Polygon2D::regular_pentagon();
        let t = pentagon.rotate(PI / 2.0);

        let v0 = pentagon.vertices[0];
        let v2 = pentagon.vertices[2];
        let action = compute_2bounce_action(&v0, &v2, &t);

        let expected = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());
        assert_relative_eq!(action, expected, epsilon = 1e-9);
    }
}
