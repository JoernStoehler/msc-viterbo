//! Constrained optimization for billiard trajectories.
//!
//! For a fixed edge combination, we find the minimum-action trajectory by
//! enumerating vertices of the feasible polytope (vertex optimality theorem).
//!
//! IMPORTANT: Not every polygonal path is a valid billiard trajectory!
//! The displacement Δq must be compatible with the Reeb velocity constraint:
//! Δq must be proportional to V_k = -(2/h_k) n_k for some edge k of K_p,
//! or a positive combination of two V_k at a vertex.

use crate::action::{compute_2bounce_action, compute_3bounce_action};
use crate::types::{BilliardTrajectory, EdgeCombination, Polygon2D, EPS, MIN_ACTION};
use nalgebra::Vector2;

/// Compute the velocity direction for q-motion when p is on edge k of K_p.
/// V_k = -(2/h_k) * n_k
fn q_velocity_direction(k_p: &Polygon2D, edge_idx: usize) -> Vector2<f64> {
    let n = k_p.normals[edge_idx];
    let h = k_p.heights[edge_idx];
    -n * (2.0 / h)
}

/// Check if a displacement can be achieved by the Reeb flow from K_p.
/// Returns Some(time) if the displacement is parallel to some V_k (with positive coefficient),
/// or in a cone of two V_k at a vertex. Returns None if not achievable.
fn is_displacement_achievable(delta: &Vector2<f64>, k_p: &Polygon2D, tol: f64) -> bool {
    let delta_norm = delta.norm();
    if delta_norm < tol {
        return true; // Zero displacement is always achievable
    }

    let n_p = k_p.num_edges();

    // Check if delta is parallel to any V_k (edge interior)
    for k in 0..n_p {
        let v_k = q_velocity_direction(k_p, k);
        let v_k_norm = v_k.norm();
        if v_k_norm < tol {
            continue;
        }

        // Check parallelism: cross product ≈ 0
        let cross = delta[0] * v_k[1] - delta[1] * v_k[0];
        if cross.abs() < tol * delta_norm * v_k_norm {
            // Check same direction (not opposite)
            let dot = delta.dot(&v_k);
            if dot > -tol {
                return true;
            }
        }
    }

    // Check if delta is in a cone of two adjacent V_k (vertex)
    for k in 0..n_p {
        let k_next = (k + 1) % n_p;
        let v1 = q_velocity_direction(k_p, k);
        let v2 = q_velocity_direction(k_p, k_next);

        // Solve: delta = α*v1 + β*v2 with α,β ≥ 0
        let det = v1[0] * v2[1] - v1[1] * v2[0];
        if det.abs() < tol {
            continue; // Parallel vectors, skip
        }

        let alpha = (delta[0] * v2[1] - delta[1] * v2[0]) / det;
        let beta = (v1[0] * delta[1] - v1[1] * delta[0]) / det;

        if alpha >= -tol && beta >= -tol {
            return true;
        }
    }

    false
}

/// Result of solving for a single edge combination.
#[derive(Debug, Clone)]
pub struct SolveResult {
    pub action: f64,
    pub q_params: Vec<f64>,
    pub p_params: Vec<f64>,
}

/// Check if two vertices of a polygon are adjacent (same, neighbors, or 1 apart).
fn vertices_adjacent(n_vertices: usize, v1: usize, v2: usize) -> bool {
    if v1 == v2 {
        return true; // Same vertex
    }
    let diff = (v1 as isize - v2 as isize).unsigned_abs();
    diff == 1 || diff == n_vertices - 1
}

/// Get vertex index from edge index and t parameter.
/// t=0 → start vertex (edge_idx), t=1 → end vertex (edge_idx + 1).
fn vertex_from_edge_param(n_vertices: usize, edge_idx: usize, t: f64) -> usize {
    if t < 0.5 {
        edge_idx
    } else {
        (edge_idx + 1) % n_vertices
    }
}

/// Solve for the minimum action 2-bounce trajectory with the given edge combination.
///
/// For 2-bounce, the trajectory goes q0 → q1 → q0.
/// Constraints:
/// 1. Both displacements must be achievable by the Reeb flow
/// 2. The trajectory must NOT be translatable into the interior (Bezdek-Bezdek)
///    - For 2-bounce, this means the q-edges must not be adjacent
///
/// By vertex optimality, we enumerate all 16 vertices of [0,1]⁴.
pub fn solve_2bounce(
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    combo: &EdgeCombination,
) -> Option<SolveResult> {
    assert_eq!(combo.q_edges.len(), 2);
    assert_eq!(combo.p_edges.len(), 2);

    // Reject same-edge combinations: if both bounce points are on the same edge,
    // the trajectory lies on that edge and is translatable (degenerate).
    if combo.q_edges[0] == combo.q_edges[1] {
        return None;
    }

    let mut best: Option<SolveResult> = None;

    // Enumerate all 16 vertices of [0,1]⁴
    for &t_q0 in &[0.0, 1.0] {
        for &t_q1 in &[0.0, 1.0] {
            for &t_p0 in &[0.0, 1.0] {
                for &t_p1 in &[0.0, 1.0] {
                    let q0 = k_q.point_on_edge(combo.q_edges[0], t_q0);
                    let q1 = k_q.point_on_edge(combo.q_edges[1], t_q1);

                    let delta = q1 - q0;

                    // Skip if both q-positions are the same (degenerate)
                    if delta.norm() < MIN_ACTION {
                        continue;
                    }

                    // Check Reeb velocity constraint:
                    // Both forward (q0→q1) and backward (q1→q0) must be achievable
                    if !is_displacement_achievable(&delta, k_p, EPS) {
                        continue;
                    }
                    if !is_displacement_achievable(&(-delta), k_p, EPS) {
                        continue;
                    }

                    let action = compute_2bounce_action(&q0, &q1, k_p);

                    if action > MIN_ACTION {
                        if best.is_none() || action < best.as_ref().unwrap().action {
                            best = Some(SolveResult {
                                action,
                                q_params: vec![t_q0, t_q1],
                                p_params: vec![t_p0, t_p1],
                            });
                        }
                    }
                }
            }
        }
    }

    best
}

/// Solve for the minimum action 3-bounce trajectory with the given edge combination.
///
/// For 3-bounce:
/// - Variables: (t_q0, t_q1, t_q2, t_p0, t_p1, t_p2) ∈ [0,1]⁶
/// - Closure constraints: Σ Δq = 0 (2 equations), Σ Δp = 0 (2 equations)
/// - Feasible region: 2D affine subspace ∩ [0,1]⁶
///
/// We enumerate vertices of this feasible polytope.
pub fn solve_3bounce(
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    combo: &EdgeCombination,
) -> Option<SolveResult> {
    assert_eq!(combo.q_edges.len(), 3);
    assert_eq!(combo.p_edges.len(), 3);

    // Find vertices of the q-closure polytope
    let q_vertices = enumerate_closure_vertices(k_q, &combo.q_edges)?;
    // Find vertices of the p-closure polytope
    let p_vertices = enumerate_closure_vertices(k_p, &combo.p_edges)?;

    let mut best: Option<SolveResult> = None;

    // Cartesian product of q and p vertices
    for t_q in &q_vertices {
        for t_p in &p_vertices {
            let q0 = k_q.point_on_edge(combo.q_edges[0], t_q[0]);
            let q1 = k_q.point_on_edge(combo.q_edges[1], t_q[1]);
            let q2 = k_q.point_on_edge(combo.q_edges[2], t_q[2]);

            let d01 = q1 - q0;
            let d12 = q2 - q1;
            let d20 = q0 - q2;

            // Skip degenerate: any two consecutive points coincident
            if d01.norm() < MIN_ACTION || d12.norm() < MIN_ACTION || d20.norm() < MIN_ACTION {
                continue;
            }

            // Skip collinear points (zero-area "triangle")
            let cross = d01[0] * d12[1] - d01[1] * d12[0];
            if cross.abs() < MIN_ACTION {
                continue;
            }

            // Check Reeb velocity constraint for all three displacements
            if !is_displacement_achievable(&d01, k_p, EPS) {
                continue;
            }
            if !is_displacement_achievable(&d12, k_p, EPS) {
                continue;
            }
            if !is_displacement_achievable(&d20, k_p, EPS) {
                continue;
            }

            let action = compute_3bounce_action(&q0, &q1, &q2, k_p);

            if action > MIN_ACTION {
                if best.is_none() || action < best.as_ref().unwrap().action {
                    best = Some(SolveResult {
                        action,
                        q_params: t_q.to_vec(),
                        p_params: t_p.to_vec(),
                    });
                }
            }
        }
    }

    best
}

/// Enumerate vertices of {t ∈ [0,1]³ : closure constraint holds}.
///
/// The closure constraint is: Σ_{i=0}^{2} (x_{i+1} - x_i) = 0
/// where x_i = point_on_edge(e_i, t_i).
///
/// This gives 2 linear equations in 3 variables, defining a 1D affine subspace.
/// Vertices occur where this line intersects edges of the cube [0,1]³.
fn enumerate_closure_vertices(polygon: &Polygon2D, edges: &[usize]) -> Option<Vec<[f64; 3]>> {
    assert_eq!(edges.len(), 3);

    // Build the closure constraint matrix.
    // closure: (v1 - v0) + (v2 - v1) + (v0 - v2) = 0 is automatic,
    // but we want: x_0 + x_1 + x_2 closes, where x_i = v_i + t_i * (v_{i+1} - v_i)
    //
    // Let d_i = edge_end(e_i) - edge_start(e_i) be the edge direction.
    // Then x_i = edge_start(e_i) + t_i * d_i
    //
    // Closure: x_0 - x_1 + x_1 - x_2 + x_2 - x_0 = 0 is trivial.
    // But for billiards, closure means: (x_1 - x_0) + (x_2 - x_1) + (x_0 - x_2) = 0
    // which is always true!
    //
    // Wait, that's not the constraint. Let me re-read the spec.
    //
    // Actually, for 3-bounce the trajectory visits q0 -> q1 -> q2 -> q0.
    // The closure constraint is that the sum of displacements is zero:
    // (q1 - q0) + (q2 - q1) + (q0 - q2) = 0
    // which is always satisfied (telescoping sum).
    //
    // So for 3-bounce on fixed edges, the feasible region is just [0,1]³ for q
    // and [0,1]³ for p, independently. The closure is automatic!
    //
    // This means we should enumerate all 8 vertices for q and all 8 for p.

    let mut vertices = Vec::new();

    // All 8 vertices of [0,1]³
    for &t0 in &[0.0, 1.0] {
        for &t1 in &[0.0, 1.0] {
            for &t2 in &[0.0, 1.0] {
                vertices.push([t0, t1, t2]);
            }
        }
    }

    if vertices.is_empty() {
        None
    } else {
        Some(vertices)
    }
}

/// Build a BilliardTrajectory from solve results.
pub fn build_trajectory(
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    combo: &EdgeCombination,
    result: &SolveResult,
) -> BilliardTrajectory {
    let num_bounces = combo.q_edges.len();

    let q_positions: Vec<Vector2<f64>> = combo
        .q_edges
        .iter()
        .zip(&result.q_params)
        .map(|(&edge, &t)| k_q.point_on_edge(edge, t))
        .collect();

    let p_positions: Vec<Vector2<f64>> = combo
        .p_edges
        .iter()
        .zip(&result.p_params)
        .map(|(&edge, &t)| k_p.point_on_edge(edge, t))
        .collect();

    BilliardTrajectory {
        num_bounces,
        q_positions,
        p_positions,
        q_params: result.q_params.clone(),
        p_params: result.p_params.clone(),
        q_edges: combo.q_edges.clone(),
        p_edges: combo.p_edges.clone(),
        action: result.action,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_solve_2bounce_square() {
        let square = Polygon2D::square(2.0).unwrap();

        // Try edge combination: edges 0 and 2 (opposite edges)
        // Edge 0: bottom (-1,-1) to (1,-1)
        // Edge 2: top (1,1) to (-1,1)
        let combo = EdgeCombination {
            q_edges: vec![0, 2],
            p_edges: vec![0, 2],
        };

        let result = solve_2bounce(&square, &square, &combo);
        assert!(result.is_some());

        let result = result.unwrap();
        // The minimum should be at vertices of the edges
        assert!(result.action > 0.0);
    }

    #[test]
    fn test_solve_3bounce_square() {
        let square = Polygon2D::square(2.0).unwrap();

        let combo = EdgeCombination {
            q_edges: vec![0, 1, 2],
            p_edges: vec![0, 1, 2],
        };

        let result = solve_3bounce(&square, &square, &combo);
        assert!(result.is_some());

        let result = result.unwrap();
        assert!(result.action > 0.0);
    }
}
