//! Constrained optimization for billiard trajectories.
//!
//! For a fixed edge combination, we find the minimum-action trajectory by
//! enumerating vertices of the feasible polytope (vertex optimality theorem).
//!
//! IMPORTANT: Not every polygonal path is a valid billiard trajectory!
//! A valid 2-bounce trajectory has 4 affine segments:
//!   1. q at q₀ (q-facet phase): p moves from p_back to p_fwd
//!   2. p at p_fwd (p-facet phase): q moves from q₀ to q₁
//!   3. q at q₁ (q-facet phase): p moves from p_fwd to p_back
//!   4. p at p_back (p-facet phase): q moves from q₁ to q₀
//!
//! The differential inclusion requires:
//! - On p-facets: q̇ ∈ cone of -(2/h_k) n_k for active p-edges
//! - On q-facets: ṗ ∈ cone of (2/h_k) n_k for active q-edges

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

/// Compute the velocity direction for p-motion when q is on edge k of K_q.
/// W_k = (2/h_k) * n_k
fn p_velocity_direction(k_q: &Polygon2D, edge_idx: usize) -> Vector2<f64> {
    let n = k_q.normals[edge_idx];
    let h = k_q.heights[edge_idx];
    n * (2.0 / h)
}

/// Find where p must be on ∂K_p to achieve q-motion direction delta.
/// Returns Some((edge_idx, t)) if achievable:
/// - t = 0.5 means interior of edge (p on edge edge_idx)
/// - t = 0.0 means at vertex edge_idx (start of edge)
/// - t = 1.0 means at vertex edge_idx + 1 (end of edge)
/// Returns None if not achievable.
fn find_p_position_for_q_motion(
    delta: &Vector2<f64>,
    k_p: &Polygon2D,
    tol: f64,
) -> Option<(usize, f64)> {
    let delta_norm = delta.norm();
    if delta_norm < tol {
        return Some((0, 0.0)); // Zero displacement, any position works
    }

    let n_p = k_p.num_edges();

    // Check if delta is parallel to any V_k (p on edge interior)
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
                return Some((k, 0.5)); // p on edge k interior
            }
        }
    }

    // Check if delta is in a cone of two adjacent V_k (p at vertex)
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
            // p must be at vertex k+1 (end of edge k, start of edge k+1)
            return Some((k, 1.0));
        }
    }

    None
}

/// Check if p-motion delta_p is achievable when q is at a vertex of K_q.
/// q at vertex v means q is on edges (v-1) and v (mod n).
/// Allowed ṗ direction is in cone(W_{v-1}, W_v) where W_k = (2/h_k)*n_k.
fn is_p_motion_achievable_at_vertex(
    delta_p: &Vector2<f64>,
    k_q: &Polygon2D,
    vertex_idx: usize,
    tol: f64,
) -> bool {
    let delta_norm = delta_p.norm();
    if delta_norm < tol {
        return true; // Zero displacement is always achievable
    }

    let n_q = k_q.num_edges();
    let edge_before = (vertex_idx + n_q - 1) % n_q;
    let edge_after = vertex_idx;

    let w1 = p_velocity_direction(k_q, edge_before);
    let w2 = p_velocity_direction(k_q, edge_after);

    // Solve: delta_p = α*w1 + β*w2 with α,β ≥ 0
    let det = w1[0] * w2[1] - w1[1] * w2[0];
    if det.abs() < tol {
        // Parallel vectors - check if delta_p is parallel to either
        let cross1 = delta_p[0] * w1[1] - delta_p[1] * w1[0];
        let cross2 = delta_p[0] * w2[1] - delta_p[1] * w2[0];
        if cross1.abs() < tol * delta_norm * w1.norm() && delta_p.dot(&w1) > -tol {
            return true;
        }
        if cross2.abs() < tol * delta_norm * w2.norm() && delta_p.dot(&w2) > -tol {
            return true;
        }
        return false;
    }

    let alpha = (delta_p[0] * w2[1] - delta_p[1] * w2[0]) / det;
    let beta = (w1[0] * delta_p[1] - w1[1] * delta_p[0]) / det;

    alpha >= -tol && beta >= -tol
}

/// Result of solving for a single edge combination.
#[derive(Debug, Clone)]
pub struct SolveResult {
    pub action: f64,
    pub q_params: Vec<f64>,
    pub p_params: Vec<f64>,
}

/// Validate that a full 2-bounce orbit (4 segments) is achievable.
///
/// The 4 segments are:
/// 1. q at q₀: p moves from p_back to p_fwd
/// 2. p at p_fwd: q moves from q₀ to q₁
/// 3. q at q₁: p moves from p_fwd to p_back
/// 4. p at p_back: q moves from q₁ to q₀
///
/// Returns Some((p_fwd_pos, p_back_pos)) if valid, None otherwise.
fn validate_2bounce_orbit(
    q0: &Vector2<f64>,
    q1: &Vector2<f64>,
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    q0_vertex: usize, // vertex index of q₀ in K_q
    q1_vertex: usize, // vertex index of q₁ in K_q
) -> Option<(Vector2<f64>, Vector2<f64>)> {
    let delta = *q1 - *q0;
    if delta.norm() < MIN_ACTION {
        return None;
    }

    // Find where p must be during forward q-motion (q₀ → q₁)
    let p_fwd_info = find_p_position_for_q_motion(&delta, k_p, EPS)?;

    // Find where p must be during backward q-motion (q₁ → q₀)
    let p_back_info = find_p_position_for_q_motion(&(-delta), k_p, EPS)?;

    // Get the actual p positions
    let p_fwd = get_p_position(k_p, p_fwd_info);
    let p_back = get_p_position(k_p, p_back_info);

    // At q₁: p must transition from p_fwd to p_back
    // This delta_p must be achievable with the ṗ constraint at q₁
    let delta_p_at_q1 = p_back - p_fwd;
    if !is_p_motion_achievable_at_vertex(&delta_p_at_q1, k_q, q1_vertex, EPS) {
        return None;
    }

    // At q₀: p must transition from p_back to p_fwd
    // This delta_p must be achievable with the ṗ constraint at q₀
    let delta_p_at_q0 = p_fwd - p_back;
    if !is_p_motion_achievable_at_vertex(&delta_p_at_q0, k_q, q0_vertex, EPS) {
        return None;
    }

    Some((p_fwd, p_back))
}

/// Get the p position from the (edge_idx, t) info returned by find_p_position_for_q_motion.
fn get_p_position(k_p: &Polygon2D, info: (usize, f64)) -> Vector2<f64> {
    let (edge_idx, t) = info;
    if (t - 0.5).abs() < EPS {
        // Edge interior - use midpoint for a representative position
        k_p.point_on_edge(edge_idx, 0.5)
    } else if t < 0.25 {
        // Vertex at start of edge
        k_p.vertices[edge_idx]
    } else {
        // Vertex at end of edge (t ≈ 1.0)
        k_p.vertices[(edge_idx + 1) % k_p.num_vertices()]
    }
}

/// Solve for the minimum action 2-bounce trajectory with the given edge combination.
///
/// For 2-bounce, the trajectory has 4 segments:
/// 1. q at q₀: p moves
/// 2. p fixed: q moves q₀ → q₁
/// 3. q at q₁: p moves
/// 4. p fixed: q moves q₁ → q₀
///
/// Constraints:
/// 1. Both q-displacements must be achievable by the Reeb flow
/// 2. Both p-transitions at the bounces must be achievable by the Reeb flow
///
/// By vertex optimality, we enumerate all 4 vertices of [0,1]² for q-parameters.
pub fn solve_2bounce(
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    combo: &EdgeCombination,
) -> Option<SolveResult> {
    assert_eq!(combo.q_edges.len(), 2);
    assert_eq!(combo.p_edges.len(), 2);

    // Reject same-edge combinations: if both bounce points are on the same edge,
    // the trajectory lies on that edge (degenerate).
    if combo.q_edges[0] == combo.q_edges[1] {
        return None;
    }

    let n_q = k_q.num_vertices();
    let mut best: Option<SolveResult> = None;

    // Enumerate all 4 vertices of [0,1]² for q-parameters
    // (p-parameters are determined by the q-motion constraints)
    for &t_q0 in &[0.0, 1.0] {
        for &t_q1 in &[0.0, 1.0] {
            let q0 = k_q.point_on_edge(combo.q_edges[0], t_q0);
            let q1 = k_q.point_on_edge(combo.q_edges[1], t_q1);

            // Get vertex indices for q₀ and q₁
            let q0_vertex = if t_q0 < 0.5 {
                combo.q_edges[0]
            } else {
                (combo.q_edges[0] + 1) % n_q
            };
            let q1_vertex = if t_q1 < 0.5 {
                combo.q_edges[1]
            } else {
                (combo.q_edges[1] + 1) % n_q
            };

            // Validate the full 4-segment orbit
            let orbit_valid =
                validate_2bounce_orbit(&q0, &q1, k_q, k_p, q0_vertex, q1_vertex);

            if orbit_valid.is_none() {
                continue;
            }

            let (_p_fwd, _p_back) = orbit_valid.unwrap();
            let action = compute_2bounce_action(&q0, &q1, k_p);

            if action > MIN_ACTION {
                if best.is_none() || action < best.as_ref().unwrap().action {
                    // For p_params, we store t=0 if at vertex, t=0.5 if on edge
                    // (This is an approximation; we could compute exact params if needed)
                    best = Some(SolveResult {
                        action,
                        q_params: vec![t_q0, t_q1],
                        p_params: vec![0.0, 0.0], // Placeholder, p positions are determined by q-motion
                    });
                }
            }
        }
    }

    best
}

/// Validate that a full 3-bounce orbit (6 segments) is achievable.
///
/// The 6 segments are:
/// 1. q at q₀: p moves from p₂ to p₀
/// 2. p at p₀: q moves from q₀ to q₁
/// 3. q at q₁: p moves from p₀ to p₁
/// 4. p at p₁: q moves from q₁ to q₂
/// 5. q at q₂: p moves from p₁ to p₂
/// 6. p at p₂: q moves from q₂ to q₀
///
/// Returns true if valid, false otherwise.
fn validate_3bounce_orbit(
    q0: &Vector2<f64>,
    q1: &Vector2<f64>,
    q2: &Vector2<f64>,
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    q0_vertex: usize,
    q1_vertex: usize,
    q2_vertex: usize,
) -> bool {
    let d01 = *q1 - *q0;
    let d12 = *q2 - *q1;
    let d20 = *q0 - *q2;

    // Find where p must be during each q-motion phase
    let p0_info = match find_p_position_for_q_motion(&d01, k_p, EPS) {
        Some(info) => info,
        None => return false,
    };
    let p1_info = match find_p_position_for_q_motion(&d12, k_p, EPS) {
        Some(info) => info,
        None => return false,
    };
    let p2_info = match find_p_position_for_q_motion(&d20, k_p, EPS) {
        Some(info) => info,
        None => return false,
    };

    // Get the actual p positions
    let p0 = get_p_position(k_p, p0_info);
    let p1 = get_p_position(k_p, p1_info);
    let p2 = get_p_position(k_p, p2_info);

    // At q₀: p must transition from p₂ to p₀
    let delta_p_at_q0 = p0 - p2;
    if !is_p_motion_achievable_at_vertex(&delta_p_at_q0, k_q, q0_vertex, EPS) {
        return false;
    }

    // At q₁: p must transition from p₀ to p₁
    let delta_p_at_q1 = p1 - p0;
    if !is_p_motion_achievable_at_vertex(&delta_p_at_q1, k_q, q1_vertex, EPS) {
        return false;
    }

    // At q₂: p must transition from p₁ to p₂
    let delta_p_at_q2 = p2 - p1;
    if !is_p_motion_achievable_at_vertex(&delta_p_at_q2, k_q, q2_vertex, EPS) {
        return false;
    }

    true
}

/// Solve for the minimum action 3-bounce trajectory with the given edge combination.
///
/// For 3-bounce, the trajectory has 6 segments:
/// 1. q at q₀: p moves
/// 2. p fixed: q moves q₀ → q₁
/// 3. q at q₁: p moves
/// 4. p fixed: q moves q₁ → q₂
/// 5. q at q₂: p moves
/// 6. p fixed: q moves q₂ → q₀
///
/// Constraints:
/// 1. All q-displacements must be achievable by the Reeb flow
/// 2. All p-transitions at the bounces must be achievable by the Reeb flow
///
/// By vertex optimality, we enumerate all 8 vertices of [0,1]³ for q-parameters.
pub fn solve_3bounce(
    k_q: &Polygon2D,
    k_p: &Polygon2D,
    combo: &EdgeCombination,
) -> Option<SolveResult> {
    assert_eq!(combo.q_edges.len(), 3);
    assert_eq!(combo.p_edges.len(), 3);

    // Find vertices of the q-closure polytope
    let q_vertices = enumerate_closure_vertices(k_q, &combo.q_edges)?;

    let n_q = k_q.num_vertices();
    let mut best: Option<SolveResult> = None;

    // Enumerate q vertices (p positions are determined by q-motion constraints)
    for t_q in &q_vertices {
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

        // Get vertex indices for q₀, q₁, q₂
        let q0_vertex = if t_q[0] < 0.5 {
            combo.q_edges[0]
        } else {
            (combo.q_edges[0] + 1) % n_q
        };
        let q1_vertex = if t_q[1] < 0.5 {
            combo.q_edges[1]
        } else {
            (combo.q_edges[1] + 1) % n_q
        };
        let q2_vertex = if t_q[2] < 0.5 {
            combo.q_edges[2]
        } else {
            (combo.q_edges[2] + 1) % n_q
        };

        // Validate the full 6-segment orbit
        if !validate_3bounce_orbit(&q0, &q1, &q2, k_q, k_p, q0_vertex, q1_vertex, q2_vertex) {
            continue;
        }

        let action = compute_3bounce_action(&q0, &q1, &q2, k_p);

        if action > MIN_ACTION {
            if best.is_none() || action < best.as_ref().unwrap().action {
                best = Some(SolveResult {
                    action,
                    q_params: t_q.to_vec(),
                    p_params: vec![0.0, 0.0, 0.0], // Placeholder, p positions determined by q-motion
                });
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
fn enumerate_closure_vertices(_polygon: &Polygon2D, edges: &[usize]) -> Option<Vec<[f64; 3]>> {
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
