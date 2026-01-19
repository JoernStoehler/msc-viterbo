//! Minkowski billiard infrastructure for Lagrangian products.
//!
//! For a Lagrangian product K = K₁ × K₂ where K₁ ⊂ ℝ²_q and K₂ ⊂ ℝ²_p,
//! the EHZ capacity equals the minimal length of a closed K₂°-billiard
//! trajectory in K₁.
//!
//! This module provides:
//! - Data types for billiard trajectories (`BilliardTrajectory`, `ThreeBounceTrajectory`)
//! - Polygon representation (`Polygon2DSimple`)
//! - Lagrangian factor extraction (`extract_lagrangian_factors`)
//! - Witness orbit construction (`construct_2bounce_witness`, `construct_3bounce_witness`)
//!
//! The actual capacity computation is in `billiard_lp.rs`, which uses LP to find
//! the optimal trajectory. By Rudolf 2022 Theorem 4, the optimal has at most 3 bounces.
//!
//! References:
//! - Rudolf (2022): "The Minkowski Billiard Characterization of the EHZ-Capacity
//!   of Convex Lagrangian Products"
//! - Artstein-Avidan & Ostrover (2014): Original connection for smooth convex bodies

use crate::result::WitnessOrbit;
use rust_viterbo_geom::{PolytopeHRep, SymplecticVector, Vector2f};

/// Tolerance for Lagrangian product detection.
const EPS_LAGR_PROD: f64 = 1e-10;

/// Result of extracting Lagrangian factors with facet index tracking.
#[derive(Clone, Debug)]
pub struct LagrangianFactors {
    /// The q-space polygon K₁
    pub k1: Polygon2DSimple,
    /// The p-space polygon K₂
    pub k2: Polygon2DSimple,
    /// Original 4D facet indices for K₁'s facets (sorted by angle)
    pub q_facet_indices: Vec<usize>,
    /// Original 4D facet indices for K₂'s facets (sorted by angle)
    pub p_facet_indices: Vec<usize>,
}

/// A billiard trajectory in the Lagrangian product.
#[derive(Clone, Debug)]
pub struct BilliardTrajectory {
    /// Total action (= capacity)
    pub action: f64,
    /// The two 2D bounce points in K₁
    pub q_points: [Vector2f; 2],
    /// Index of q-facets hit (in K₁'s sorted order)
    pub q_facet_local: [usize; 2],
    /// Index of K₂ vertices for p-coordinates [forward_direction, backward_direction]
    pub p_vertex_local: [usize; 2],
    /// Index of p-facets traversed (in K₂'s sorted order)
    pub p_facet_local: [usize; 2],
}

/// A 2D convex polygon with vertices and edges.
#[derive(Clone, Debug)]
pub struct Polygon2DSimple {
    /// Vertices in counterclockwise order
    pub vertices: Vec<Vector2f>,
    /// Edge normals (outward)
    pub normals: Vec<Vector2f>,
    /// Edge heights (from origin)
    pub heights: Vec<f64>,
}

impl Polygon2DSimple {
    /// Create a polygon from H-representation (normals and heights).
    pub fn from_hrep(normals: Vec<Vector2f>, heights: Vec<f64>) -> Self {
        let n = normals.len();
        let mut vertices = Vec::with_capacity(n);

        // Compute vertices as intersections of consecutive edges
        for i in 0..n {
            let j = (i + 1) % n;
            if let Some(v) = line_intersection(&normals[i], heights[i], &normals[j], heights[j]) {
                vertices.push(v);
            }
        }

        Self {
            vertices,
            normals,
            heights,
        }
    }

    /// Support function: h_K(v) = max_{x ∈ K} ⟨x, v⟩
    pub fn support(&self, direction: Vector2f) -> f64 {
        self.vertices
            .iter()
            .map(|v| v.dot(&direction))
            .fold(f64::NEG_INFINITY, f64::max)
    }

    /// Find the vertex that achieves the support function value.
    /// Returns the vertex y* = argmax_{y ∈ K} ⟨y, direction⟩
    pub fn supporting_vertex(&self, direction: Vector2f) -> Vector2f {
        let mut best_idx = 0;
        let mut best_val = f64::NEG_INFINITY;
        for (i, v) in self.vertices.iter().enumerate() {
            let val = v.dot(&direction);
            if val > best_val {
                best_val = val;
                best_idx = i;
            }
        }
        self.vertices[best_idx]
    }

    /// Compute the polar body K° = {y : h_K(y) ≤ 1}
    /// For a polygon with vertices v_i, the polar has normals v_i/||v_i||² and heights 1/||v_i||
    /// But more practically: polar of polygon with normals n_i, heights h_i has vertices n_i/h_i
    pub fn polar(&self) -> Polygon2DSimple {
        // The polar of a polygon given by {x : ⟨n_i, x⟩ ≤ h_i} has vertices at n_i/h_i
        let polar_vertices: Vec<Vector2f> = self
            .normals
            .iter()
            .zip(&self.heights)
            .map(|(n, h)| *n / *h)
            .collect();

        // Compute polar normals and heights from vertices
        // For vertices v_i, v_{i+1}, the edge normal is perpendicular to v_{i+1} - v_i
        let n = polar_vertices.len();
        let mut polar_normals = Vec::with_capacity(n);
        let mut polar_heights = Vec::with_capacity(n);

        for i in 0..n {
            let v1 = polar_vertices[i];
            let v2 = polar_vertices[(i + 1) % n];
            let edge = v2 - v1;
            // Outward normal (perpendicular, pointing away from origin)
            let normal = Vector2f::new(edge.y, -edge.x);
            let normal = if normal.dot(&v1) > 0.0 {
                normal / normal.norm()
            } else {
                -normal / normal.norm()
            };
            let height = normal.dot(&v1);
            polar_normals.push(normal);
            polar_heights.push(height);
        }

        Polygon2DSimple {
            vertices: polar_vertices,
            normals: polar_normals,
            heights: polar_heights,
        }
    }

    /// Compute the width of the polygon in a given direction using the K°-metric.
    /// Width(K, n) = h_K(n) + h_K(-n)
    pub fn width_euclidean(&self, direction: Vector2f) -> f64 {
        self.support(direction) + self.support(-direction)
    }
}

/// Find intersection of two lines given by ⟨n_i, x⟩ = h_i
fn line_intersection(
    n1: &Vector2f,
    h1: f64,
    n2: &Vector2f,
    h2: f64,
) -> Option<Vector2f> {
    let det = n1.x * n2.y - n1.y * n2.x;
    if det.abs() < 1e-12 {
        return None; // Parallel lines
    }
    let x = (h1 * n2.y - h2 * n1.y) / det;
    let y = (n1.x * h2 - n2.x * h1) / det;
    Some(Vector2f::new(x, y))
}

/// Extract the q-space and p-space factors from a Lagrangian product.
///
/// Returns `LagrangianFactors` containing K₁, K₂, and the mapping from
/// sorted facet indices back to original 4D facet indices.
pub fn extract_lagrangian_factors(hrep: &PolytopeHRep) -> Option<LagrangianFactors> {
    let mut q_data: Vec<(Vector2f, f64, usize)> = Vec::new();
    let mut p_data: Vec<(Vector2f, f64, usize)> = Vec::new();

    for (i, (normal, &height)) in hrep.normals.iter().zip(&hrep.heights).enumerate() {
        let q_part = (normal[0].abs() > EPS_LAGR_PROD) || (normal[1].abs() > EPS_LAGR_PROD);
        let p_part = (normal[2].abs() > EPS_LAGR_PROD) || (normal[3].abs() > EPS_LAGR_PROD);

        if q_part && !p_part {
            // Pure q-space facet
            q_data.push((Vector2f::new(normal[0], normal[1]), height, i));
        } else if p_part && !q_part {
            // Pure p-space facet
            p_data.push((Vector2f::new(normal[2], normal[3]), height, i));
        } else {
            // Mixed facet - not a Lagrangian product
            return None;
        }
    }

    if q_data.len() < 3 || p_data.len() < 3 {
        return None;
    }

    // Sort by angle and extract components
    let (k1, q_facet_indices) = sort_polygon_ccw_with_indices(q_data);
    let (k2, p_facet_indices) = sort_polygon_ccw_with_indices(p_data);

    Some(LagrangianFactors {
        k1,
        k2,
        q_facet_indices,
        p_facet_indices,
    })
}

/// Sort polygon data to counterclockwise order by normal angle, preserving original indices.
fn sort_polygon_ccw_with_indices(
    data: Vec<(Vector2f, f64, usize)>,
) -> (Polygon2DSimple, Vec<usize>) {
    let mut sorted = data;
    sorted.sort_by(|(n1, _, _), (n2, _, _)| {
        let angle1 = n1.y.atan2(n1.x);
        let angle2 = n2.y.atan2(n2.x);
        angle1.partial_cmp(&angle2).unwrap()
    });

    let normals: Vec<Vector2f> = sorted.iter().map(|(n, _, _)| *n).collect();
    let heights: Vec<f64> = sorted.iter().map(|(_, h, _)| *h).collect();
    let indices: Vec<usize> = sorted.iter().map(|(_, _, i)| *i).collect();

    (Polygon2DSimple::from_hrep(normals, heights), indices)
}

/// Find which facet of a polygon a vertex lies on.
/// Returns the index of the facet (edge) whose constraint is active at this vertex.
fn find_facet_for_vertex(_polygon: &Polygon2DSimple, vertex_idx: usize) -> usize {
    // Vertex i is at the intersection of edges i-1 and i (in CCW order).
    // The edge i goes from vertex i to vertex i+1, with normal polygon.normals[i].
    // So vertex i lies on edge (i-1) mod n and edge i.
    // We return edge i as the "incoming" edge.
    vertex_idx
}

/// Find which facet (edge) of a polygon a point lies on.
/// Returns the index of the facet whose constraint is most tightly satisfied (closest to equality).
fn find_facet_containing_point(polygon: &Polygon2DSimple, point: Vector2f) -> usize {
    let mut best_idx = 0;
    let mut best_slack = f64::INFINITY;

    for (i, (normal, &height)) in polygon.normals.iter().zip(&polygon.heights).enumerate() {
        // Constraint: n · x <= h
        // Slack: h - n · x (should be >= 0 and small if on boundary)
        let slack = (height - normal.dot(&point)).abs();
        if slack < best_slack {
            best_slack = slack;
            best_idx = i;
        }
    }

    best_idx
}

/// Find which vertex of K₂ achieves the support h_{K₂}(direction).
/// Returns the vertex index.
fn find_supporting_vertex(k2: &Polygon2DSimple, direction: Vector2f) -> usize {
    let mut best_idx = 0;
    let mut best_val = f64::NEG_INFINITY;
    for (i, v) in k2.vertices.iter().enumerate() {
        let val = v.dot(&direction);
        if val > best_val {
            best_val = val;
            best_idx = i;
        }
    }
    best_idx
}

/// Find which facet of K₂ is active when moving in the given direction.
/// For the support direction d, this is the facet whose normal is most aligned with d.
fn find_supporting_facet(k2: &Polygon2DSimple, direction: Vector2f) -> usize {
    let mut best_idx = 0;
    let mut best_val = f64::NEG_INFINITY;
    for (i, normal) in k2.normals.iter().enumerate() {
        let val = normal.dot(&direction);
        if val > best_val {
            best_val = val;
            best_idx = i;
        }
    }
    best_idx
}

/// Compute the minimal billiard trajectory with full trajectory information.
///
/// For a K₂°-billiard in K₁, finds the 2-bounce trajectory with minimal K₂-length
/// and returns the trajectory details needed to construct a witness orbit.
pub fn find_minimal_billiard(k1: &Polygon2DSimple, k2: &Polygon2DSimple) -> Option<BilliardTrajectory> {
    let n1 = k1.vertices.len();
    if n1 < 3 {
        return None;
    }

    let mut best: Option<BilliardTrajectory> = None;
    let mut min_length = f64::INFINITY;

    // Check all NON-ADJACENT pairs of vertices as potential bounce points.
    // Adjacent vertices share an edge, so the "trajectory" would go along the
    // boundary, not through the interior. Only non-adjacent pairs form valid
    // 2-bounce billiard trajectories.
    for i in 0..n1 {
        for j in (i + 1)..n1 {
            // Skip adjacent vertices (share an edge)
            let adjacent = (j == i + 1) || (i == 0 && j == n1 - 1);
            if adjacent {
                continue;
            }

            let v_i = k1.vertices[i];
            let v_j = k1.vertices[j];
            let direction = v_j - v_i;

            // K₂-length of round-trip
            let length_forward = k2.support(direction);
            let length_backward = k2.support(-direction);
            let total_length = length_forward + length_backward;

            if total_length < min_length {
                min_length = total_length;
                // Find which K₂ vertices and facets are active for each direction
                let p_vert_fwd = find_supporting_vertex(k2, direction);
                let p_vert_bwd = find_supporting_vertex(k2, -direction);
                let p_facet_fwd = find_supporting_facet(k2, direction);
                let p_facet_bwd = find_supporting_facet(k2, -direction);
                best = Some(BilliardTrajectory {
                    action: total_length,
                    q_points: [v_i, v_j],
                    q_facet_local: [find_facet_for_vertex(k1, i), find_facet_for_vertex(k1, j)],
                    p_vertex_local: [p_vert_fwd, p_vert_bwd],
                    p_facet_local: [p_facet_fwd, p_facet_bwd],
                });
            }
        }
    }

    // Also check edge-perpendicular directions (width minimizers)
    for i in 0..n1 {
        let v1 = k1.vertices[i];
        let v2 = k1.vertices[(i + 1) % n1];
        let edge = v2 - v1;
        let perp = Vector2f::new(-edge.y, edge.x);

        // Find points on opposite parallel edges
        let max_proj = k1.support(perp);
        let min_proj = -k1.support(-perp);
        let width_vec = perp * ((max_proj - min_proj) / perp.norm_squared());

        let length = k2.support(width_vec) + k2.support(-width_vec);
        if length < min_length {
            min_length = length;
            // For edge-perpendicular case, the bounce points are on edges
            // We use the midpoint of edge i and project to find the opposite point
            let mid = (v1 + v2) * 0.5;
            let opposite = mid + width_vec;

            // Find which K₁ facets these points lie on by checking constraints
            let q_facet_mid = find_facet_containing_point(k1, mid);
            let q_facet_opp = find_facet_containing_point(k1, opposite);

            // Find which K₂ vertices and facets are active
            let p_vert_fwd = find_supporting_vertex(k2, width_vec);
            let p_vert_bwd = find_supporting_vertex(k2, -width_vec);
            let p_facet_fwd = find_supporting_facet(k2, width_vec);
            let p_facet_bwd = find_supporting_facet(k2, -width_vec);
            best = Some(BilliardTrajectory {
                action: length,
                q_points: [mid, opposite],
                q_facet_local: [q_facet_mid, q_facet_opp],
                p_vertex_local: [p_vert_fwd, p_vert_bwd],
                p_facet_local: [p_facet_fwd, p_facet_bwd],
            });
        }
    }

    best
}

/// Simple version that just returns the length (for backward compatibility in tests).
pub fn minimal_billiard_length(k1: &Polygon2DSimple, k2: &Polygon2DSimple) -> f64 {
    find_minimal_billiard(k1, k2)
        .map(|t| t.action)
        .unwrap_or(f64::INFINITY)
}

// ============================================================================
// 3-Bounce Trajectory Data Structure
// ============================================================================

/// Result of 3-bounce optimization.
#[derive(Clone, Debug)]
pub struct ThreeBounceTrajectory {
    /// Total action (= capacity)
    pub action: f64,
    /// The three 2D bounce points in K₁
    pub q_points: [Vector2f; 3],
    /// Edge parameters t ∈ [0,1] for each bounce point
    pub edge_params: [f64; 3],
    /// Index of K₁ edges (facets) hit
    pub q_facet_local: [usize; 3],
}

/// Construct witness orbit for a 2-bounce trajectory.
pub fn construct_2bounce_witness(
    factors: &LagrangianFactors,
    trajectory: &BilliardTrajectory,
) -> Option<WitnessOrbit> {
    // A 2-bounce billiard has 4 segments: q0→p1→q1→p0→(close)
    //
    // For the orbit (q_a, p_0) → (q_a, p_1) → (q_b, p_1) → (q_b, p_0) → close:
    // - Breakpoint 0: (q_a, p_0)
    // - Breakpoint 1: (q_a, p_1)
    // - Breakpoint 2: (q_b, p_1)
    // - Breakpoint 3: (q_b, p_0)

    let q_a = trajectory.q_points[0];
    let q_b = trajectory.q_points[1];

    // p_0, p_1 are the vertices of K₂ that achieve the support in each direction
    let direction = q_b - q_a;
    let p_1 = factors.k2.vertices[trajectory.p_vertex_local[0]]; // supports direction
    let p_0 = factors.k2.vertices[trajectory.p_vertex_local[1]]; // supports -direction

    // 4D breakpoints
    let breakpoints = vec![
        SymplecticVector::new(q_a.x, q_a.y, p_0.x, p_0.y),
        SymplecticVector::new(q_a.x, q_a.y, p_1.x, p_1.y),
        SymplecticVector::new(q_b.x, q_b.y, p_1.x, p_1.y),
        SymplecticVector::new(q_b.x, q_b.y, p_0.x, p_0.y),
    ];

    // Map local facet indices back to original 4D facet indices
    let q_facet_0 = factors.q_facet_indices[trajectory.q_facet_local[0]];
    let q_facet_1 = factors.q_facet_indices[trajectory.q_facet_local[1]];
    let p_facet_0 = factors.p_facet_indices[trajectory.p_facet_local[1]];
    let p_facet_1 = factors.p_facet_indices[trajectory.p_facet_local[0]];

    let facet_sequence = vec![q_facet_0, q_facet_0, p_facet_1, q_facet_1, p_facet_0];

    // Compute segment times
    let delta_p = (p_1 - p_0).norm();
    let delta_q = direction.norm();

    let n_q0 = factors.k1.normals[trajectory.q_facet_local[0]];
    let h_q0 = factors.k1.heights[trajectory.q_facet_local[0]];
    let t0 = delta_p * h_q0 / (2.0 * n_q0.norm());

    let n_p1 = factors.k2.normals[trajectory.p_facet_local[0]];
    let h_p1 = factors.k2.heights[trajectory.p_facet_local[0]];
    let t1 = delta_q * h_p1 / (2.0 * n_p1.norm());

    let n_q1 = factors.k1.normals[trajectory.q_facet_local[1]];
    let h_q1 = factors.k1.heights[trajectory.q_facet_local[1]];
    let t2 = delta_p * h_q1 / (2.0 * n_q1.norm());

    let n_p0 = factors.k2.normals[trajectory.p_facet_local[1]];
    let h_p0 = factors.k2.heights[trajectory.p_facet_local[1]];
    let t3 = delta_q * h_p0 / (2.0 * n_p0.norm());

    let segment_times = vec![t0, t1, t2, t3];

    Some(WitnessOrbit {
        breakpoints,
        facet_sequence,
        segment_times,
    })
}

/// Construct witness orbit for a 3-bounce trajectory.
pub fn construct_3bounce_witness(
    factors: &LagrangianFactors,
    trajectory: &ThreeBounceTrajectory,
) -> Option<WitnessOrbit> {
    // A 3-bounce billiard has 6 segments alternating between q-facets and p-facets:
    // q₁ → q₂: p changes on p_12 facet
    // q₂ → q₃: p changes on p_23 facet
    // q₃ → q₁: p changes on p_31 facet
    //
    // The full 4D orbit is:
    // (q₁, p₃₁) → (q₁, p₁₂) → (q₂, p₁₂) → (q₂, p₂₃) → (q₃, p₂₃) → (q₃, p₃₁) → close

    let [q1, q2, q3] = trajectory.q_points;

    // Compute displacement directions and find supporting K₂ vertices
    let d12 = q2 - q1;
    let d23 = q3 - q2;
    let d31 = q1 - q3;

    // p-vertices for each direction
    let p_12 = factors.k2.supporting_vertex(d12);
    let p_23 = factors.k2.supporting_vertex(d23);
    let p_31 = factors.k2.supporting_vertex(d31);

    // 4D breakpoints (6 points for 3-bounce)
    let breakpoints = vec![
        SymplecticVector::new(q1.x, q1.y, p_31.x, p_31.y),
        SymplecticVector::new(q1.x, q1.y, p_12.x, p_12.y),
        SymplecticVector::new(q2.x, q2.y, p_12.x, p_12.y),
        SymplecticVector::new(q2.x, q2.y, p_23.x, p_23.y),
        SymplecticVector::new(q3.x, q3.y, p_23.x, p_23.y),
        SymplecticVector::new(q3.x, q3.y, p_31.x, p_31.y),
    ];

    // Map local facet indices to 4D indices
    let q_facet_1 = factors.q_facet_indices[trajectory.q_facet_local[0]];
    let q_facet_2 = factors.q_facet_indices[trajectory.q_facet_local[1]];
    let q_facet_3 = factors.q_facet_indices[trajectory.q_facet_local[2]];

    // Find p-facets for each direction
    let p_facet_12 = factors.p_facet_indices[find_supporting_facet_idx(&factors.k2, d12)];
    let p_facet_23 = factors.p_facet_indices[find_supporting_facet_idx(&factors.k2, d23)];
    let p_facet_31 = factors.p_facet_indices[find_supporting_facet_idx(&factors.k2, d31)];

    // Facet sequence: alternates q-facet, p-facet, q-facet, p-facet, q-facet, p-facet
    let facet_sequence = vec![
        q_facet_1, // starting facet
        q_facet_1, // segment 0: p changes on q_facet_1
        p_facet_12, // segment 1: q changes from q₁ to q₂
        q_facet_2, // segment 2: p changes on q_facet_2
        p_facet_23, // segment 3: q changes from q₂ to q₃
        q_facet_3, // segment 4: p changes on q_facet_3
        p_facet_31, // segment 5: q changes from q₃ to q₁
    ];

    // Compute segment times (simplified - use normalized times)
    // For proper physics, each segment time would be computed from the flow equations
    let delta_p_01 = (p_12 - p_31).norm();
    let delta_q_12 = d12.norm();
    let delta_p_23_p = (p_23 - p_12).norm();
    let delta_q_23 = d23.norm();
    let delta_p_45 = (p_31 - p_23).norm();
    let delta_q_31 = d31.norm();

    // Simplified time computation (proportional to distance)
    // In a full implementation, this would use the facet normals and heights
    let segment_times = vec![
        delta_p_01,
        delta_q_12,
        delta_p_23_p,
        delta_q_23,
        delta_p_45,
        delta_q_31,
    ];

    Some(WitnessOrbit {
        breakpoints,
        facet_sequence,
        segment_times,
    })
}

/// Find the local facet index whose normal is most aligned with the given direction.
fn find_supporting_facet_idx(k2: &Polygon2DSimple, direction: Vector2f) -> usize {
    let mut best_idx = 0;
    let mut best_val = f64::NEG_INFINITY;
    for (i, normal) in k2.normals.iter().enumerate() {
        let val = normal.dot(&direction);
        if val > best_val {
            best_val = val;
            best_idx = i;
        }
    }
    best_idx
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_viterbo_geom::SymplecticVector;

    fn unit_square() -> Polygon2DSimple {
        // Square [-1, 1]²
        let normals = vec![
            Vector2f::new(1.0, 0.0),
            Vector2f::new(0.0, 1.0),
            Vector2f::new(-1.0, 0.0),
            Vector2f::new(0.0, -1.0),
        ];
        let heights = vec![1.0, 1.0, 1.0, 1.0];
        Polygon2DSimple::from_hrep(normals, heights)
    }

    #[test]
    fn unit_square_vertices() {
        let sq = unit_square();
        assert_eq!(sq.vertices.len(), 4);
        // Check vertices are corners of [-1,1]²
        let expected = vec![
            Vector2f::new(1.0, 1.0),
            Vector2f::new(-1.0, 1.0),
            Vector2f::new(-1.0, -1.0),
            Vector2f::new(1.0, -1.0),
        ];
        for v in &sq.vertices {
            let found = expected.iter().any(|e| (v - e).norm() < 1e-10);
            assert!(found, "Unexpected vertex {:?}", v);
        }
    }

    #[test]
    fn unit_square_support() {
        let sq = unit_square();
        assert!((sq.support(Vector2f::new(1.0, 0.0)) - 1.0).abs() < 1e-10);
        assert!((sq.support(Vector2f::new(0.0, 1.0)) - 1.0).abs() < 1e-10);
        assert!((sq.support(Vector2f::new(1.0, 1.0)) - 2.0).abs() < 1e-10);
    }

    #[test]
    fn unit_square_polar() {
        let sq = unit_square();
        let polar = sq.polar();
        // Polar of [-1,1]² is the diamond with vertices at (±1, 0), (0, ±1)
        assert_eq!(polar.vertices.len(), 4);
        for v in &polar.vertices {
            // Each vertex should have L² norm 1
            assert!((v.norm() - 1.0).abs() < 1e-10, "Polar vertex {:?} not on unit circle", v);
        }
    }

    #[test]
    fn tesseract_capacity() {
        // Tesseract = [-1,1]⁴ = [-1,1]² × [-1,1]²
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
        let hrep = PolytopeHRep::new(normals, vec![1.0; 8]);

        // Use the LP algorithm for rigorous computation
        let result = crate::billiard_lp::compute_billiard_capacity_lp(hrep)
            .expect("should compute capacity");

        // For tesseract, capacity should be 4
        assert!(
            (result.capacity - 4.0).abs() < 1e-6,
            "Tesseract capacity should be 4, got {}",
            result.capacity
        );
    }

    #[test]
    fn billiard_length_square_square() {
        let sq = unit_square();
        // For K₁ = K₂ = [-1,1]², the K₂-length of segment (−1,0)→(1,0) is:
        // h_{K₂}(2, 0) = max_{y ∈ [-1,1]²} ⟨(2,0), y⟩ = 2 * 1 = 2
        // The 2-bounce billiard has total length 2 * 2 = 4
        let length = minimal_billiard_length(&sq, &sq);
        assert!(
            (length - 4.0).abs() < 1e-6,
            "Billiard length should be 4, got {}",
            length
        );
    }
}
