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
//! the optimal trajectory.
//!
//! # Citations
//!
//! - **Rudolf 2022 Theorem 3**: For K polytope and T strictly convex, action-minimizing
//!   closed characteristics on ∂(K×T) correspond to closed (K,T)-Minkowski billiard
//!   trajectories in K with dual trajectories in T.
//!   Source: "The Minkowski Billiard Characterization of the EHZ-Capacity of Convex
//!   Lagrangian Products", J. Dyn. Diff. Equat., arXiv:2203.01718
//!
//! - **Rudolf 2022 Theorem 4**: The T-minimizing closed (K,T)-Minkowski billiard
//!   trajectory has **at most n+1 bouncing points** (where n = dim K). For n=2
//!   (planar polygons), this means at most 3 bounces.
//!
//! - **Artstein-Avidan & Ostrover 2014**: Original connection for smooth convex bodies.
//!   Source: "Bounds for Minkowski Billiard Trajectories in Convex Bodies", IMRN 2014(1),
//!   arXiv:1111.2353

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
    ///
    /// # Panics (in debug mode)
    /// - If normals and heights have different lengths
    /// - If fewer than 3 edges
    /// - If any normal is zero
    /// - If any height is non-positive (origin must be inside)
    /// - If line intersections fail (parallel edges)
    pub fn from_hrep(normals: Vec<Vector2f>, heights: Vec<f64>) -> Self {
        let n = normals.len();

        // Validate inputs in debug mode
        debug_assert_eq!(
            normals.len(),
            heights.len(),
            "normals and heights must have same length"
        );
        debug_assert!(n >= 3, "polygon must have at least 3 edges, got {}", n);
        for (i, normal) in normals.iter().enumerate() {
            debug_assert!(normal.norm() > 1e-10, "normal {} is zero or near-zero", i);
        }
        for (i, &h) in heights.iter().enumerate() {
            debug_assert!(
                h > 0.0,
                "height {} must be positive (origin inside polygon), got {}",
                i,
                h
            );
        }

        let mut vertices = Vec::with_capacity(n);

        // Compute vertices as intersections of consecutive edges
        for i in 0..n {
            let j = (i + 1) % n;
            if let Some(v) = line_intersection(&normals[i], heights[i], &normals[j], heights[j]) {
                debug_assert!(
                    v.x.is_finite() && v.y.is_finite(),
                    "vertex {} is not finite: {:?}",
                    i,
                    v
                );
                vertices.push(v);
            }
        }

        debug_assert_eq!(
            vertices.len(),
            n,
            "failed to compute all {} vertices, got {}",
            n,
            vertices.len()
        );

        Self {
            vertices,
            normals,
            heights,
        }
    }

    /// Support function: h_K(v) = max_{x ∈ K} ⟨x, v⟩
    ///
    /// **UNCITED standard definition**: Support function is a standard concept in convex
    /// analysis. For Minkowski billiards, see Rudolf 2022 §3.1.
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
    ///
    /// **UNCITED standard result**: For a polygon given by {x : ⟨n_i, x⟩ ≤ h_i} with origin
    /// in interior, the polar body has vertices at n_i/h_i. This is a standard result in
    /// convex geometry (polar duality) but should be cited from a textbook source.
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
fn line_intersection(n1: &Vector2f, h1: f64, n2: &Vector2f, h2: f64) -> Option<Vector2f> {
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

    // Sort normals by angle to get boundary order.
    // For a convex polygon with origin inside, outward normals in CCW boundary order
    // have monotonically increasing angles.
    // This is necessary because the 4D H-rep might have facets in arbitrary order.
    q_data.sort_by(|a, b| {
        let angle_a = a.0.y.atan2(a.0.x);
        let angle_b = b.0.y.atan2(b.0.x);
        angle_a.partial_cmp(&angle_b).unwrap()
    });
    p_data.sort_by(|a, b| {
        let angle_a = a.0.y.atan2(a.0.x);
        let angle_b = b.0.y.atan2(b.0.x);
        angle_a.partial_cmp(&angle_b).unwrap()
    });

    let (k1, q_facet_indices) = extract_polygon_with_indices(q_data);
    let (k2, p_facet_indices) = extract_polygon_with_indices(p_data);

    // Validate output invariants in debug mode
    debug_assert_eq!(
        k1.vertices.len(),
        k1.normals.len(),
        "K1 vertices/normals mismatch"
    );
    debug_assert_eq!(
        k2.vertices.len(),
        k2.normals.len(),
        "K2 vertices/normals mismatch"
    );
    debug_assert_eq!(
        q_facet_indices.len(),
        k1.normals.len(),
        "q_facet_indices length mismatch"
    );
    debug_assert_eq!(
        p_facet_indices.len(),
        k2.normals.len(),
        "p_facet_indices length mismatch"
    );

    // Validate facet indices are valid and unique
    for &idx in &q_facet_indices {
        debug_assert!(
            idx < hrep.normals.len(),
            "q_facet_index {} out of range",
            idx
        );
    }
    for &idx in &p_facet_indices {
        debug_assert!(
            idx < hrep.normals.len(),
            "p_facet_index {} out of range",
            idx
        );
    }

    Some(LagrangianFactors {
        k1,
        k2,
        q_facet_indices,
        p_facet_indices,
    })
}

/// Extract polygon data WITHOUT sorting, preserving original order and indices.
///
/// The input normals are assumed to already be in boundary order (consecutive normals
/// correspond to adjacent edges). This is the case when normals come from to_hrep_2d.
fn extract_polygon_with_indices(
    data: Vec<(Vector2f, f64, usize)>,
) -> (Polygon2DSimple, Vec<usize>) {
    let normals: Vec<Vector2f> = data.iter().map(|(n, _, _)| *n).collect();
    let heights: Vec<f64> = data.iter().map(|(_, h, _)| *h).collect();
    let indices: Vec<usize> = data.iter().map(|(_, _, i)| *i).collect();

    (Polygon2DSimple::from_hrep(normals, heights), indices)
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
///
/// # Invariants (documented for future verification)
///
/// ## Input requirements:
/// - `trajectory.q_points` lie on ∂K₁ (boundary of K₁)
/// - `trajectory.q_facet_local` indices are valid for `factors.k1`
/// - `trajectory.p_vertex_local` indices are valid for `factors.k2`
/// - `trajectory.p_facet_local` indices are valid for `factors.k2`
///
/// ## Output invariants (should be verified by WitnessOrbit::verify):
/// - Each breakpoint lies on the corresponding facet in facet_sequence
/// - segment_times: NOT IMPLEMENTED (placeholder zeros)
/// - The orbit closes: flowing from last breakpoint returns to first
///
/// ## Geometry:
/// A 2-bounce billiard trajectory oscillates between two points q_a, q_b ∈ ∂K₁.
/// In the Lagrangian product K₁ × K₂, this becomes a 4-segment orbit:
/// ```text
/// (q_a, p_0) → (q_a, p_1) → (q_b, p_1) → (q_b, p_0) → (close)
///     ↑ segment 0    ↑ segment 1    ↑ segment 2    ↑ segment 3
///     on q-facet     on p-facet     on q-facet     on p-facet
/// ```
/// where p_0 and p_1 are the K₂ vertices supporting the forward and backward directions.
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
    let _direction = q_b - q_a;
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

    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // ⚠️  PLACEHOLDER VALUES - NOT COMPUTED  ⚠️
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    //
    // segment_times need proper derivation from Reeb flow equations.
    // The previous formula here had no derivation and gave 335% error on random polygons.
    //
    // WARNING: Code that USES these values will produce WRONG results!
    // The WitnessOrbit::verify() function detects this and warns loudly.
    //
    // Only breakpoints and facet_sequence are reliable from this witness.
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    let segment_times = vec![0.0; 4]; // PLACEHOLDER - DO NOT USE FOR COMPUTATION

    Some(WitnessOrbit {
        breakpoints,
        facet_sequence,
        segment_times,
    })
}

/// Construct witness orbit for a 3-bounce trajectory.
///
/// # Invariants (documented for future verification)
///
/// ## Input requirements:
/// - `trajectory.q_points` lie on ∂K₁ (each on its respective facet)
/// - `trajectory.edge_params[i] ∈ [0, 1]` (valid edge parameter)
/// - `trajectory.q_facet_local` indices are valid for `factors.k1`
///
/// ## Output invariants (should be verified by WitnessOrbit::verify):
/// - Each breakpoint lies on the corresponding facet in facet_sequence
/// - segment_times: NOT IMPLEMENTED (placeholder zeros)
/// - The orbit closes: flowing from last breakpoint returns to first
///
/// ## Geometry:
/// A 3-bounce trajectory visits three points q₁, q₂, q₃ ∈ ∂K₁.
/// In the Lagrangian product, this becomes a 6-segment orbit:
/// ```text
/// (q₁, p₃₁) → (q₁, p₁₂) → (q₂, p₁₂) → (q₂, p₂₃) → (q₃, p₂₃) → (q₃, p₃₁) → close
/// ```
/// where p_ij is the K₂ vertex supporting direction q_j - q_i.
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
        q_facet_1,  // starting facet
        q_facet_1,  // segment 0: p changes on q_facet_1
        p_facet_12, // segment 1: q changes from q₁ to q₂
        q_facet_2,  // segment 2: p changes on q_facet_2
        p_facet_23, // segment 3: q changes from q₂ to q₃
        q_facet_3,  // segment 4: p changes on q_facet_3
        p_facet_31, // segment 5: q changes from q₃ to q₁
    ];

    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    // ⚠️  PLACEHOLDER VALUES - NOT COMPUTED  ⚠️
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    //
    // segment_times need proper derivation from Reeb flow equations.
    // The previous formula here had no derivation.
    //
    // WARNING: Code that USES these values will produce WRONG results!
    // The WitnessOrbit::verify() function detects this and warns loudly.
    //
    // Only breakpoints and facet_sequence are reliable from this witness.
    // !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    let segment_times = vec![0.0; 6]; // PLACEHOLDER - DO NOT USE FOR COMPUTATION

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

    // =========================================================================
    // Test Fixtures
    // =========================================================================

    /// Unit square [-1, 1]² centered at origin.
    fn unit_square() -> Polygon2DSimple {
        let normals = vec![
            Vector2f::new(1.0, 0.0),
            Vector2f::new(0.0, 1.0),
            Vector2f::new(-1.0, 0.0),
            Vector2f::new(0.0, -1.0),
        ];
        let heights = vec![1.0, 1.0, 1.0, 1.0];
        Polygon2DSimple::from_hrep(normals, heights)
    }

    /// Equilateral triangle with circumradius 1.
    fn equilateral_triangle() -> Polygon2DSimple {
        use std::f64::consts::PI;
        let angles = [
            PI / 2.0,
            PI / 2.0 + 2.0 * PI / 3.0,
            PI / 2.0 + 4.0 * PI / 3.0,
        ];
        let vertices: Vec<Vector2f> = angles
            .iter()
            .map(|&a| Vector2f::new(a.cos(), a.sin()))
            .collect();

        let n = vertices.len();
        let mut normals = Vec::with_capacity(n);
        let mut heights = Vec::with_capacity(n);

        for i in 0..n {
            let v1 = vertices[i];
            let v2 = vertices[(i + 1) % n];
            let edge = v2 - v1;
            let normal = Vector2f::new(edge.y, -edge.x);
            let normal = if normal.dot(&v1) > 0.0 {
                normal / normal.norm()
            } else {
                -normal / normal.norm()
            };
            let height = normal.dot(&v1);
            normals.push(normal);
            heights.push(height);
        }

        Polygon2DSimple {
            vertices,
            normals,
            heights,
        }
    }

    // =========================================================================
    // Polygon2DSimple::from_hrep Tests
    // =========================================================================

    #[test]
    fn from_hrep_square_has_four_vertices() {
        let sq = unit_square();
        assert_eq!(sq.vertices.len(), 4, "Square should have 4 vertices");
    }

    #[test]
    fn from_hrep_square_vertices_are_corners() {
        let sq = unit_square();
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
    fn from_hrep_triangle_has_three_vertices() {
        let tri = equilateral_triangle();
        assert_eq!(tri.vertices.len(), 3, "Triangle should have 3 vertices");
    }

    #[test]
    fn from_hrep_vertices_satisfy_constraints() {
        // Invariant: Each vertex lies on exactly 2 adjacent facets
        let sq = unit_square();
        let tol = 1e-10;

        for (v_idx, v) in sq.vertices.iter().enumerate() {
            let n = sq.normals.len();
            // Vertex i = intersection of edge i and edge (i+1) mod n
            let e1 = v_idx;
            let e2 = (v_idx + 1) % n;

            // Check equality on adjacent edges
            let err1 = (sq.normals[e1].dot(v) - sq.heights[e1]).abs();
            let err2 = (sq.normals[e2].dot(v) - sq.heights[e2]).abs();
            assert!(
                err1 < tol,
                "Vertex {} not on edge {}: err={:.2e}",
                v_idx,
                e1,
                err1
            );
            assert!(
                err2 < tol,
                "Vertex {} not on edge {}: err={:.2e}",
                v_idx,
                e2,
                err2
            );

            // Check strict inequality on other edges
            for e in 0..n {
                if e != e1 && e != e2 {
                    let val = sq.normals[e].dot(v);
                    assert!(
                        val < sq.heights[e] + tol,
                        "Vertex {} violates edge {} inequality: {:.6} >= {:.6}",
                        v_idx,
                        e,
                        val,
                        sq.heights[e]
                    );
                }
            }
        }
    }

    // =========================================================================
    // Support Function Tests
    // =========================================================================

    #[test]
    fn support_axis_aligned_directions() {
        let sq = unit_square();
        // h_K(e_1) = max{x : x ∈ [-1,1]²} = 1
        assert!((sq.support(Vector2f::new(1.0, 0.0)) - 1.0).abs() < 1e-10);
        assert!((sq.support(Vector2f::new(0.0, 1.0)) - 1.0).abs() < 1e-10);
        assert!((sq.support(Vector2f::new(-1.0, 0.0)) - 1.0).abs() < 1e-10);
        assert!((sq.support(Vector2f::new(0.0, -1.0)) - 1.0).abs() < 1e-10);
    }

    #[test]
    fn support_diagonal_direction() {
        let sq = unit_square();
        // h_K((1,1)) = max{x+y : x,y ∈ [-1,1]} = 2 (attained at (1,1))
        assert!((sq.support(Vector2f::new(1.0, 1.0)) - 2.0).abs() < 1e-10);
    }

    #[test]
    fn support_equals_height_for_normal() {
        // Invariant: h_K(n_i) = h_i for each facet normal
        let sq = unit_square();
        for (i, (n, &h)) in sq.normals.iter().zip(&sq.heights).enumerate() {
            let support_val = sq.support(*n);
            assert!(
                (support_val - h).abs() < 1e-10,
                "support(n_{}) = {:.6} ≠ h_{} = {:.6}",
                i,
                support_val,
                i,
                h
            );
        }
    }

    // =========================================================================
    // Supporting Vertex Tests
    // =========================================================================

    #[test]
    fn supporting_vertex_achieves_support() {
        // Invariant: ⟨v*, d⟩ = h_K(d) where v* = supporting_vertex(d)
        let sq = unit_square();
        let directions = [
            Vector2f::new(1.0, 0.0),
            Vector2f::new(0.0, 1.0),
            Vector2f::new(1.0, 1.0),
            Vector2f::new(-1.0, 0.5),
        ];
        for d in directions {
            let v_star = sq.supporting_vertex(d);
            let support_val = sq.support(d);
            let achieved = d.dot(&v_star);
            assert!(
                (achieved - support_val).abs() < 1e-10,
                "supporting_vertex({:?}) = {:?} gives ⟨v*,d⟩ = {:.6} ≠ h_K(d) = {:.6}",
                d,
                v_star,
                achieved,
                support_val
            );
        }
    }

    // =========================================================================
    // Polar Body Tests
    // =========================================================================

    #[test]
    fn polar_square_is_diamond() {
        let sq = unit_square();
        let polar = sq.polar();
        // Polar of [-1,1]² is the diamond {(x,y) : |x| + |y| ≤ 1}
        // with vertices at (±1, 0), (0, ±1)
        assert_eq!(polar.vertices.len(), 4);
        for v in &polar.vertices {
            assert!(
                (v.norm() - 1.0).abs() < 1e-10,
                "Polar vertex {:?} not on unit circle",
                v
            );
        }
    }

    #[test]
    fn polar_vertices_are_normalized_normals() {
        // Invariant: polar vertices are n_i/h_i
        let sq = unit_square();
        let polar = sq.polar();
        for (i, v) in polar.vertices.iter().enumerate() {
            let expected = sq.normals[i] / sq.heights[i];
            assert!(
                (v - &expected).norm() < 1e-10,
                "Polar vertex {} = {:?} ≠ n_{}/h_{} = {:?}",
                i,
                v,
                i,
                i,
                expected
            );
        }
    }

    #[test]
    fn polar_of_polar_recovers_original() {
        // Invariant: (K°)° = K for convex body containing origin
        let sq = unit_square();
        let polar = sq.polar();
        let double_polar = polar.polar();

        // Check same number of vertices
        assert_eq!(double_polar.vertices.len(), sq.vertices.len());

        // Check vertices match (possibly permuted)
        for v in &sq.vertices {
            let found = double_polar.vertices.iter().any(|w| (v - w).norm() < 1e-6);
            assert!(found, "Original vertex {:?} not in double polar", v);
        }
    }

    // =========================================================================
    // Width Tests
    // =========================================================================

    #[test]
    fn width_euclidean_axis_directions() {
        let sq = unit_square();
        // Width of [-1,1]² in x-direction = 2
        let width_x = sq.width_euclidean(Vector2f::new(1.0, 0.0));
        let width_y = sq.width_euclidean(Vector2f::new(0.0, 1.0));
        assert!((width_x - 2.0).abs() < 1e-10, "Width in x = {}", width_x);
        assert!((width_y - 2.0).abs() < 1e-10, "Width in y = {}", width_y);
    }

    #[test]
    fn width_euclidean_diagonal() {
        let sq = unit_square();
        // Width in (1,1) direction = h_K((1,1)) + h_K((-1,-1)) = 2 + 2 = 4
        let width_diag = sq.width_euclidean(Vector2f::new(1.0, 1.0));
        assert!(
            (width_diag - 4.0).abs() < 1e-10,
            "Diagonal width = {}",
            width_diag
        );
    }

    // =========================================================================
    // extract_lagrangian_factors Tests
    // =========================================================================

    #[test]
    fn extract_lagrangian_factors_tesseract() {
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
        let factors = extract_lagrangian_factors(&hrep);
        assert!(factors.is_some(), "Tesseract should be Lagrangian product");

        let f = factors.unwrap();
        assert_eq!(f.k1.vertices.len(), 4, "K1 should have 4 vertices");
        assert_eq!(f.k2.vertices.len(), 4, "K2 should have 4 vertices");
        assert_eq!(f.q_facet_indices.len(), 4, "Should have 4 q-facet indices");
        assert_eq!(f.p_facet_indices.len(), 4, "Should have 4 p-facet indices");
    }

    #[test]
    fn extract_lagrangian_factors_rejects_non_product() {
        // A mixed normal: (1, 0, 1, 0) touches both q and p
        let normals = vec![
            SymplecticVector::new(1.0, 0.0, 1.0, 0.0), // Mixed!
            SymplecticVector::new(-1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
            SymplecticVector::new(0.0, -1.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 0.0, -1.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
            SymplecticVector::new(0.0, 0.0, 0.0, -1.0),
        ];
        let hrep = PolytopeHRep::new(normals, vec![1.0; 7]);
        let factors = extract_lagrangian_factors(&hrep);
        assert!(
            factors.is_none(),
            "Mixed normal should prevent Lagrangian extraction"
        );
    }

    #[test]
    fn extract_lagrangian_factors_index_mapping_correct() {
        // Verify that q_facet_indices[i] points to the correct 4D facet
        let normals = vec![
            SymplecticVector::new(1.0, 0.0, 0.0, 0.0),  // q
            SymplecticVector::new(-1.0, 0.0, 0.0, 0.0), // q
            SymplecticVector::new(0.0, 1.0, 0.0, 0.0),  // q
            SymplecticVector::new(0.0, -1.0, 0.0, 0.0), // q
            SymplecticVector::new(0.0, 0.0, 1.0, 0.0),  // p
            SymplecticVector::new(0.0, 0.0, -1.0, 0.0), // p
            SymplecticVector::new(0.0, 0.0, 0.0, 1.0),  // p
            SymplecticVector::new(0.0, 0.0, 0.0, -1.0), // p
        ];
        let hrep = PolytopeHRep::new(normals.clone(), vec![1.0; 8]);
        let f = extract_lagrangian_factors(&hrep).unwrap();

        // Check q_facet_indices point to q-facets
        for (local_idx, &global_idx) in f.q_facet_indices.iter().enumerate() {
            let n4d = normals[global_idx];
            assert!(
                n4d.z.abs() < 1e-10 && n4d.w.abs() < 1e-10,
                "q_facet_indices[{}] = {} points to non-q facet",
                local_idx,
                global_idx
            );
            // Check 2D normal matches
            let n2d = f.k1.normals[local_idx];
            assert!(
                (n2d.x - n4d.x).abs() < 1e-10 && (n2d.y - n4d.y).abs() < 1e-10,
                "Normal mismatch at q_facet[{}]",
                local_idx
            );
        }

        // Check p_facet_indices point to p-facets
        for (local_idx, &global_idx) in f.p_facet_indices.iter().enumerate() {
            let n4d = normals[global_idx];
            assert!(
                n4d.x.abs() < 1e-10 && n4d.y.abs() < 1e-10,
                "p_facet_indices[{}] = {} points to non-p facet",
                local_idx,
                global_idx
            );
        }
    }

    // =========================================================================
    // Integration Tests
    // =========================================================================

    #[test]
    fn tesseract_capacity_via_lp() {
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

        let result = crate::billiard_lp::compute_billiard_capacity_lp(hrep)
            .expect("should compute capacity");

        assert!(
            (result.capacity - 4.0).abs() < 1e-6,
            "Tesseract capacity should be 4, got {}",
            result.capacity
        );
    }
}
