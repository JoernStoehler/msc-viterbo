//! Tube data structures and operations.
//!
//! A tube represents all Reeb trajectories with a fixed facet sequence.
//! See spec §2.9-2.13 for definitions.

use nalgebra::{Matrix2, Vector2, Vector4};

use crate::consts::EPS;
use crate::error::{Error, Result};
use crate::geom::{intersect_polygons, point_in_polygon, symplectic_form, Polygon2D, J_MATRIX, K_MATRIX};
use crate::polytope::{PolytopeData, TwoFaceEnriched};
use crate::trivialization::{compute_transition_matrix, untrivialize};

// =============================================================================
// Affine Map (§2.9)
// =============================================================================

/// An affine map in 2D: f(x) = Ax + b
#[derive(Debug, Clone)]
pub struct AffineMap2D {
    /// Linear part (2×2 matrix)
    pub matrix: Matrix2<f64>,
    /// Translation offset
    pub offset: Vector2<f64>,
}

impl AffineMap2D {
    /// Identity map
    pub fn identity() -> Self {
        Self {
            matrix: Matrix2::identity(),
            offset: Vector2::zeros(),
        }
    }

    /// Apply the affine map to a point
    pub fn apply(&self, x: &Vector2<f64>) -> Vector2<f64> {
        self.matrix * x + self.offset
    }

    /// Apply the affine map to all vertices of a polygon
    pub fn apply_to_polygon(&self, p: &Polygon2D) -> Polygon2D {
        Polygon2D::new(p.vertices.iter().map(|v| self.apply(v)).collect())
    }
}

/// Compose two affine maps: f ∘ g
/// (Ax + b) ∘ (Cx + d) = A(Cx + d) + b = (AC)x + (Ad + b)
pub fn compose_affine(f: &AffineMap2D, g: &AffineMap2D) -> AffineMap2D {
    AffineMap2D {
        matrix: f.matrix * g.matrix,
        offset: f.matrix * g.offset + f.offset,
    }
}

// =============================================================================
// Affine Function (§2.9)
// =============================================================================

/// An affine function in 2D: f(x) = ⟨g, x⟩ + c
#[derive(Debug, Clone)]
pub struct AffineFunc {
    /// Gradient vector
    pub gradient: Vector2<f64>,
    /// Constant term
    pub constant: f64,
}

impl AffineFunc {
    /// Zero function
    pub fn zero() -> Self {
        Self {
            gradient: Vector2::zeros(),
            constant: 0.0,
        }
    }

    /// Evaluate the function at a point
    pub fn eval(&self, x: &Vector2<f64>) -> f64 {
        self.gradient.dot(x) + self.constant
    }
}

/// Add two affine functions
pub fn add_affine_funcs(f: &AffineFunc, g: &AffineFunc) -> AffineFunc {
    AffineFunc {
        gradient: f.gradient + g.gradient,
        constant: f.constant + g.constant,
    }
}

/// Compose affine function with affine map: f(Ax + b)
/// where f(y) = ⟨g, y⟩ + c
/// Result: ⟨g, Ax + b⟩ + c = ⟨Aᵀg, x⟩ + (⟨g, b⟩ + c)
pub fn compose_with_map(f: &AffineFunc, map: &AffineMap2D) -> AffineFunc {
    AffineFunc {
        gradient: map.matrix.transpose() * f.gradient,
        constant: f.gradient.dot(&map.offset) + f.constant,
    }
}

// =============================================================================
// Tube Structure (§2.9)
// =============================================================================

/// A tube represents all Reeb trajectories with a fixed facet sequence.
#[derive(Debug, Clone)]
pub struct Tube {
    /// Facet sequence [i₀, i₁, ..., iₖ, iₖ₊₁]
    /// Start 2-face: F_{i₀, i₁}
    /// End 2-face: F_{iₖ, iₖ₊₁}
    pub facet_sequence: Vec<usize>,

    /// Set of valid starting points (in trivialized coords of start 2-face)
    pub p_start: Polygon2D,

    /// Set of valid ending points (in trivialized coords of end 2-face)
    pub p_end: Polygon2D,

    /// Flow map: maps start point → end point
    pub flow_map: AffineMap2D,

    /// Action as function of start point
    pub action_func: AffineFunc,

    /// Accumulated rotation (turns)
    pub rotation: f64,
}

impl Tube {
    /// Check if this is a root tube (facet_sequence length = 2)
    pub fn is_root(&self) -> bool {
        self.facet_sequence.len() == 2
    }

    /// Check if this tube is "next-step closeable"
    /// (first facet = last facet, can close by adding second facet)
    pub fn is_next_step_closeable(&self) -> bool {
        self.facet_sequence.len() >= 3
            && self.facet_sequence[0] == *self.facet_sequence.last().unwrap()
    }

    /// Check if this tube is closed
    /// (start 2-face = end 2-face, i.e., facets[m-1] = facets[0] AND facets[m] = facets[1])
    pub fn is_closed(&self) -> bool {
        let m = self.facet_sequence.len();
        if m < 4 {
            return false;
        }
        self.facet_sequence[m - 2] == self.facet_sequence[0]
            && self.facet_sequence[m - 1] == self.facet_sequence[1]
    }

    /// Get the action lower bound (minimum action over all trajectories in tube)
    ///
    /// Since action is affine over start polygon, minimum is at a vertex.
    pub fn action_lower_bound(&self) -> f64 {
        if self.p_start.is_empty() {
            return f64::INFINITY;
        }
        self.p_start
            .vertices
            .iter()
            .map(|v| self.action_func.eval(v))
            .fold(f64::INFINITY, f64::min)
    }

    /// Check if the tube is empty (no valid trajectories)
    pub fn is_empty(&self) -> bool {
        self.p_start.is_empty() || self.p_end.is_empty()
    }

    /// Get the start 2-face indices (i₀, i₁)
    pub fn start_2face(&self) -> (usize, usize) {
        (self.facet_sequence[0], self.facet_sequence[1])
    }

    /// Get the end 2-face indices
    pub fn end_2face(&self) -> (usize, usize) {
        let m = self.facet_sequence.len();
        (self.facet_sequence[m - 2], self.facet_sequence[m - 1])
    }

    /// Get the current facet (last in sequence)
    pub fn current_facet(&self) -> usize {
        *self.facet_sequence.last().unwrap()
    }
}

// =============================================================================
// Root Tube Creation (§2.9)
// =============================================================================

/// Create a root tube for a 2-face.
///
/// A root tube has facet_sequence = [i, j] and represents zero-length
/// trajectories at the 2-face F_{i,j}.
pub fn create_root_tube(two_face: &TwoFaceEnriched) -> Tube {
    // For root tubes, start = end, and flow_map = identity
    Tube {
        facet_sequence: vec![two_face.i, two_face.j],
        p_start: two_face.polygon_2d.clone(),
        p_end: two_face.polygon_2d.clone(),
        flow_map: AffineMap2D::identity(),
        action_func: AffineFunc::zero(),
        rotation: 0.0,
    }
}

// =============================================================================
// Tube Extension (§2.10)
// =============================================================================

/// Compute the facet flow map and time function.
///
/// This computes the affine map and time function for flowing along a facet
/// from one 2-face to the next.
fn compute_facet_flow(
    tube: &Tube,
    next_facet: usize,
    data: &PolytopeData,
) -> Option<(AffineMap2D, AffineFunc)> {
    let seq = &tube.facet_sequence;
    let prev_facet = seq[seq.len() - 2]; // i_k
    let curr_facet = seq[seq.len() - 1]; // i_{k+1}, the facet we flow along

    // Get 2-faces
    let entry_2face = data.get_two_face_enriched(prev_facet, curr_facet)?;
    let exit_2face = data.get_two_face_enriched(curr_facet, next_facet)?;

    // Get Reeb vector on current facet
    let r_curr = data.reeb_vector(curr_facet);
    let n_next = data.normal(next_facet);
    let h_next = data.height(next_facet);

    // Denominator of time formula: ⟨R_curr, n_next⟩
    let r_dot_n = r_curr.dot(n_next);
    if r_dot_n.abs() < EPS {
        // Lagrangian 2-face or degenerate - shouldn't happen
        return None;
    }

    // Entry trivialization uses exit_normal per CH2021 convention
    let entry_triv_normal = &entry_2face.exit_normal;
    let j_n_entry = J_MATRIX * entry_triv_normal;
    let k_n_entry = K_MATRIX * entry_triv_normal;
    let c_entry = entry_2face.centroid_4d;

    // Exit trivialization
    let exit_triv_normal = &exit_2face.exit_normal;
    let j_n_exit = J_MATRIX * exit_triv_normal;
    let k_n_exit = K_MATRIX * exit_triv_normal;
    let c_exit = exit_2face.centroid_4d;

    // Time function: t(p_2d) = t_const + ⟨t_grad, p_2d⟩
    let t_const = (h_next - c_entry.dot(n_next)) / r_dot_n;
    let t_grad = Vector2::new(
        -j_n_entry.dot(n_next) / r_dot_n,
        -k_n_entry.dot(n_next) / r_dot_n,
    );
    let time_func = AffineFunc {
        gradient: t_grad,
        constant: t_const,
    };

    // Transition matrix: entry→exit
    let psi = compute_transition_matrix(entry_triv_normal, exit_triv_normal);

    // Time-dependent term
    let r_triv = Vector2::new(r_curr.dot(&j_n_exit), r_curr.dot(&k_n_exit));

    // Matrix: A = ψ + r_triv ⊗ t_grad
    let a_matrix = psi + r_triv * t_grad.transpose();

    // Offset: b = trivialize(exit_triv_normal, c_entry - c_exit + t_const * R_curr)
    let delta_c = c_entry - c_exit + r_curr * t_const;
    let b_offset = Vector2::new(delta_c.dot(&j_n_exit), delta_c.dot(&k_n_exit));

    let flow_map = AffineMap2D {
        matrix: a_matrix,
        offset: b_offset,
    };

    Some((flow_map, time_func))
}

/// Extend a tube by one facet transition.
///
/// Returns None if the extension is invalid (no adjacent 2-face or empty tube).
pub fn extend_tube(tube: &Tube, next_facet: usize, data: &PolytopeData) -> Option<Tube> {
    let current_facet = tube.current_facet();

    // Check adjacency
    let exit_2face = data.get_two_face_enriched(current_facet, next_facet)?;

    // Compute flow across the facet
    let (phi, time_func) = compute_facet_flow(tube, next_facet, data)?;

    // New endpoint set: apply flow map and intersect with exit 2-face polygon
    let flowed_end = phi.apply_to_polygon(&tube.p_end);
    let new_p_end = intersect_polygons(&flowed_end, &exit_2face.polygon_2d);

    if new_p_end.is_empty() {
        return None; // No valid trajectories
    }

    // Compose flow maps and action functions
    let new_flow_map = compose_affine(&phi, &tube.flow_map);
    let new_action_func = add_affine_funcs(&tube.action_func, &compose_with_map(&time_func, &tube.flow_map));

    Some(Tube {
        facet_sequence: [&tube.facet_sequence[..], &[next_facet]].concat(),
        p_start: tube.p_start.clone(),
        p_end: new_p_end,
        flow_map: new_flow_map,
        action_func: new_action_func,
        rotation: tube.rotation + exit_2face.rotation_number(),
    })
}

// =============================================================================
// Tube Closure and Fixed Points (§2.11)
// =============================================================================

/// Find closed orbits in a closed tube by solving for fixed points.
///
/// For a closed tube, solve ψ(s) = s where ψ = flow_map.
/// Returns (action, fixed_point) pairs.
pub fn find_fixed_points(tube: &Tube) -> Result<Vec<(f64, Vector2<f64>)>> {
    if !tube.is_closed() {
        return Ok(vec![]);
    }

    // Solve (A - I) s = -b
    let a_minus_i = tube.flow_map.matrix - Matrix2::identity();
    let neg_b = -tube.flow_map.offset;

    let det = a_minus_i.determinant();

    if det.abs() < EPS {
        // Near-singular: degenerate polytope or numerical instability
        return Err(Error::NearSingularFlowMap {
            det,
            facets: tube.facet_sequence.clone(),
        });
    }

    // Unique fixed point
    let s = a_minus_i
        .try_inverse()
        .ok_or_else(|| Error::NearSingularFlowMap {
            det,
            facets: tube.facet_sequence.clone(),
        })?
        * neg_b;

    // Check if fixed point is in the valid start region
    if !point_in_polygon(&s, &tube.p_start) {
        return Ok(vec![]);
    }

    let action = tube.action_func.eval(&s);

    // Sanity check: action should be positive
    if action <= 0.0 {
        return Ok(vec![]);
    }

    Ok(vec![(action, s)])
}

// =============================================================================
// 4D Reconstruction (§2.12)
// =============================================================================

/// A closed Reeb orbit on the polytope boundary.
#[derive(Debug, Clone)]
pub struct ClosedReebOrbit {
    /// Period = action
    pub period: f64,
    /// Breakpoints in 4D (p₀, p₁, ..., pₘ with pₘ = p₀)
    pub breakpoints: Vec<Vector4<f64>>,
    /// Facet indices for each segment
    pub segment_facets: Vec<usize>,
    /// Time spent on each segment
    pub segment_times: Vec<f64>,
}

impl ClosedReebOrbit {
    /// Validate the orbit against the polytope.
    pub fn validate(&self, data: &PolytopeData) -> Result<()> {
        // 1. Closure
        if (self.breakpoints.last().unwrap() - &self.breakpoints[0]).norm() > EPS {
            return Err(Error::ValidationError("Orbit not closed".to_string()));
        }

        // 2. All breakpoints on boundary
        for (k, p) in self.breakpoints.iter().enumerate() {
            let mut on_boundary = false;
            for i in 0..data.num_facets() {
                let dist = data.normal(i).dot(p) - data.height(i);
                if dist.abs() < EPS {
                    on_boundary = true;
                    break;
                }
            }
            if !on_boundary {
                return Err(Error::ValidationError(format!(
                    "Breakpoint {} not on boundary",
                    k
                )));
            }
        }

        // 3. Segments lie on claimed facets
        for k in 0..self.segment_facets.len() {
            let i = self.segment_facets[k];
            let p_start = &self.breakpoints[k];
            let p_end = &self.breakpoints[k + 1];

            let h = data.height(i);
            let n = data.normal(i);

            if (n.dot(p_start) - h).abs() > EPS {
                return Err(Error::ValidationError(format!(
                    "Segment {} start not on facet {}",
                    k, i
                )));
            }
            if (n.dot(p_end) - h).abs() > EPS {
                return Err(Error::ValidationError(format!(
                    "Segment {} end not on facet {}",
                    k, i
                )));
            }
        }

        // 4. Velocities match Reeb vectors
        for k in 0..self.segment_facets.len() {
            let i = self.segment_facets[k];
            let displacement = &self.breakpoints[k + 1] - &self.breakpoints[k];
            let velocity = displacement / self.segment_times[k];
            let reeb = data.reeb_vector(i);

            if (velocity - reeb).norm() > EPS * reeb.norm().max(1.0) {
                return Err(Error::ValidationError(format!(
                    "Segment {} velocity mismatch",
                    k
                )));
            }
        }

        // 5. Period = sum of times = action
        let time_sum: f64 = self.segment_times.iter().sum();
        if (self.period - time_sum).abs() > EPS {
            return Err(Error::ValidationError("Period mismatch".to_string()));
        }

        let action = action_of_closed_polygon(&self.breakpoints);
        if (self.period - action).abs() > EPS * self.period.max(1.0) {
            return Err(Error::ValidationError("Action mismatch".to_string()));
        }

        Ok(())
    }
}

/// Compute action of a closed polygonal curve.
///
/// A = (1/2) Σ ω(vₖ, vₖ₊₁)
fn action_of_closed_polygon(vertices: &[Vector4<f64>]) -> f64 {
    let n = vertices.len();
    let mut sum = 0.0;
    for k in 0..n {
        sum += symplectic_form(&vertices[k], &vertices[(k + 1) % n]);
    }
    0.5 * sum
}

/// Convert a 2D trivialized point back to 4D.
fn untrivialize_point(point_2d: &Vector2<f64>, two_face: &TwoFaceEnriched) -> Vector4<f64> {
    let offset_4d = untrivialize(&two_face.exit_normal, point_2d);
    two_face.centroid_4d + offset_4d
}

/// Reconstruct a 4D orbit from a 2D fixed point.
pub fn reconstruct_4d_orbit(
    fixed_point_2d: &Vector2<f64>,
    tube: &Tube,
    data: &PolytopeData,
) -> Result<ClosedReebOrbit> {
    let seq = &tube.facet_sequence;
    let n_segments = seq.len() - 2;

    // Start from the 2D fixed point on the start 2-face
    let start_two_face = data
        .get_two_face_enriched(seq[0], seq[1])
        .ok_or_else(|| Error::ValidationError("Start 2-face not found".to_string()))?;
    let start_4d = untrivialize_point(fixed_point_2d, start_two_face);

    // Trace through each facet to get breakpoints
    let mut breakpoints = vec![start_4d];
    let mut current_2d = *fixed_point_2d;

    for k in 1..=n_segments {
        // Build partial flow to get exit point
        let entry_2face = data
            .get_two_face_enriched(seq[k - 1], seq[k])
            .ok_or_else(|| Error::ValidationError("Entry 2-face not found".to_string()))?;
        let exit_2face = data
            .get_two_face_enriched(seq[k], seq[k + 1])
            .ok_or_else(|| Error::ValidationError("Exit 2-face not found".to_string()))?;

        // Get Reeb vector
        let r_curr = data.reeb_vector(seq[k]);
        let n_next = data.normal(seq[k + 1]);
        let h_next = data.height(seq[k + 1]);

        let r_dot_n = r_curr.dot(n_next);
        if r_dot_n.abs() < EPS {
            return Err(Error::ValidationError("Degenerate flow".to_string()));
        }

        // Entry trivialization
        let entry_triv_normal = &entry_2face.exit_normal;
        let _j_n_entry = J_MATRIX * entry_triv_normal;
        let _k_n_entry = K_MATRIX * entry_triv_normal;
        let c_entry = entry_2face.centroid_4d;

        // Exit trivialization
        let exit_triv_normal = &exit_2face.exit_normal;
        let j_n_exit = J_MATRIX * exit_triv_normal;
        let k_n_exit = K_MATRIX * exit_triv_normal;
        let c_exit = exit_2face.centroid_4d;

        // Convert current 2D point to 4D
        let p_4d = c_entry + untrivialize(entry_triv_normal, &current_2d);

        // Compute time to exit
        let t = (h_next - p_4d.dot(n_next)) / r_dot_n;

        // Flow to exit point
        let q_4d = p_4d + r_curr * t;
        breakpoints.push(q_4d);

        // Convert to exit 2D coordinates
        let q_rel = q_4d - c_exit;
        current_2d = Vector2::new(q_rel.dot(&j_n_exit), q_rel.dot(&k_n_exit));
    }

    // Verify closure
    if (breakpoints.last().unwrap() - &start_4d).norm() > EPS {
        return Err(Error::ValidationError("Orbit failed to close".to_string()));
    }

    // Compute segment facets and times
    let segment_facets: Vec<usize> = (0..n_segments).map(|k| seq[k + 1]).collect();

    let segment_times: Vec<f64> = (0..n_segments)
        .map(|k| {
            let facet_idx = segment_facets[k];
            let displacement = &breakpoints[k + 1] - &breakpoints[k];
            let reeb = data.reeb_vector(facet_idx);
            displacement.dot(&reeb) / reeb.norm_squared()
        })
        .collect();

    let period: f64 = segment_times.iter().sum();

    Ok(ClosedReebOrbit {
        period,
        breakpoints,
        segment_facets,
        segment_times,
    })
}

// =============================================================================
// Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    #[test]
    fn test_affine_map_identity() {
        let identity = AffineMap2D::identity();
        let p = Vector2::new(1.0, 2.0);
        assert_relative_eq!(identity.apply(&p), p, epsilon = EPS);
    }

    #[test]
    fn test_compose_affine_with_identity() {
        let f = AffineMap2D {
            matrix: Matrix2::new(1.0, 2.0, 3.0, 4.0),
            offset: Vector2::new(5.0, 6.0),
        };
        let identity = AffineMap2D::identity();

        let fg = compose_affine(&f, &identity);
        assert_relative_eq!(fg.matrix, f.matrix, epsilon = EPS);
        assert_relative_eq!(fg.offset, f.offset, epsilon = EPS);
    }

    #[test]
    fn test_affine_func_eval() {
        let f = AffineFunc {
            gradient: Vector2::new(1.0, 2.0),
            constant: 3.0,
        };
        let x = Vector2::new(4.0, 5.0);
        // f(x) = 1*4 + 2*5 + 3 = 4 + 10 + 3 = 17
        assert_relative_eq!(f.eval(&x), 17.0, epsilon = EPS);
    }

    #[test]
    fn test_tube_is_closed() {
        // Closed: [0, 1, 2, 0, 1]
        let tube = Tube {
            facet_sequence: vec![0, 1, 2, 0, 1],
            p_start: Polygon2D::new(vec![Vector2::zeros()]),
            p_end: Polygon2D::new(vec![Vector2::zeros()]),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
        };
        assert!(tube.is_closed());

        // Not closed: [0, 1, 2, 3]
        let tube2 = Tube {
            facet_sequence: vec![0, 1, 2, 3],
            p_start: Polygon2D::new(vec![Vector2::zeros()]),
            p_end: Polygon2D::new(vec![Vector2::zeros()]),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
        };
        assert!(!tube2.is_closed());
    }

    #[test]
    fn test_tube_is_next_step_closeable() {
        // Next-step closeable: [0, 1, 2, 0]
        let tube = Tube {
            facet_sequence: vec![0, 1, 2, 0],
            p_start: Polygon2D::new(vec![Vector2::zeros()]),
            p_end: Polygon2D::new(vec![Vector2::zeros()]),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
        };
        assert!(tube.is_next_step_closeable());

        // Not next-step closeable: [0, 1, 2, 3]
        let tube2 = Tube {
            facet_sequence: vec![0, 1, 2, 3],
            p_start: Polygon2D::new(vec![Vector2::zeros()]),
            p_end: Polygon2D::new(vec![Vector2::zeros()]),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
        };
        assert!(!tube2.is_next_step_closeable());
    }

    #[test]
    fn test_action_of_closed_polygon() {
        // Rectangle with vertices (0,0,0,0), (1,0,0,0), (1,0,1,0), (0,0,1,0)
        // in q1-p1 plane (symplectic area = 1)
        let vertices = vec![
            Vector4::new(0.0, 0.0, 0.0, 0.0),
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(1.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
        ];
        let action = action_of_closed_polygon(&vertices);
        assert_relative_eq!(action, 1.0, epsilon = EPS);
    }
}
