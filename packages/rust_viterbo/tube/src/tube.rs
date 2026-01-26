//! Tube data structures and operations.
//!
//! A **tube** represents all Reeb trajectories with a fixed combinatorial class (facet sequence).
//! Key operations:
//! - Root tube creation at each 2-face
//! - Tube extension by one facet transition
//! - Closure detection and fixed point finding
//! - 4D orbit reconstruction

use nalgebra::{Matrix2, Vector2, Vector4};

use crate::consts::{EPS, EPS_ROTATION};
use crate::error::{TubeError, TubeResult};
use crate::geom::action_of_closed_polygon;
use crate::polygon::{
    add_affine_funcs, compose_affine, compose_func_with_map, intersect_line_polygon,
    intersect_polygons, AffineFunc, AffineMap2D, Polygon2D,
};
use crate::polytope::{PolytopeData, TwoFaceEnriched};
use crate::symplectic::{apply_j, apply_k};
use crate::trivialization::untrivialize_point;

/// A tube: a set of Reeb trajectories with a fixed facet sequence.
#[derive(Debug, Clone)]
pub struct Tube {
    /// Facet sequence [i₀, i₁, ..., iₖ, i_{k+1}].
    /// Start 2-face: F_{i₀, i₁}
    /// End 2-face: F_{iₖ, i_{k+1}}
    pub facet_sequence: Vec<usize>,

    /// Set of valid starting points in 2D trivialized coordinates of start 2-face.
    pub p_start: Polygon2D,

    /// Set of valid ending points (in end 2-face coordinates).
    pub p_end: Polygon2D,

    /// Flow map: maps start point → end point.
    pub flow_map: AffineMap2D,

    /// Action as function of start point.
    pub action_func: AffineFunc,

    /// Accumulated rotation (in turns).
    pub rotation: f64,
}

impl Tube {
    /// Create a root tube at a 2-face.
    ///
    /// A root tube has:
    /// - facet_sequence = [i, j] (the 2-face)
    /// - p_start = p_end = 2-face polygon
    /// - flow_map = identity
    /// - action_func = 0
    /// - rotation = 0
    pub fn root(two_face: &TwoFaceEnriched) -> Self {
        Self {
            facet_sequence: vec![two_face.entry_facet, two_face.exit_facet],
            p_start: two_face.polygon_2d.clone(),
            p_end: two_face.polygon_2d.clone(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
        }
    }

    /// Check if this is an initial (root) tube.
    pub fn is_initial(&self) -> bool {
        self.facet_sequence.len() == 2
    }

    /// Get the start 2-face indices (entry, exit).
    pub fn start_2face(&self) -> (usize, usize) {
        (self.facet_sequence[0], self.facet_sequence[1])
    }

    /// Get the end 2-face indices (entry, exit).
    pub fn end_2face(&self) -> (usize, usize) {
        let n = self.facet_sequence.len();
        (self.facet_sequence[n - 2], self.facet_sequence[n - 1])
    }

    /// Check if this tube is next-step closeable.
    ///
    /// A tube is next-step closeable if first facet = last facet.
    /// Extending with facet_sequence[1] yields a closed tube.
    pub fn is_next_step_closeable(&self) -> bool {
        self.facet_sequence.len() >= 3
            && self.facet_sequence[0] == self.facet_sequence[self.facet_sequence.len() - 1]
    }

    /// Check if this tube is closed.
    ///
    /// A tube is closed if start 2-face = end 2-face and it's not initial.
    pub fn is_closed(&self) -> bool {
        if self.facet_sequence.len() < 5 {
            return false; // Minimum closed tube length is 5
        }
        let n = self.facet_sequence.len();
        self.facet_sequence[n - 2] == self.facet_sequence[0]
            && self.facet_sequence[n - 1] == self.facet_sequence[1]
    }

    /// Get the action lower bound (minimum action over p_start).
    pub fn action_lower_bound(&self) -> f64 {
        if self.p_start.is_empty() {
            return f64::INFINITY;
        }
        self.action_func.min_over_polygon(&self.p_start)
    }

    /// Check if the tube should be pruned.
    pub fn should_prune(&self, best_action: f64) -> bool {
        // Prune if empty
        if self.p_start.is_empty() || self.p_end.is_empty() {
            return true;
        }

        // Prune if rotation exceeds bound
        if self.rotation > 2.0 + EPS_ROTATION {
            return true;
        }

        // Prune if action lower bound exceeds best
        if self.action_lower_bound() >= best_action {
            return true;
        }

        false
    }
}

/// Extend a tube by one facet transition.
///
/// Returns None if the extension results in an empty tube.
pub fn extend_tube(
    tube: &Tube,
    next_facet: usize,
    data: &PolytopeData,
) -> TubeResult<Option<Tube>> {
    let current_end_facet = tube.facet_sequence[tube.facet_sequence.len() - 1];

    // Get the 2-face between current end and next facet
    let exit_2face = match data.get_two_face_enriched(current_end_facet, next_facet) {
        Some(tf) => tf,
        None => return Ok(None), // No valid 2-face
    };

    // Compute flow across the facet
    let (phi, time_func) = match compute_facet_flow(tube, next_facet, data) {
        Ok(result) => result,
        Err(TubeError::ValidationFailed(_)) => {
            // Flow direction is wrong - not a valid extension
            return Ok(None);
        }
        Err(e) => return Err(e),
    };

    // Apply flow map to current end polygon
    let mapped_end = phi.apply_to_polygon(&tube.p_end);

    // Intersect with exit 2-face polygon
    let new_p_end = intersect_polygons(&mapped_end, &exit_2face.polygon_2d);

    if new_p_end.is_empty() {
        return Ok(None); // No valid trajectories
    }

    // Compose flow maps
    let new_flow_map = compose_affine(&phi, &tube.flow_map);

    // Compose action functions
    // new_action(s) = tube.action(s) + time(tube.flow_map(s))
    let time_composed = compose_func_with_map(&time_func, &tube.flow_map);
    let new_action_func = add_affine_funcs(&tube.action_func, &time_composed);

    // Accumulate rotation
    let new_rotation = tube.rotation + exit_2face.rotation;

    Ok(Some(Tube {
        facet_sequence: [&tube.facet_sequence[..], &[next_facet]].concat(),
        p_start: tube.p_start.clone(),
        p_end: new_p_end,
        flow_map: new_flow_map,
        action_func: new_action_func,
        rotation: new_rotation,
    }))
}

/// Compute the flow map and time function for flowing across a facet.
///
/// Returns (flow_map, time_func) where:
/// - flow_map: 2D affine map from entry 2-face coords to exit 2-face coords
/// - time_func: affine function giving flow time as function of entry point
fn compute_facet_flow(
    tube: &Tube,
    next_facet: usize,
    data: &PolytopeData,
) -> TubeResult<(AffineMap2D, AffineFunc)> {
    let seq = &tube.facet_sequence;
    let prev_facet = seq[seq.len() - 2];
    let curr_facet = seq[seq.len() - 1];

    // Get 2-faces
    let entry_2face = data.get_two_face_enriched(prev_facet, curr_facet).ok_or_else(|| {
        TubeError::NumericalInstability {
            message: format!("No enriched 2-face for ({}, {})", prev_facet, curr_facet),
            facet_sequence: Some(seq.clone()),
        }
    })?;

    let exit_2face = data.get_two_face_enriched(curr_facet, next_facet).ok_or_else(|| {
        TubeError::NumericalInstability {
            message: format!("No enriched 2-face for ({}, {})", curr_facet, next_facet),
            facet_sequence: Some(seq.clone()),
        }
    })?;

    // Get Reeb vector on current facet
    let r_curr = data.reeb(curr_facet);
    let n_next = data.normal(next_facet);
    let h_next = data.height(next_facet);

    // Denominator: ⟨R_curr, n_next⟩
    // This must be positive for flow toward exit facet
    let r_dot_n = r_curr.dot(n_next);

    if r_dot_n.abs() < EPS {
        return Err(TubeError::NumericalInstability {
            message: format!(
                "Degenerate flow: ⟨R_curr, n_next⟩ = {:.2e}",
                r_dot_n
            ),
            facet_sequence: Some(seq.clone()),
        });
    }

    if r_dot_n < 0.0 {
        // Flow is going away from exit facet, not a valid extension
        // Signal this with a sentinel that extend_tube will convert to Ok(None)
        return Err(TubeError::ValidationFailed(format!(
            "Flow direction wrong: ⟨R_curr, n_next⟩ = {:.2e}",
            r_dot_n
        )));
    }

    // Get basis vectors and centroids
    let b_entry = &entry_2face.basis_exit;
    let c_entry = entry_2face.centroid_4d;
    let c_exit = exit_2face.centroid_4d;
    let n_exit = &exit_2face.exit_normal;
    let jn_exit = apply_j(n_exit);
    let kn_exit = apply_k(n_exit);

    // Time function: t(p_2d) = t_const + ⟨t_grad, p_2d⟩
    // t = (h_next - ⟨p_4d, n_next⟩) / ⟨R_curr, n_next⟩
    // p_4d = c_entry + a * b_entry[0] + b * b_entry[1]
    let t_const = (h_next - c_entry.dot(n_next)) / r_dot_n;
    let t_grad = Vector2::new(
        -b_entry[0].dot(n_next) / r_dot_n,
        -b_entry[1].dot(n_next) / r_dot_n,
    );
    let time_func = AffineFunc {
        gradient: t_grad,
        constant: t_const,
    };

    // Transition matrix: ψ[k, l] = ⟨b_entry[l], (Jn_exit or Kn_exit)⟩
    let psi = Matrix2::new(
        b_entry[0].dot(&jn_exit),
        b_entry[1].dot(&jn_exit),
        b_entry[0].dot(&kn_exit),
        b_entry[1].dot(&kn_exit),
    );

    // Reeb vector in exit coordinates
    let r_triv = Vector2::new(r_curr.dot(&jn_exit), r_curr.dot(&kn_exit));

    // Flow matrix: A = ψ + r_triv ⊗ t_grad
    let a_matrix = psi + r_triv * t_grad.transpose();

    // Offset: b = τ_exit(c_entry - c_exit + t_const * R_curr)
    let delta_c = c_entry - c_exit + *r_curr * t_const;
    let b_offset = Vector2::new(delta_c.dot(&jn_exit), delta_c.dot(&kn_exit));

    let flow_map = AffineMap2D::new(a_matrix, b_offset);

    Ok((flow_map, time_func))
}

/// Find closed orbits in a closed tube.
///
/// For a closed tube, the flow map ψ maps the start 2-face to itself.
/// Fixed points ψ(s) = s correspond to closed orbits.
///
/// Two cases:
/// 1. **Hyperbolic**: det(A - I) ≠ 0 → unique fixed point, check if in p_start
/// 2. **Parabolic**: det(A - I) ≈ 0 (shear matrix) → line of fixed points, intersect with p_start
pub fn find_closed_orbits(tube: &Tube) -> TubeResult<Vec<(f64, Vector2<f64>)>> {
    if !tube.is_closed() {
        return Ok(Vec::new());
    }

    // Solve (A - I) s = -b
    let a_minus_i = tube.flow_map.matrix - Matrix2::identity();
    let neg_b = -tube.flow_map.offset;

    let det = a_minus_i.determinant();

    if det.abs() >= EPS {
        // Hyperbolic case: unique fixed point
        let s = a_minus_i.try_inverse().unwrap() * neg_b;

        // Check if fixed point is in p_start
        if !tube.p_start.contains(&s) {
            return Ok(Vec::new());
        }

        let action = tube.action_func.eval(&s);
        return Ok(vec![(action, s)]);
    }

    // Parabolic case: det(A - I) ≈ 0, shear matrix
    // There's a line of fixed points (or no fixed points if system is inconsistent)
    find_parabolic_fixed_points(tube, &a_minus_i, &neg_b)
}

/// Handle the parabolic case where det(A - I) ≈ 0.
///
/// For a shear matrix like [[1, k], [0, 1]], A - I = [[0, k], [0, 0]].
/// The kernel is spanned by (1, 0) (or a similar direction).
/// Fixed points satisfy (A - I)s = -b, which may have:
/// - No solutions (inconsistent)
/// - A line of solutions: s = s_particular + t * kernel_direction
fn find_parabolic_fixed_points(
    tube: &Tube,
    a_minus_i: &Matrix2<f64>,
    neg_b: &Vector2<f64>,
) -> TubeResult<Vec<(f64, Vector2<f64>)>> {
    // Find kernel direction: look for non-zero column or row
    // For a rank-1 matrix, the kernel is 1-dimensional
    let kernel_dir = find_kernel_direction(a_minus_i);

    // Try to find a particular solution
    // For a 2x2 singular matrix with rank 1, we solve the non-zero row
    let particular = match find_particular_solution(a_minus_i, neg_b) {
        Some(s) => s,
        None => {
            // System is inconsistent: no fixed points
            return Ok(Vec::new());
        }
    };

    // Fixed point line: particular + t * kernel_dir
    // Intersect with p_start polygon
    let intersection = match intersect_line_polygon(&particular, &kernel_dir, &tube.p_start) {
        Some((t_min, t_max)) => (t_min, t_max),
        None => return Ok(Vec::new()),
    };

    // Compute orbits at segment endpoints
    let mut orbits = Vec::new();

    for &t in &[intersection.0, intersection.1] {
        if t.is_finite() {
            let s = particular + kernel_dir * t;
            if tube.p_start.contains(&s) {
                let action = tube.action_func.eval(&s);
                orbits.push((action, s));
            }
        }
    }

    // Also check for minimum action along the segment
    // Action(t) = ⟨g, particular + t * kernel⟩ + c = action_at_particular + t * ⟨g, kernel⟩
    let g_dot_kernel = tube.action_func.gradient.dot(&kernel_dir);
    if g_dot_kernel.abs() > EPS {
        // Action is linear in t, so minimum is at one of the endpoints (already included)
    } else {
        // Action is constant along the line - any point works, return midpoint
        let t_mid = (intersection.0 + intersection.1) / 2.0;
        if t_mid.is_finite() {
            let s = particular + kernel_dir * t_mid;
            if tube.p_start.contains(&s) {
                let action = tube.action_func.eval(&s);
                // Only add if not already present
                if !orbits.iter().any(|(_, p)| (p - s).norm() < EPS) {
                    orbits.push((action, s));
                }
            }
        }
    }

    // Sort by action
    orbits.sort_by(|a, b| a.0.partial_cmp(&b.0).unwrap());

    Ok(orbits)
}

/// Find a direction in the kernel of a singular 2x2 matrix.
fn find_kernel_direction(m: &Matrix2<f64>) -> Vector2<f64> {
    // For a singular matrix, at least one column is linearly dependent
    // Kernel direction: perpendicular to any non-zero row
    let row0 = Vector2::new(m[(0, 0)], m[(0, 1)]);
    let row1 = Vector2::new(m[(1, 0)], m[(1, 1)]);

    // Use the row with larger norm
    let (row, _) = if row0.norm() >= row1.norm() {
        (row0, row1)
    } else {
        (row1, row0)
    };

    if row.norm() < EPS {
        // Zero matrix: any direction works
        return Vector2::new(1.0, 0.0);
    }

    // Perpendicular to the row
    let kernel = Vector2::new(-row[1], row[0]);
    kernel / kernel.norm()
}

/// Find a particular solution to (A - I)s = -b for a singular matrix.
/// Returns None if the system is inconsistent.
fn find_particular_solution(a_minus_i: &Matrix2<f64>, neg_b: &Vector2<f64>) -> Option<Vector2<f64>> {
    // Find the non-zero row (the one with constraints)
    let row0 = Vector2::new(a_minus_i[(0, 0)], a_minus_i[(0, 1)]);
    let row1 = Vector2::new(a_minus_i[(1, 0)], a_minus_i[(1, 1)]);

    let norm0 = row0.norm();
    let norm1 = row1.norm();

    if norm0 < EPS && norm1 < EPS {
        // Zero matrix: any point is a fixed point if b = 0
        if neg_b.norm() < EPS {
            return Some(Vector2::zeros());
        } else {
            return None; // Inconsistent
        }
    }

    // Use the row with larger norm as the constraint
    let (primary_row, primary_b, secondary_row, secondary_b) = if norm0 >= norm1 {
        (row0, neg_b[0], row1, neg_b[1])
    } else {
        (row1, neg_b[1], row0, neg_b[0])
    };

    // Constraint: ⟨primary_row, s⟩ = primary_b
    // Choose s to lie on this line, e.g., s = (primary_b / ||row||²) * row
    let norm_sq = primary_row.norm_squared();
    let s = primary_row * (primary_b / norm_sq);

    // Check consistency: if secondary row is non-trivial, it must also be satisfied
    if secondary_row.norm() > EPS {
        let residual = secondary_row.dot(&s) - secondary_b;
        if residual.abs() > EPS {
            return None; // Inconsistent system
        }
    }

    Some(s)
}

/// A closed Reeb orbit.
#[derive(Debug, Clone)]
pub struct ClosedReebOrbit {
    /// Period (= action for Reeb orbits).
    pub period: f64,
    /// Breakpoints p₀, p₁, ..., pₘ with pₘ = p₀.
    pub breakpoints: Vec<Vector4<f64>>,
    /// Facet for each segment: segment k flows along facet[k].
    pub segment_facets: Vec<usize>,
    /// Time spent on each segment.
    pub segment_times: Vec<f64>,
}

impl ClosedReebOrbit {
    /// Validate the orbit.
    ///
    /// Allows zero-length segments (τ_k = 0) as long as:
    /// - Total period T > 0 (non-trivial orbit)
    /// - Zero-length segments have zero displacement (b_{k+1} = b_k)
    pub fn validate(&self, data: &PolytopeData) -> TubeResult<()> {
        // 0. Period must be positive (rules out trivial orbit)
        if self.period <= EPS {
            return Err(TubeError::ValidationFailed(format!(
                "Period must be positive: T = {:.2e}",
                self.period
            )));
        }

        // 1. Closure
        let n = self.breakpoints.len();
        if n < 2 {
            return Err(TubeError::ValidationFailed("Too few breakpoints".to_string()));
        }

        let closure_error = (&self.breakpoints[n - 1] - &self.breakpoints[0]).norm();
        if closure_error > EPS {
            return Err(TubeError::ValidationFailed(format!(
                "Orbit not closed: error = {:.2e}",
                closure_error
            )));
        }

        // 2. Segments lie on claimed facets
        for k in 0..self.segment_facets.len() {
            let i = self.segment_facets[k];
            let p_start = &self.breakpoints[k];
            let p_end = &self.breakpoints[k + 1];
            let n_i = data.normal(i);
            let h_i = data.height(i);

            let start_error = (n_i.dot(p_start) - h_i).abs();
            let end_error = (n_i.dot(p_end) - h_i).abs();

            if start_error > EPS {
                return Err(TubeError::ValidationFailed(format!(
                    "Segment {} start not on facet {}: error = {:.2e}",
                    k, i, start_error
                )));
            }
            if end_error > EPS {
                return Err(TubeError::ValidationFailed(format!(
                    "Segment {} end not on facet {}: error = {:.2e}",
                    k, i, end_error
                )));
            }
        }

        // 3. Velocities match Reeb vectors (skip zero-length segments)
        for k in 0..self.segment_facets.len() {
            let time = self.segment_times[k];

            // Zero-length segment: just verify displacement is also zero
            if time < EPS {
                let displacement = (&self.breakpoints[k + 1] - &self.breakpoints[k]).norm();
                if displacement > EPS {
                    return Err(TubeError::ValidationFailed(format!(
                        "Segment {} has zero time but non-zero displacement: d = {:.2e}",
                        k, displacement
                    )));
                }
                continue; // Skip velocity check (would divide by zero)
            }

            let i = self.segment_facets[k];
            let displacement = &self.breakpoints[k + 1] - &self.breakpoints[k];
            let velocity = displacement / time;
            let reeb = data.reeb(i);

            let velocity_error = (velocity - reeb).norm();
            if velocity_error > EPS * reeb.norm() {
                return Err(TubeError::ValidationFailed(format!(
                    "Segment {} velocity mismatch: error = {:.2e}",
                    k, velocity_error
                )));
            }
        }

        // 4. Period = sum of times
        let time_sum: f64 = self.segment_times.iter().sum();
        if (self.period - time_sum).abs() > EPS {
            return Err(TubeError::ValidationFailed(format!(
                "Period mismatch: period = {}, sum = {}",
                self.period, time_sum
            )));
        }

        // 5. Period = action
        let action = action_of_closed_polygon(&self.breakpoints);
        if (self.period - action).abs() > EPS * self.period {
            return Err(TubeError::ValidationFailed(format!(
                "Action mismatch: period = {}, action = {}",
                self.period, action
            )));
        }

        Ok(())
    }
}

/// Reconstruct a 4D orbit from a 2D fixed point.
pub fn reconstruct_orbit(
    fixed_point_2d: &Vector2<f64>,
    tube: &Tube,
    data: &PolytopeData,
) -> TubeResult<ClosedReebOrbit> {
    let seq = &tube.facet_sequence;
    let n_segments = seq.len() - 2; // Number of facet segments

    // Get start 2-face
    let start_2face = data.get_two_face_enriched(seq[0], seq[1]).ok_or_else(|| {
        TubeError::NumericalInstability {
            message: "Cannot get start 2-face".to_string(),
            facet_sequence: Some(seq.clone()),
        }
    })?;

    // Convert 2D fixed point to 4D
    let start_4d = untrivialize_point(
        fixed_point_2d,
        &start_2face.basis_exit,
        &start_2face.centroid_4d,
    );

    // Trace through each facet
    let mut breakpoints = vec![start_4d];
    let mut current_4d = start_4d;
    let mut segment_times = Vec::new();
    let mut segment_facets = Vec::new();

    for k in 0..n_segments {
        let facet = seq[k + 1]; // Flow along this facet
        let next_facet = seq[k + 2]; // Exit to this facet

        let reeb = data.reeb(facet);
        let n_next = data.normal(next_facet);
        let h_next = data.height(next_facet);

        // Compute time to exit
        let r_dot_n = reeb.dot(n_next);
        if r_dot_n.abs() < EPS {
            return Err(TubeError::NumericalInstability {
                message: format!("Degenerate flow at segment {}", k),
                facet_sequence: Some(seq.clone()),
            });
        }

        let time = (h_next - current_4d.dot(n_next)) / r_dot_n;
        if time < -EPS {
            return Err(TubeError::ValidationFailed(format!(
                "Negative time at segment {}: t = {}",
                k, time
            )));
        }

        // Flow to exit
        let exit_4d = current_4d + *reeb * time;

        breakpoints.push(exit_4d);
        // Clamp small negatives to zero. Zero-length segments (τ_k = 0) are
        // mathematically valid as long as total period T > 0. The HK formula
        // uses β_i ≥ 0 (non-strict), and zero-length segments contribute
        // nothing to the action.
        segment_times.push(time.max(0.0));
        segment_facets.push(facet);

        current_4d = exit_4d;
    }

    let period: f64 = segment_times.iter().sum();

    // Total period must be positive (rules out trivial orbit)
    if period <= EPS {
        return Err(TubeError::ValidationFailed(format!(
            "Reconstructed orbit has zero period: T = {:.2e}",
            period
        )));
    }

    Ok(ClosedReebOrbit {
        period,
        breakpoints,
        segment_facets,
        segment_times,
    })
}

/// Result of the tube algorithm.
#[derive(Debug)]
pub struct TubeResult2 {
    /// The computed capacity.
    pub capacity: f64,
    /// The minimum-action orbit (if found).
    pub orbit: Option<ClosedReebOrbit>,
    /// Number of tubes explored.
    pub tubes_explored: usize,
    /// Number of closed orbits found.
    pub orbits_found: usize,
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    #[test]
    fn test_tube_root_properties() {
        // Create a simple enriched 2-face (mock)
        let polygon = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);

        let root = Tube {
            facet_sequence: vec![0, 1],
            p_start: polygon.clone(),
            p_end: polygon.clone(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
        };

        assert!(root.is_initial());
        assert!(!root.is_closed());
        assert!(!root.is_next_step_closeable());
        assert_relative_eq!(root.rotation, 0.0, epsilon = 1e-14);
        assert_relative_eq!(root.action_lower_bound(), 0.0, epsilon = 1e-14);
    }

    #[test]
    fn test_tube_closed_detection() {
        let polygon = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(0.5, 1.0),
        ]);

        // Length 5 closed tube: [0, 1, 2, 0, 1]
        // Start 2-face is (0, 1), end 2-face is (0, 1)
        let closed_tube = Tube {
            facet_sequence: vec![0, 1, 2, 0, 1],
            p_start: polygon.clone(),
            p_end: polygon.clone(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 1.5,
        };

        assert!(closed_tube.is_closed());

        // A closeable tube: [0, 1, 2, 0]
        // Start 2-face is (0, 1), current 2-face is (2, 0)
        // If we extend with 1, we get [0, 1, 2, 0, 1] which closes
        let closeable_tube = Tube {
            facet_sequence: vec![0, 1, 2, 0],
            p_start: polygon.clone(),
            p_end: polygon.clone(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 1.0,
        };

        assert!(!closeable_tube.is_closed()); // Not yet closed
        assert!(closeable_tube.is_next_step_closeable()); // Would close if extended with [1]
    }

    #[test]
    fn test_find_closed_orbits_identity() {
        // Identity flow map: every point is a fixed point (parabolic case with zero matrix)
        let polygon = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(0.5, 1.0),
        ]);

        let tube = Tube {
            facet_sequence: vec![0, 1, 2, 0, 1],
            p_start: polygon.clone(),
            p_end: polygon.clone(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 1.5,
        };

        // Identity map has A - I = 0, b = 0, so all points are fixed
        // Should find some fixed points (parabolic case)
        let result = find_closed_orbits(&tube);
        assert!(result.is_ok());
        let orbits = result.unwrap();
        // Should find at least one fixed point
        assert!(!orbits.is_empty());
    }

    #[test]
    fn test_find_closed_orbits_parabolic_shear() {
        // Shear flow map: [[1, k], [0, 1]] with k ≠ 0
        // Fixed points satisfy: (A - I)s = -b
        // A - I = [[0, k], [0, 0]], so s[1] = -b[1] / k (constraint on y)
        // For b = (0, 0), all points with any y satisfy the constraint
        // For b = (-1, 0), fixed points have y = 0
        let polygon = Polygon2D::new(vec![
            Vector2::new(-1.0, -1.0),
            Vector2::new(1.0, -1.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(-1.0, 1.0),
        ]);

        let k = 4.0;
        let tube = Tube {
            facet_sequence: vec![0, 1, 2, 0, 1],
            p_start: polygon.clone(),
            p_end: polygon.clone(),
            // Shear matrix
            flow_map: AffineMap2D::new(
                Matrix2::new(1.0, k, 0.0, 1.0),
                Vector2::new(0.0, 0.0), // b = 0
            ),
            action_func: AffineFunc {
                gradient: Vector2::new(1.0, 0.0), // Action = x
                constant: 0.0,
            },
            rotation: 1.5,
        };

        // A - I = [[0, 4], [0, 0]], kernel = (1, 0)
        // (A - I)s = 0 requires 4*s[1] = 0, so s[1] = 0
        // Fixed point line: y = 0, any x
        let orbits = find_closed_orbits(&tube).unwrap();
        assert!(!orbits.is_empty(), "Should find parabolic fixed points");

        // All fixed points should have y ≈ 0
        for (_, fp) in &orbits {
            assert!(fp[1].abs() < 1e-10, "Fixed point y should be 0, got {}", fp[1]);
        }

        // The minimum action should be at x = -1 (left edge of polygon)
        let (min_action, _) = orbits.iter().min_by(|a, b| a.0.partial_cmp(&b.0).unwrap()).unwrap();
        assert_relative_eq!(*min_action, -1.0, epsilon = 1e-10);
    }

    #[test]
    fn test_find_closed_orbits_unique() {
        let polygon = Polygon2D::new(vec![
            Vector2::new(-1.0, -1.0),
            Vector2::new(1.0, -1.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(-1.0, 1.0),
        ]);

        // Flow map with unique fixed point at (0.5, 0.5)
        // A*s + b = s => (A - I)*s = -b
        // Let A - I = [[0.5, 0], [0, 0.5]], so s = -2*b
        // b = (-0.25, -0.25) => s = (0.5, 0.5)
        let tube = Tube {
            facet_sequence: vec![0, 1, 2, 0, 1],
            p_start: polygon.clone(),
            p_end: polygon.clone(),
            flow_map: AffineMap2D::new(
                Matrix2::new(1.5, 0.0, 0.0, 1.5),
                Vector2::new(-0.25, -0.25),
            ),
            action_func: AffineFunc {
                gradient: Vector2::new(1.0, 1.0),
                constant: 0.0,
            },
            rotation: 1.5,
        };

        let orbits = find_closed_orbits(&tube).unwrap();
        assert_eq!(orbits.len(), 1);

        let (action, fixed_point) = &orbits[0];
        assert_relative_eq!(fixed_point[0], 0.5, epsilon = 1e-10);
        assert_relative_eq!(fixed_point[1], 0.5, epsilon = 1e-10);
        assert_relative_eq!(*action, 1.0, epsilon = 1e-10); // 1*0.5 + 1*0.5
    }
}
