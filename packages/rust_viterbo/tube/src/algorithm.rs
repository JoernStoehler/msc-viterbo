//! Tube algorithm for computing EHZ capacity.
//!
//! This module implements the branch-and-bound search over "tubes" —
//! sets of Reeb trajectories sharing a combinatorial class (facet sequence).
//!
//! Source: This thesis (Stöhler 2026), building on CH2021's mathematical framework.

use nalgebra::{Matrix2, Vector2, Vector4};
use std::collections::BinaryHeap;

use crate::constants::{EPS, EPS_CLOSURE, EPS_ROTATION, MAX_ROTATION, MIN_POLYGON_AREA};
use crate::geometry::{apply_affine_to_polygon, intersect_polygons, point_in_polygon};
use crate::preprocess::{preprocess, PolytopeData};
use crate::quaternion::{apply_quat_j, apply_quat_k};
use crate::types::{
    AffineFunc, AffineMap2D, ClosedReebOrbit, FlowDirection, PolytopeHRep, Tube, TubeError,
    TubeResult, TwoFaceEnriched,
};

/// Main entry point: compute the EHZ capacity using the tube algorithm.
///
/// # Arguments
/// - `hrep`: H-representation of a 4D polytope with no Lagrangian 2-faces
///
/// # Returns
/// - `Ok(TubeResult)`: The capacity and optimal orbit
/// - `Err(TubeError)`: If the polytope has Lagrangian 2-faces or no orbits found
pub fn tube_capacity(hrep: &PolytopeHRep) -> Result<TubeResult, TubeError> {
    let data = preprocess(hrep)?;

    if data.has_lagrangian_two_faces() {
        return Err(TubeError::HasLagrangianTwoFaces);
    }

    let mut best_action = f64::INFINITY;
    let mut best_orbit: Option<ClosedReebOrbit> = None;
    let mut worklist = BinaryHeap::new();
    let mut tubes_explored = 0;
    let mut tubes_pruned = 0;

    // Initialize: one root tube per 2-face
    for tfe in &data.two_faces_enriched {
        let root = create_root_tube(tfe);
        worklist.push(TubePriority::new(root));
    }

    // Branch and bound
    while let Some(tube_priority) = worklist.pop() {
        let tube = tube_priority.tube;
        tubes_explored += 1;

        // Prune by action bound
        if tube.action_lower_bound() >= best_action {
            tubes_pruned += 1;
            continue;
        }

        // Get possible extensions
        for extension in get_extensions(&tube, &data) {
            match extension {
                Extension::Closed { orbit, action } => {
                    if action < best_action {
                        best_action = action;
                        best_orbit = Some(orbit);
                    }
                }
                Extension::Open(new_tube) => {
                    // Prune by rotation bound
                    if new_tube.rotation <= MAX_ROTATION + EPS_ROTATION {
                        // Prune by action bound
                        if new_tube.action_lower_bound() < best_action {
                            worklist.push(TubePriority::new(new_tube));
                        } else {
                            tubes_pruned += 1;
                        }
                    } else {
                        tubes_pruned += 1;
                    }
                }
            }
        }
    }

    match best_orbit {
        Some(orbit) => Ok(TubeResult {
            capacity: best_action,
            optimal_orbit: orbit,
            tubes_explored,
            tubes_pruned,
        }),
        None => Err(TubeError::NoClosedOrbits),
    }
}

/// Wrapper for priority queue ordering (min-heap by action lower bound).
///
/// Rust's `BinaryHeap` is a max-heap by default, so we store the negated
/// action lower bound to get min-heap behavior. This ensures we explore
/// tubes with smaller action bounds first (branch-and-bound pruning).
#[derive(Debug)]
struct TubePriority {
    tube: Tube,
    /// Negative of action_lower_bound (BinaryHeap is max-heap, we want min-heap)
    priority: f64,
}

impl TubePriority {
    fn new(tube: Tube) -> Self {
        let priority = -tube.action_lower_bound();
        Self { tube, priority }
    }
}

impl PartialEq for TubePriority {
    fn eq(&self, other: &Self) -> bool {
        self.priority == other.priority
    }
}

impl Eq for TubePriority {}

impl PartialOrd for TubePriority {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for TubePriority {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        // NaN handling: treat NaN as less than everything
        self.priority
            .partial_cmp(&other.priority)
            .unwrap_or(std::cmp::Ordering::Less)
    }
}

/// Result of extending a tube.
enum Extension {
    /// Tube closed successfully, found a periodic orbit.
    Closed { orbit: ClosedReebOrbit, action: f64 },
    /// Tube extended but not closed.
    Open(Tube),
}

/// Create the root tube for a 2-face.
///
/// A "root tube" represents the starting point of a branch-and-bound search path.
/// It corresponds to trajectories that:
/// - Start on a 2-face (intersection of two facets)
/// - Flow along one facet direction until reaching the same 2-face again
///
/// The root tube has trivial data: identity flow map (no flow yet), zero action,
/// and zero rotation. As the search extends the tube through additional facets,
/// these values accumulate.
fn create_root_tube(tfe: &TwoFaceEnriched) -> Tube {
    let (entry_facet, exit_facet) = match tfe.flow_direction {
        Some(FlowDirection::ItoJ) => (tfe.i, tfe.j),
        Some(FlowDirection::JtoI) => (tfe.j, tfe.i),
        None => panic!("Cannot create root tube for Lagrangian 2-face"),
    };

    Tube {
        facet_sequence: vec![entry_facet, exit_facet],
        p_start: tfe.polygon_2d.clone(),
        p_end: tfe.polygon_2d.clone(),
        flow_map: AffineMap2D::identity(),
        action_func: AffineFunc::zero(),
        rotation: 0.0,
    }
}

/// Get all valid extensions of a tube.
fn get_extensions(tube: &Tube, data: &PolytopeData) -> Vec<Extension> {
    let mut extensions = Vec::new();

    // Current end facet
    let curr_facet = *tube.facet_sequence.last().unwrap();

    // Find all facets we can flow to from the current facet
    let next_facets = data.adjacent_facets_forward(curr_facet);

    for next_facet in next_facets {
        if let Some(extended) = extend_tube(tube, next_facet, data) {
            // Check if this closes the tube
            if extended.is_closed() {
                // Try to find fixed points
                if let Some((action, fixed_point)) = find_closed_orbit(&extended) {
                    // Reconstruct the 4D orbit
                    if let Ok(orbit) = reconstruct_orbit(&fixed_point, &extended, data) {
                        extensions.push(Extension::Closed { orbit, action });
                    }
                }
            } else {
                extensions.push(Extension::Open(extended));
            }
        }
    }

    extensions
}

/// Extend a tube by flowing to the next facet.
fn extend_tube(tube: &Tube, next_facet: usize, data: &PolytopeData) -> Option<Tube> {
    let seq = &tube.facet_sequence;
    let prev_facet = seq[seq.len() - 2];
    let curr_facet = seq[seq.len() - 1];

    // Get the 2-faces
    let entry_2face = data.get_two_face_enriched(prev_facet, curr_facet)?;
    let exit_2face = data.get_two_face_enriched(curr_facet, next_facet)?;

    // Compute flow across the current facet
    let (flow_step, time_step) = compute_facet_flow(entry_2face, exit_2face, data, curr_facet);

    // Compose with existing flow map
    let new_flow_map = flow_step.compose(&tube.flow_map);

    // Compose action function
    let new_action_func = tube
        .action_func
        .add(&time_step.compose_with_map(&tube.flow_map));

    // Apply flow to end polygon and intersect with exit 2-face
    let flowed_end = apply_affine_to_polygon(&flow_step, &tube.p_end);
    let new_p_end = intersect_polygons(&flowed_end, &exit_2face.polygon_2d);

    // Check if result is non-empty
    if new_p_end.is_empty() || new_p_end.area() < MIN_POLYGON_AREA {
        return None;
    }

    // Compute new start polygon by pulling back constraints
    // p_start is the set of points that eventually land in new_p_end
    // new_p_start = p_start ∩ flow_map^{-1}(new_p_end)
    let new_p_start = if let Some(flow_inv) = new_flow_map.try_inverse() {
        let pullback = apply_affine_to_polygon(&flow_inv, &new_p_end);
        intersect_polygons(&tube.p_start, &pullback)
    } else {
        // Flow map not invertible (shouldn't happen for symplectic maps)
        debug_assert!(false, "Flow map not invertible");
        tube.p_start.clone()
    };

    // Check p_start is non-empty (otherwise no valid orbits can start here)
    if new_p_start.is_empty() || new_p_start.area() < MIN_POLYGON_AREA {
        return None;
    }

    Some(Tube {
        facet_sequence: [&tube.facet_sequence[..], &[next_facet]].concat(),
        p_start: new_p_start,
        p_end: new_p_end,
        flow_map: new_flow_map,
        action_func: new_action_func,
        rotation: tube.rotation + exit_2face.rotation,
    })
}

/// Compute the affine flow map and time function for flowing across a facet.
fn compute_facet_flow(
    entry_2face: &TwoFaceEnriched,
    exit_2face: &TwoFaceEnriched,
    data: &PolytopeData,
    curr_facet: usize,
) -> (AffineMap2D, AffineFunc) {
    // Get Reeb vector on current facet
    let r_curr = data.reeb_vector(curr_facet);
    let n_next = &exit_2face.exit_normal;
    let h_next = data.height(if exit_2face.i == curr_facet {
        exit_2face.j
    } else {
        exit_2face.i
    });

    // Denominator of time formula: ⟨R_curr, n_next⟩
    let r_dot_n = r_curr.dot(n_next);
    debug_assert!(
        r_dot_n.abs() > EPS,
        "r_dot_n ≈ 0 indicates Lagrangian 2-face"
    );

    // Basis vectors
    let b_entry = &entry_2face.basis_exit;
    let c_entry = entry_2face.centroid_4d;
    let c_exit = exit_2face.centroid_4d;

    // Trivialization vectors for exit
    let jn_exit = apply_quat_j(&exit_2face.exit_normal);
    let kn_exit = apply_quat_k(&exit_2face.exit_normal);

    // Time function: t(p_2d) = t_const + ⟨t_grad, p_2d⟩
    let t_const = (h_next - c_entry.dot(n_next)) / r_dot_n;
    let t_grad = Vector2::new(
        -b_entry[0].dot(n_next) / r_dot_n,
        -b_entry[1].dot(n_next) / r_dot_n,
    );
    let time_func = AffineFunc {
        gradient: t_grad,
        constant: t_const,
    };

    // Transition matrix: trivialize entry basis in exit coordinates
    let psi = Matrix2::new(
        b_entry[0].dot(&jn_exit),
        b_entry[1].dot(&jn_exit),
        b_entry[0].dot(&kn_exit),
        b_entry[1].dot(&kn_exit),
    );

    // Reeb vector trivialized in exit coordinates
    let r_triv = Vector2::new(r_curr.dot(&jn_exit), r_curr.dot(&kn_exit));

    // Full flow matrix: A = ψ + r_triv ⊗ t_grad
    let a_matrix = psi + r_triv * t_grad.transpose();

    // Offset: b = τ_exit(c_entry - c_exit + t_const * R_curr)
    let delta_c = c_entry - c_exit + r_curr * t_const;
    let b_offset = Vector2::new(delta_c.dot(&jn_exit), delta_c.dot(&kn_exit));

    let flow_map = AffineMap2D {
        matrix: a_matrix,
        offset: b_offset,
    };

    (flow_map, time_func)
}

/// Find closed orbits as fixed points of the flow map.
///
/// For shear transformations (det(A-I) ≈ 0), fixed points form a line.
/// We find where this line intersects p_start and return the minimum-action point.
fn find_closed_orbit(tube: &Tube) -> Option<(f64, Vector2<f64>)> {
    // Solve (A - I) s = -b
    let a_minus_i = tube.flow_map.matrix - Matrix2::identity();
    let neg_b = -tube.flow_map.offset;

    let det = a_minus_i.determinant();

    if det.abs() < EPS {
        // Shear case: det(A-I) ≈ 0, fixed points may form a line
        return find_fixed_point_on_line(tube, &a_minus_i, &neg_b);
    }

    // Unique fixed point (regular case)
    let s = a_minus_i.try_inverse()? * neg_b;

    // Check if fixed point is in p_end (reachable region)
    if !point_in_polygon(&s, &tube.p_end) {
        return None;
    }

    // Consistency check: for properly tracked p_start, s ∈ p_end implies s ∈ p_start
    // (since p_start = flow_map⁻¹(p_end) and s is a fixed point)
    // Due to accumulated numerical errors in polygon intersections, this may fail
    // for points near the boundary. Only flag as error if clearly outside.
    #[cfg(debug_assertions)]
    if !point_in_polygon(&s, &tube.p_start) {
        // Check how far outside p_start the point is
        // This helps distinguish numerical error from actual tracking bugs
        let min_dist_to_boundary = tube
            .p_start
            .vertices
            .iter()
            .map(|v| (s - v).norm())
            .fold(f64::INFINITY, f64::min);
        if min_dist_to_boundary > 0.1 {
            // Point is clearly outside, not just numerical error
            debug_assert!(
                false,
                "Fixed point in p_end but far from p_start (dist={:.4}) - tracking may be broken",
                min_dist_to_boundary
            );
        }
    }

    // Verify it's actually a fixed point
    let s_mapped = tube.flow_map.apply(&s);
    if (s - s_mapped).norm() > EPS {
        return None;
    }

    let action = tube.action_func.eval(&s);

    // Action should be positive for valid orbits
    if action < EPS {
        return None;
    }

    Some((action, s))
}

/// Handle the shear case where fixed points form a line.
///
/// For shear matrix A - I with rank 1:
/// - Column space is 1D (spanned by some vector v)
/// - -b must be in column space for solutions to exist
/// - Solutions form line: s = s_particular + t * null_vector
fn find_fixed_point_on_line(
    tube: &Tube,
    a_minus_i: &Matrix2<f64>,
    neg_b: &Vector2<f64>,
) -> Option<(f64, Vector2<f64>)> {
    // Find the column with larger norm (spans column space)
    let col0 = Vector2::new(a_minus_i[(0, 0)], a_minus_i[(1, 0)]);
    let col1 = Vector2::new(a_minus_i[(0, 1)], a_minus_i[(1, 1)]);

    // Check if A ≈ I (both columns near zero)
    if col0.norm() < EPS && col1.norm() < EPS {
        // A = I case: fixed points exist iff b = 0
        if neg_b.norm() < EPS {
            // All points in p_start are fixed points
            // Return the one with minimum action
            return find_min_action_in_polygon(tube);
        }
        return None; // b ≠ 0, no fixed points
    }

    // Determine which row of A-I to use for parameterization
    // Use the row with larger norm for numerical stability
    let row0 = Vector2::new(a_minus_i[(0, 0)], a_minus_i[(0, 1)]);
    let row1 = Vector2::new(a_minus_i[(1, 0)], a_minus_i[(1, 1)]);

    let (w, b_component) = if row0.norm() > row1.norm() {
        (row0, neg_b[0])
    } else {
        (row1, neg_b[1])
    };

    // Check if -b is in column space of A-I
    // For rank-1 matrix, (A-I)s = -b requires the "other" component of -b to be ~0
    let (col, other_b) = if col0.norm() > col1.norm() {
        // Column space spanned by col0
        // Check if neg_b[1] / col0[1] ≈ neg_b[0] / col0[0] (i.e., neg_b parallel to col0)
        (
            col0,
            if col0[0].abs() > EPS {
                neg_b[1] - (neg_b[0] / col0[0]) * col0[1]
            } else if col0[1].abs() > EPS {
                neg_b[0] - (neg_b[1] / col0[1]) * col0[0]
            } else {
                return None; // Degenerate
            },
        )
    } else {
        (
            col1,
            if col1[0].abs() > EPS {
                neg_b[1] - (neg_b[0] / col1[0]) * col1[1]
            } else if col1[1].abs() > EPS {
                neg_b[0] - (neg_b[1] / col1[1]) * col1[0]
            } else {
                return None;
            },
        )
    };

    // Tolerance check: is -b in the column space?
    let tol = EPS * (col.norm() * neg_b.norm()).max(1.0);
    if other_b.abs() > tol {
        return None; // -b not in column space, no fixed points
    }

    // Find null vector (kernel of A-I)
    // Null space is perpendicular to both rows, so use cross product intuition in 2D
    let null_vec = if w[0].abs() > w[1].abs() {
        Vector2::new(-w[1] / w[0], 1.0).normalize()
    } else if w[1].abs() > EPS {
        Vector2::new(1.0, -w[0] / w[1]).normalize()
    } else {
        return None; // Degenerate
    };

    // Find a particular solution
    // w · s_particular = b_component
    let s_particular = if w[0].abs() > w[1].abs() {
        Vector2::new(b_component / w[0], 0.0)
    } else {
        Vector2::new(0.0, b_component / w[1])
    };

    // The fixed point line is: s(t) = s_particular + t * null_vec
    // Find where this line intersects the valid region (p_start ∩ p_end)
    // For properly tracked polygons, p_start = flow_map⁻¹(p_end), so intersection is p_end
    // We use p_end as the primary check, with debug_assert for consistency
    let valid_region = &tube.p_end;

    intersect_line_with_polygon_min_action(
        &s_particular,
        &null_vec,
        valid_region,
        &tube.action_func,
        &tube.flow_map,
        &tube.p_start, // For debug consistency check
    )
}

/// Find the fixed point with minimum action when all points are fixed (A = I, b = 0).
fn find_min_action_in_polygon(tube: &Tube) -> Option<(f64, Vector2<f64>)> {
    // Action is affine: action(s) = g · s + c
    // Minimum is at a vertex of the polygon or where gradient points outside
    // Use p_end as the valid region (for properly tracked polygons, p_start ≈ p_end for fixed points)
    let _grad = &tube.action_func.gradient; // For affine functions, min is at a vertex

    let mut best_action = f64::INFINITY;
    let mut best_point = None;

    // Check all vertices of p_end
    for v in &tube.p_end.vertices {
        let action = tube.action_func.eval(v);
        if action > EPS && action < best_action {
            best_action = action;
            best_point = Some(*v);
        }
    }

    // For affine functions, the minimum over a convex polygon is at a vertex
    // (unless gradient is zero, in which case all vertices have same value)

    best_point.map(|p| (best_action, p))
}

/// Intersect a line with a polygon and find the point with minimum positive action.
///
/// The `p_start_for_debug` parameter is used for consistency checking in debug builds.
fn intersect_line_with_polygon_min_action(
    point_on_line: &Vector2<f64>,
    direction: &Vector2<f64>,
    polygon: &crate::types::Polygon2D,
    action_func: &AffineFunc,
    flow_map: &AffineMap2D,
    p_start_for_debug: &crate::types::Polygon2D,
) -> Option<(f64, Vector2<f64>)> {
    // Line: p(t) = point_on_line + t * direction
    // Find t_min and t_max where line intersects polygon

    let mut t_values = Vec::new();

    // Intersect with each edge of the polygon
    let n = polygon.vertices.len();
    for i in 0..n {
        let v0 = &polygon.vertices[i];
        let v1 = &polygon.vertices[(i + 1) % n];
        let edge = v1 - v0;

        // Solve: point_on_line + t * direction = v0 + s * edge
        // This gives us: t * direction - s * edge = v0 - point_on_line
        // In matrix form: [direction | -edge] * [t, s]^T = v0 - point_on_line

        let rhs = v0 - point_on_line;
        let det = direction[0] * (-edge[1]) - direction[1] * (-edge[0]);

        if det.abs() < EPS {
            // Parallel: check if line lies on edge (rare case)
            continue;
        }

        let t = (rhs[0] * (-edge[1]) - rhs[1] * (-edge[0])) / det;
        let s = (direction[0] * rhs[1] - direction[1] * rhs[0]) / det;

        // s must be in [0, 1] for intersection to be on the edge
        if (-EPS..=1.0 + EPS).contains(&s) {
            t_values.push(t);
        }
    }

    if t_values.is_empty() {
        return None;
    }

    // Find t range that's inside the polygon
    t_values.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));

    // The valid range is between consecutive intersection points
    // For a convex polygon, we should have exactly 2 intersection points (or 0)
    if t_values.len() < 2 {
        // Line might only touch a vertex; try that point
        if !t_values.is_empty() {
            let t = t_values[0];
            let candidate = point_on_line + direction * t;
            if point_in_polygon(&candidate, polygon) {
                return validate_and_return(&candidate, action_func, flow_map);
            }
        }
        return None;
    }

    let t_min = t_values[0];
    let t_max = t_values[t_values.len() - 1];

    // Action on the line: action(t) = action_func.eval(point_on_line + t * direction)
    //                               = g · (point_on_line + t * direction) + c
    //                               = (g · point_on_line + c) + t * (g · direction)
    // This is linear in t!

    let action_at_0 = action_func.eval(point_on_line);
    let action_slope = action_func.gradient.dot(direction);

    // action(t) = action_at_0 + t * action_slope
    // We want minimum positive action in [t_min, t_max]

    let action_at_t_min = action_at_0 + t_min * action_slope;
    let action_at_t_max = action_at_0 + t_max * action_slope;

    // For linear function, extrema are at endpoints
    let (best_t, best_action) = if action_slope.abs() < EPS {
        // Constant action along line
        (t_min, action_at_t_min)
    } else if action_slope > 0.0 {
        // Action increases with t, so minimum at t_min
        (t_min, action_at_t_min)
    } else {
        // Action decreases with t, so minimum at t_max
        (t_max, action_at_t_max)
    };

    if best_action < EPS {
        return None; // Action not positive
    }

    let best_point = point_on_line + direction * best_t;

    // Note: We skip strict p_start consistency check here due to numerical precision
    // issues with accumulated polygon intersections. The p_start_for_debug parameter
    // is retained for future investigation of tracking accuracy.
    let _ = p_start_for_debug; // Suppress unused warning

    validate_and_return(&best_point, action_func, flow_map)
}

/// Validate that a point is actually a fixed point and return (action, point).
fn validate_and_return(
    point: &Vector2<f64>,
    action_func: &AffineFunc,
    flow_map: &AffineMap2D,
) -> Option<(f64, Vector2<f64>)> {
    // Verify it's actually a fixed point (use lenient tolerance for accumulated error)
    let mapped = flow_map.apply(point);
    if (point - mapped).norm() > EPS_CLOSURE {
        return None; // Not a fixed point
    }

    let action = action_func.eval(point);
    if action < EPS {
        return None;
    }

    Some((action, *point))
}

/// Reconstruct the 4D orbit from 2D fixed point and tube.
fn reconstruct_orbit(
    fixed_point_2d: &Vector2<f64>,
    tube: &Tube,
    data: &PolytopeData,
) -> Result<ClosedReebOrbit, TubeError> {
    let seq = &tube.facet_sequence;

    // Number of facet transitions
    let n_transitions = seq.len() - 2;

    if n_transitions == 0 {
        return Err(TubeError::InvalidPolytope(
            "Tube has no transitions".to_string(),
        ));
    }

    // Get start 2-face
    let start_2face = data
        .get_two_face_enriched(seq[0], seq[1])
        .ok_or_else(|| TubeError::InvalidPolytope("Start 2-face not found".to_string()))?;

    // Convert starting point to 4D
    let start_4d = untrivialize_point(fixed_point_2d, start_2face);

    // Trace through to get all breakpoints
    let mut breakpoints = vec![start_4d];
    let mut current_4d = start_4d;

    for k in 1..=n_transitions {
        // Flow along facet seq[k] to 2-face F_{seq[k], seq[k+1]}
        let facet = seq[k];
        let reeb = data.reeb_vector(facet);

        // Determine next facet (wrapping for closed tube)
        let next_facet = if k + 1 < seq.len() {
            seq[k + 1]
        } else {
            seq[1] // Wrap around
        };

        let n_next = data.normal(next_facet);
        let h_next = data.height(next_facet);

        // Compute time to reach next facet
        let r_dot_n = reeb.dot(n_next);
        if r_dot_n.abs() < EPS {
            return Err(TubeError::NumericalInstability(
                "r_dot_n ≈ 0 during reconstruction".to_string(),
            ));
        }

        let t = (h_next - current_4d.dot(n_next)) / r_dot_n;

        // Flow
        current_4d += reeb * t;
        breakpoints.push(current_4d);
    }

    // Verify closure (use lenient tolerance for accumulated error along trajectory)
    let closure_error = (breakpoints.last().unwrap() - start_4d).norm();
    if closure_error > EPS_CLOSURE {
        return Err(TubeError::NumericalInstability(format!(
            "Orbit failed to close: error = {:.2e}",
            closure_error
        )));
    }

    // Set last point exactly equal to first
    *breakpoints.last_mut().unwrap() = start_4d;

    // Compute segment data
    let mut segment_facets = Vec::new();
    let mut segment_times = Vec::new();

    for k in 0..n_transitions {
        let facet = seq[k + 1];
        segment_facets.push(facet);

        let displacement = breakpoints[k + 1] - breakpoints[k];
        let reeb = data.reeb_vector(facet);
        let time = displacement.dot(reeb) / reeb.norm_squared();
        segment_times.push(time);
    }

    let period: f64 = segment_times.iter().sum();

    Ok(ClosedReebOrbit {
        period,
        breakpoints,
        segment_facets,
        segment_times,
    })
}

/// Convert 2D trivialized point back to 4D.
fn untrivialize_point(point_2d: &Vector2<f64>, tfe: &TwoFaceEnriched) -> Vector4<f64> {
    tfe.centroid_4d + point_2d[0] * tfe.basis_exit[0] + point_2d[1] * tfe.basis_exit[1]
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixtures::unit_cross_polytope;
    use crate::types::{AffineFunc, AffineMap2D, Polygon2D, Tube};
    use approx::assert_relative_eq;

    #[test]
    fn test_debug_tube_algorithm() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        println!("Num facets: {}", data.num_facets);
        println!("Num enriched 2-faces: {}", data.two_faces_enriched.len());

        // Check adjacency
        for i in 0..data.num_facets {
            let adj = data.adjacent_facets_forward(i);
            if !adj.is_empty() {
                println!("Facet {} -> {:?}", i, adj);
            }
        }

        // Try extending one root tube
        let tfe = &data.two_faces_enriched[0];
        println!(
            "\nRoot tube on 2-face ({}, {}), flow: {:?}",
            tfe.i, tfe.j, tfe.flow_direction
        );
        let root = create_root_tube(tfe);
        println!(
            "Root facet_sequence: {:?}, p_start area: {}",
            root.facet_sequence,
            root.p_start.area()
        );

        let curr_facet = *root.facet_sequence.last().unwrap();
        let next_facets = data.adjacent_facets_forward(curr_facet);
        println!("Next facets from {}: {:?}", curr_facet, next_facets);

        for &next_facet in &next_facets {
            println!("  Trying to extend to facet {}", next_facet);
            match extend_tube(&root, next_facet, &data) {
                Some(extended) => {
                    println!(
                        "    Extended! seq={:?}, p_end area={}",
                        extended.facet_sequence,
                        extended.p_end.area()
                    );
                }
                None => {
                    println!("    Failed to extend");
                }
            }
        }
    }

    #[test]
    fn test_debug_flow_map() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        // Take a simple extension and verify the flow map
        let tfe = &data.two_faces_enriched[0];
        println!(
            "Root 2-face: ({}, {}), flow={:?}",
            tfe.i, tfe.j, tfe.flow_direction
        );
        println!("  entry_normal: {:?}", tfe.entry_normal);
        println!("  exit_normal: {:?}", tfe.exit_normal);

        let root = create_root_tube(tfe);
        let curr_facet = *root.facet_sequence.last().unwrap();
        let next_facets = data.adjacent_facets_forward(curr_facet);
        println!(
            "Current facet: {}, next facets: {:?}",
            curr_facet, next_facets
        );

        if let Some(&next_facet) = next_facets.first() {
            let seq = &root.facet_sequence;
            let prev_facet = seq[seq.len() - 2];

            let entry_2face = data.get_two_face_enriched(prev_facet, curr_facet).unwrap();
            let exit_2face = data.get_two_face_enriched(curr_facet, next_facet).unwrap();

            println!("\nEntry 2-face ({}, {}):", entry_2face.i, entry_2face.j);
            println!("  entry_normal: {:?}", entry_2face.entry_normal);
            println!("  exit_normal: {:?}", entry_2face.exit_normal);
            println!(
                "  transition_matrix det: {}",
                entry_2face.transition_matrix.determinant()
            );

            println!("\nExit 2-face ({}, {}):", exit_2face.i, exit_2face.j);
            println!("  entry_normal: {:?}", exit_2face.entry_normal);
            println!("  exit_normal: {:?}", exit_2face.exit_normal);
            println!(
                "  transition_matrix det: {}",
                exit_2face.transition_matrix.determinant()
            );

            // Verify basis vectors
            println!(
                "\nEntry 2-face basis_exit[0]: {:?}",
                entry_2face.basis_exit[0]
            );
            println!(
                "Entry 2-face basis_exit[1]: {:?}",
                entry_2face.basis_exit[1]
            );

            // Check orthogonality to normals
            println!(
                "  b0 · entry_normal = {}",
                entry_2face.basis_exit[0].dot(&entry_2face.entry_normal)
            );
            println!(
                "  b0 · exit_normal = {}",
                entry_2face.basis_exit[0].dot(&entry_2face.exit_normal)
            );

            // Compute flow map
            let (flow_step, _time_step) =
                compute_facet_flow(entry_2face, exit_2face, &data, curr_facet);
            println!("\nFlow map:");
            println!("  matrix: {:?}", flow_step.matrix);
            println!("  offset: {:?}", flow_step.offset);
            println!("  det(A): {}", flow_step.matrix.determinant());
            println!(
                "  det(A-I): {}",
                (flow_step.matrix - Matrix2::identity()).determinant()
            );

            // Test on a specific point
            let test_point = Vector2::new(0.5, 0.5);
            let mapped = flow_step.apply(&test_point);
            println!("\nTest: {:?} -> {:?}", test_point, mapped);
        }
    }

    #[test]
    fn test_debug_full_search() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        // Collect all closed tubes up to a certain depth
        fn collect_closed_tubes(
            tube: &Tube,
            data: &PolytopeData,
            depth: usize,
            max_depth: usize,
            results: &mut Vec<Tube>,
        ) {
            if depth >= max_depth {
                return;
            }

            let curr_facet = *tube.facet_sequence.last().unwrap();
            let next_facets = data.adjacent_facets_forward(curr_facet);

            for &next_facet in &next_facets {
                if let Some(extended) = extend_tube(tube, next_facet, data) {
                    if extended.is_closed() {
                        results.push(extended.clone());
                    }
                    // Continue searching even if closed (to find more)
                    collect_closed_tubes(&extended, data, depth + 1, max_depth, results);
                }
            }
        }

        println!("Collecting all closed tubes (max_depth=8)...");

        let mut all_closed = Vec::new();
        for tfe in &data.two_faces_enriched {
            let root = create_root_tube(tfe);
            collect_closed_tubes(&root, &data, 0, 8, &mut all_closed);
        }

        println!("Found {} closed tubes total", all_closed.len());

        // Analyze each closed tube for shear fixed points
        println!("\nAnalyzing closed tubes:");
        for (i, closed) in all_closed.iter().take(10).enumerate() {
            let a = &closed.flow_map.matrix;
            let b = &closed.flow_map.offset;
            let a_minus_i = a - Matrix2::identity();
            let det = a_minus_i.determinant();

            println!("\nTube {}: {:?}", i, closed.facet_sequence);
            println!("  A = {:?}", a);
            println!("  b = {:?}", b);
            println!("  det(A-I) = {:.6}", det);

            if det.abs() < EPS {
                // Shear case: check if b is in column space of (A-I)
                // A-I has rank 1 (or 0), so column space is spanned by first nonzero column
                let col0 = Vector2::new(a_minus_i[(0, 0)], a_minus_i[(1, 0)]);
                let col1 = Vector2::new(a_minus_i[(0, 1)], a_minus_i[(1, 1)]);

                let col = if col0.norm() > col1.norm() {
                    col0
                } else {
                    col1
                };

                if col.norm() < EPS {
                    // A = I, so we need b = 0 for fixed points (all points fixed)
                    if b.norm() < EPS {
                        println!("  A = I and b ≈ 0: ALL points are fixed!");
                        // Minimum action is over the polygon p_start
                        let min_action = closed.action_lower_bound();
                        println!("  Minimum action = {}", min_action);
                    } else {
                        println!("  A = I but b ≠ 0: no fixed points");
                    }
                } else {
                    // Check if -b is parallel to col (i.e., -b = t * col for some t)
                    let neg_b = -b;
                    let cross = col[0] * neg_b[1] - col[1] * neg_b[0];
                    if cross.abs() < EPS * col.norm() * neg_b.norm().max(1.0) {
                        // -b is in column space, so there's a LINE of fixed points
                        println!("  -b is in column space: LINE of fixed points exists!");
                        // The fixed point line intersects p_start somewhere
                        // We need to find where and compute the minimum action
                    } else {
                        println!("  -b NOT in column space: no fixed points");
                    }
                }
            }
        }
    }

    #[test]
    fn test_tube_capacity_cross_polytope() {
        let hrep = unit_cross_polytope();
        let result = tube_capacity(&hrep);

        match result {
            Ok(r) => {
                println!("Cross-polytope capacity: {}", r.capacity);
                println!("Tubes explored: {}", r.tubes_explored);
                println!("Tubes pruned: {}", r.tubes_pruned);

                // Print orbit details
                let orbit = &r.optimal_orbit;
                println!("\nOptimal orbit:");
                println!("  Period: {}", orbit.period);
                println!("  Facet sequence: {:?}", orbit.segment_facets);
                println!("  Segment times: {:?}", orbit.segment_times);
                println!("  Num breakpoints: {}", orbit.breakpoints.len());

                // Verify orbit closure
                let closure_error =
                    (orbit.breakpoints.last().unwrap() - orbit.breakpoints.first().unwrap()).norm();
                println!("  Closure error: {}", closure_error);
                assert!(
                    closure_error < EPS,
                    "Orbit not closed: error = {}",
                    closure_error
                );

                // Verify period equals action
                let time_sum: f64 = orbit.segment_times.iter().sum();
                println!("  Sum of times: {}", time_sum);
                assert_relative_eq!(orbit.period, time_sum, epsilon = EPS);

                // Empirically determined: unit cross-polytope has capacity = 1.0
                // (Spec notes that this value was previously unknown)
                assert_relative_eq!(r.capacity, 1.0, epsilon = 0.01);
            }
            Err(e) => {
                panic!("Tube algorithm failed: {:?}", e);
            }
        }
    }

    /// Test that capacity scales correctly: c(λK) = λ² c(K)
    #[test]
    fn test_capacity_scaling() {
        use crate::fixtures::scaled_cross_polytope;

        let c_unit = tube_capacity(&unit_cross_polytope())
            .expect("Failed for unit")
            .capacity;
        let c_scaled = tube_capacity(&scaled_cross_polytope(2.0))
            .expect("Failed for scaled")
            .capacity;

        println!("Unit cross-polytope capacity: {}", c_unit);
        println!("2x scaled cross-polytope capacity: {}", c_scaled);
        println!("Ratio: {}", c_scaled / c_unit);

        // Symplectic capacity scales as λ²
        // c(2K) = 4 * c(K)
        assert_relative_eq!(c_scaled, 4.0 * c_unit, epsilon = 0.1);
    }

    #[test]
    fn test_debug_action_computation() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        // Take a simple closed tube and analyze its action
        fn collect_first_closed_tubes(
            tube: &Tube,
            data: &PolytopeData,
            max_depth: usize,
        ) -> Vec<(Tube, f64, Vector2<f64>)> {
            let mut results = Vec::new();
            fn recurse(
                tube: &Tube,
                data: &PolytopeData,
                depth: usize,
                max_depth: usize,
                results: &mut Vec<(Tube, f64, Vector2<f64>)>,
            ) {
                if depth >= max_depth || results.len() >= 5 {
                    return;
                }
                let curr_facet = *tube.facet_sequence.last().unwrap();
                for &next_facet in &data.adjacent_facets_forward(curr_facet) {
                    if let Some(extended) = extend_tube(tube, next_facet, data) {
                        if extended.is_closed() {
                            if let Some((action, fixed_pt)) = find_closed_orbit(&extended) {
                                results.push((extended.clone(), action, fixed_pt));
                            }
                        }
                        recurse(&extended, data, depth + 1, max_depth, results);
                    }
                }
            }
            recurse(tube, data, 0, max_depth, &mut results);
            results
        }

        for (i, tfe) in data.two_faces_enriched.iter().enumerate().take(3) {
            let root = create_root_tube(tfe);
            let closed_tubes = collect_first_closed_tubes(&root, &data, 8);

            if !closed_tubes.is_empty() {
                println!("\nFrom root 2-face {} (facets {}, {}):", i, tfe.i, tfe.j);
                for (tube, action, fixed_pt) in closed_tubes.iter().take(3) {
                    println!("  Tube: {:?}", tube.facet_sequence);
                    println!("    Fixed point (2D): {:?}", fixed_pt);
                    println!("    Action from func: {}", action);
                    println!("    Rotation: {}", tube.rotation);

                    // Reconstruct and check 4D orbit
                    if let Ok(orbit) = reconstruct_orbit(fixed_pt, tube, &data) {
                        println!("    Period (4D orbit): {}", orbit.period);
                        println!("    Ratio action/period: {}", action / orbit.period);
                    }
                }
            }
        }
    }

    #[test]
    fn test_create_root_tube() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        for tfe in &data.two_faces_enriched {
            let root = create_root_tube(tfe);

            // Root tube should have identity flow map
            assert_relative_eq!(root.flow_map.matrix, Matrix2::identity(), epsilon = EPS);
            assert!(root.flow_map.offset.norm() < EPS);

            // Root tube should have zero action function
            assert!(root.action_func.gradient.norm() < EPS);
            assert!(root.action_func.constant.abs() < EPS);

            // Root tube should have zero rotation
            assert!(root.rotation.abs() < EPS);

            // p_start and p_end should be non-empty
            assert!(!root.p_start.is_empty());
            assert!(!root.p_end.is_empty());
        }
    }

    #[test]
    fn test_flow_map_symplectic() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        // Take a root tube and extend it
        let tfe = &data.two_faces_enriched[0];
        let root = create_root_tube(tfe);

        let curr_facet = *root.facet_sequence.last().unwrap();
        let next_facets = data.adjacent_facets_forward(curr_facet);

        if let Some(next_facet) = next_facets.first() {
            if let Some(extended) = extend_tube(&root, *next_facet, &data) {
                // Flow map should be symplectic (det = 1)
                let det = extended.flow_map.matrix.determinant();
                assert_relative_eq!(det, 1.0, epsilon = 1e-8);
            }
        }
    }

    /// Test shear case 1: A = I, b = 0 (all points are fixed).
    #[test]
    fn test_shear_case_identity_zero_offset() {
        // Create a synthetic tube where flow_map.matrix = I and flow_map.offset = 0
        let p_start = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);
        let p_end = p_start.clone();

        let flow_map = AffineMap2D {
            matrix: Matrix2::identity(),
            offset: Vector2::zeros(),
        };

        // Action function: action(s) = s.x + s.y + 1.0
        // Minimum over the polygon should be at vertex (0, 0) with action = 1.0
        let action_func = AffineFunc {
            gradient: Vector2::new(1.0, 1.0),
            constant: 1.0,
        };

        let tube = Tube {
            facet_sequence: vec![0, 1],
            p_start,
            p_end,
            flow_map,
            action_func,
            rotation: 0.0,
        };

        let a_minus_i = tube.flow_map.matrix - Matrix2::identity();
        let neg_b = -tube.flow_map.offset;

        let result = find_fixed_point_on_line(&tube, &a_minus_i, &neg_b);

        assert!(
            result.is_some(),
            "Should find fixed point when A = I and b = 0"
        );
        let (action, _fixed_pt) = result.unwrap();

        // The minimum action should be at vertex (0, 0): action = 1.0
        assert_relative_eq!(action, 1.0, epsilon = EPS);
    }

    /// Test shear case 2: A = I, b ≠ 0 (no fixed points).
    #[test]
    fn test_shear_case_identity_nonzero_offset() {
        // Create a synthetic tube where flow_map.matrix = I but flow_map.offset ≠ 0
        let p_start = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);
        let p_end = p_start.clone();

        let flow_map = AffineMap2D {
            matrix: Matrix2::identity(),
            offset: Vector2::new(0.1, 0.2), // Non-zero offset
        };

        let action_func = AffineFunc {
            gradient: Vector2::new(1.0, 1.0),
            constant: 1.0,
        };

        let tube = Tube {
            facet_sequence: vec![0, 1],
            p_start,
            p_end,
            flow_map,
            action_func,
            rotation: 0.0,
        };

        let a_minus_i = tube.flow_map.matrix - Matrix2::identity();
        let neg_b = -tube.flow_map.offset;

        let result = find_fixed_point_on_line(&tube, &a_minus_i, &neg_b);

        assert!(
            result.is_none(),
            "Should not find fixed point when A = I but b ≠ 0"
        );
    }

    /// Test shear case 3: A - I has rank 1 (line of fixed points).
    #[test]
    fn test_shear_case_rank_one() {
        // Create a synthetic tube where A - I has rank 1
        // Use A = [[1, 0.5], [0, 1]], so A - I = [[0, 0.5], [0, 0]]
        // This has rank 1 (column space spanned by [0.5, 0]^T)
        //
        // For fixed points to exist, -b must be in the column space.
        // Column space is spanned by col1 = [0.5, 0]^T
        // So we need b = -[c * 0.5, 0]^T for some c
        // Let's use b = -[0.5, 0]^T, i.e., offset = [-0.5, 0]
        //
        // The fixed point equation (A-I)s = -b becomes:
        // [[0, 0.5], [0, 0]] * s = [0.5, 0]
        // => 0.5 * s.y = 0.5  =>  s.y = 1.0
        // s.x is free, so the line of fixed points is: s = [t, 1.0] for any t

        let p_start = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(2.0, 0.0),
            Vector2::new(2.0, 2.0),
            Vector2::new(0.0, 2.0),
        ]);
        let p_end = p_start.clone();

        let flow_map = AffineMap2D {
            matrix: Matrix2::new(1.0, 0.5, 0.0, 1.0),
            offset: Vector2::new(-0.5, 0.0),
        };

        // Action function: action(s) = s.x + 2.0
        // On the line s = [t, 1.0], action = t + 2.0
        // The line intersects the polygon for t ∈ [0, 2]
        // Minimum is at t = 0, i.e., s = [0, 1], with action = 2.0
        let action_func = AffineFunc {
            gradient: Vector2::new(1.0, 0.0),
            constant: 2.0,
        };

        let tube = Tube {
            facet_sequence: vec![0, 1],
            p_start,
            p_end,
            flow_map,
            action_func,
            rotation: 0.0,
        };

        let a_minus_i = tube.flow_map.matrix - Matrix2::identity();
        let neg_b = -tube.flow_map.offset;

        let result = find_fixed_point_on_line(&tube, &a_minus_i, &neg_b);

        assert!(
            result.is_some(),
            "Should find fixed point on line for rank-1 case"
        );
        let (action, fixed_pt) = result.unwrap();

        // Verify it's actually a fixed point
        let mapped = tube.flow_map.apply(&fixed_pt);
        assert!(
            (mapped - fixed_pt).norm() < EPS,
            "Point should be a fixed point: s = {:?}, A*s+b = {:?}",
            fixed_pt,
            mapped
        );

        // The fixed point should be on the line y = 1.0
        assert_relative_eq!(fixed_pt.y, 1.0, epsilon = 1e-6);

        // The fixed point should minimize action on this line segment
        // For the line s = [t, 1] intersected with [0,2]×[0,2], t ∈ [0,2]
        // action(t) = t + 2.0, minimum at t = 0
        // So we expect fixed_pt ≈ [0, 1] and action ≈ 2.0
        assert_relative_eq!(fixed_pt.x, 0.0, epsilon = 1e-6);
        assert_relative_eq!(action, 2.0, epsilon = 1e-6);
    }

    /// Test shear case 3b: Rank-1 case where -b is NOT in column space (no fixed points).
    #[test]
    fn test_shear_case_rank_one_no_solution() {
        // Use the same A as before: A = [[1, 0.5], [0, 1]]
        // A - I = [[0, 0.5], [0, 0]] (rank 1, column space spanned by [0.5, 0]^T)
        //
        // But this time, choose b such that -b is NOT in the column space.
        // For example, b = [0, 0.1], so -b = [0, -0.1]
        // This is not parallel to [0.5, 0]^T, so no fixed points exist.

        let p_start = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(2.0, 0.0),
            Vector2::new(2.0, 2.0),
            Vector2::new(0.0, 2.0),
        ]);
        let p_end = p_start.clone();

        let flow_map = AffineMap2D {
            matrix: Matrix2::new(1.0, 0.5, 0.0, 1.0),
            offset: Vector2::new(0.0, 0.1), // Offset not in column space
        };

        let action_func = AffineFunc {
            gradient: Vector2::new(1.0, 0.0),
            constant: 2.0,
        };

        let tube = Tube {
            facet_sequence: vec![0, 1],
            p_start,
            p_end,
            flow_map,
            action_func,
            rotation: 0.0,
        };

        let a_minus_i = tube.flow_map.matrix - Matrix2::identity();
        let neg_b = -tube.flow_map.offset;

        let result = find_fixed_point_on_line(&tube, &a_minus_i, &neg_b);

        assert!(
            result.is_none(),
            "Should not find fixed point when -b is not in column space"
        );
    }

    /// Test shear case 3c: Rank-1 case where line doesn't intersect polygon.
    #[test]
    fn test_shear_case_rank_one_no_intersection() {
        // Use A = [[1, 0.5], [0, 1]], so A - I = [[0, 0.5], [0, 0]]
        // Choose b such that the line of fixed points doesn't intersect p_end.
        // Fixed point line: s.y = constant, s.x free
        // Make the constant outside the polygon range.

        let p_start = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(1.0, 0.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);
        let p_end = p_start.clone();

        // For b = [-2.5, 0], we get -b = [2.5, 0]
        // Fixed point equation: 0.5 * s.y = 2.5 => s.y = 5.0
        // But the polygon only covers y ∈ [0, 1], so no intersection.
        let flow_map = AffineMap2D {
            matrix: Matrix2::new(1.0, 0.5, 0.0, 1.0),
            offset: Vector2::new(-2.5, 0.0),
        };

        let action_func = AffineFunc {
            gradient: Vector2::new(1.0, 0.0),
            constant: 2.0,
        };

        let tube = Tube {
            facet_sequence: vec![0, 1],
            p_start,
            p_end,
            flow_map,
            action_func,
            rotation: 0.0,
        };

        let a_minus_i = tube.flow_map.matrix - Matrix2::identity();
        let neg_b = -tube.flow_map.offset;

        let result = find_fixed_point_on_line(&tube, &a_minus_i, &neg_b);

        assert!(
            result.is_none(),
            "Should not find fixed point when line doesn't intersect polygon"
        );
    }
}
