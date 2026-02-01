//! Fixed point detection for closed Reeb orbits.
//!
//! This module handles the mathematical problem: given an affine return map φ(s) = As + b,
//! find fixed points s* where φ(s*) = s*.
//!
//! Three cases arise based on det(A - I):
//! - **Regular case** (det ≠ 0): Unique fixed point s* = (A-I)⁻¹(-b)
//! - **Shear case** (det ≈ 0, rank 1): Fixed points form a line
//! - **Identity case** (A ≈ I): All points fixed if b ≈ 0, none otherwise

use nalgebra::{Matrix2, Vector2};

use crate::constants::{EPS, EPS_CLOSURE};
use crate::geometry::point_in_polygon;
use crate::types::{AffineFunc, AffineMap2D, Polygon2D, Tube};

/// Find closed orbits as fixed points of the flow map.
///
/// For shear transformations (det(A-I) ≈ 0), fixed points form a line.
/// We find where this line intersects p_end and return the minimum-action point.
pub(super) fn find_closed_orbit(tube: &Tube) -> Option<(f64, Vector2<f64>)> {
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
            panic!(
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
            // All points in p_end are fixed points
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
    // Find where this line intersects the valid region (p_end)
    intersect_line_with_polygon_min_action(
        &s_particular,
        &null_vec,
        &tube.p_end,
        &tube.action_func,
        &tube.flow_map,
    )
}

/// Find the fixed point with minimum action when all points are fixed (A = I, b = 0).
fn find_min_action_in_polygon(tube: &Tube) -> Option<(f64, Vector2<f64>)> {
    // Action is affine: action(s) = g · s + c
    // Minimum is at a vertex of the polygon or where gradient points outside
    // Use p_end as the valid region
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
fn intersect_line_with_polygon_min_action(
    point_on_line: &Vector2<f64>,
    direction: &Vector2<f64>,
    polygon: &Polygon2D,
    action_func: &AffineFunc,
    flow_map: &AffineMap2D,
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

#[cfg(test)]
mod tests {
    use super::*;
    use nalgebra::Matrix2;

    /// Helper to create a simple tube for testing fixed point detection.
    fn make_test_tube(
        matrix: Matrix2<f64>,
        offset: Vector2<f64>,
        action_gradient: Vector2<f64>,
        action_constant: f64,
    ) -> Tube {
        let polygon = Polygon2D::new(vec![
            Vector2::new(-1.0, -1.0),
            Vector2::new(1.0, -1.0),
            Vector2::new(1.0, 1.0),
            Vector2::new(-1.0, 1.0),
        ]);

        Tube {
            facet_sequence: vec![0, 1, 0], // Closed tube
            p_start: polygon.clone(),
            p_end: polygon,
            flow_map: AffineMap2D { matrix, offset },
            action_func: AffineFunc {
                gradient: action_gradient,
                constant: action_constant,
            },
            rotation: 0.0,
        }
    }

    #[test]
    fn test_shear_case_identity_zero_offset() {
        // A = I, b = 0: All points are fixed
        let tube = make_test_tube(
            Matrix2::identity(),
            Vector2::zeros(),
            Vector2::new(1.0, 0.0), // action = x + 1
            1.0,
        );

        let result = find_closed_orbit(&tube);
        assert!(result.is_some(), "Should find fixed point when A=I, b=0");

        let (action, point) = result.unwrap();
        // Minimum action at x = -1 (left edge), action = -1 + 1 = 0... but we need positive
        // So it should be at a vertex with positive action
        assert!(action > 0.0, "Action should be positive");
        assert!(
            point_in_polygon(&point, &tube.p_end),
            "Point should be in polygon"
        );
    }

    #[test]
    fn test_shear_case_identity_nonzero_offset() {
        // A = I, b ≠ 0: No fixed points
        let tube = make_test_tube(
            Matrix2::identity(),
            Vector2::new(1.0, 0.0), // b ≠ 0
            Vector2::new(1.0, 1.0),
            1.0,
        );

        let result = find_closed_orbit(&tube);
        assert!(
            result.is_none(),
            "Should find no fixed points when A=I, b≠0"
        );
    }

    #[test]
    fn test_shear_case_rank_one() {
        // A - I has rank 1: fixed points form a line
        // A = [[1, 1], [0, 1]], so A - I = [[0, 1], [0, 0]]
        // Fixed point equation: (A-I)s = -b => s_y = -b_x
        // For b = (0, 0), all points on line y = 0 are fixed
        let tube = make_test_tube(
            Matrix2::new(1.0, 1.0, 0.0, 1.0),
            Vector2::zeros(),
            Vector2::new(0.0, 1.0), // action = y + 1
            1.0,
        );

        let result = find_closed_orbit(&tube);
        assert!(result.is_some(), "Should find fixed point on line");

        let (action, point) = result.unwrap();
        // Fixed points are on y = 0 line
        // Minimum action at y = -1 (bottom of polygon), action = -1 + 1 = 0
        // But we need positive action, so should be at y slightly > -1
        assert!(action > 0.0, "Action should be positive");

        // Verify it's actually a fixed point
        let mapped = tube.flow_map.apply(&point);
        assert!(
            (point - mapped).norm() < EPS_CLOSURE,
            "Point should be a fixed point"
        );
    }

    #[test]
    fn test_shear_case_rank_one_no_solution() {
        // A - I has rank 1, but -b is not in column space
        // A = [[1, 1], [0, 1]], A - I = [[0, 1], [0, 0]]
        // Column space is span of (1, 0)
        // For b = (0, 1), -b = (0, -1) is not in column space
        let tube = make_test_tube(
            Matrix2::new(1.0, 1.0, 0.0, 1.0),
            Vector2::new(0.0, 1.0),
            Vector2::new(1.0, 1.0),
            1.0,
        );

        let result = find_closed_orbit(&tube);
        assert!(
            result.is_none(),
            "Should find no fixed points when -b not in column space"
        );
    }

    #[test]
    fn test_regular_case_unique_fixed_point() {
        // Regular case: det(A-I) ≠ 0, unique fixed point
        // A = [[0.5, 0], [0, 0.5]], A - I = [[-0.5, 0], [0, -0.5]]
        // Fixed point: s = (A-I)^{-1}(-b) = 2b
        let tube = make_test_tube(
            Matrix2::new(0.5, 0.0, 0.0, 0.5),
            Vector2::new(0.25, 0.25), // b, so fixed point at (0.5, 0.5)
            Vector2::new(1.0, 1.0),   // action = x + y + 1
            1.0,
        );

        let result = find_closed_orbit(&tube);
        assert!(result.is_some(), "Should find unique fixed point");

        let (action, point) = result.unwrap();
        // Fixed point should be at 2 * (0.25, 0.25) = (0.5, 0.5)
        assert!(
            (point - Vector2::new(0.5, 0.5)).norm() < 0.01,
            "Fixed point should be at (0.5, 0.5), got {:?}",
            point
        );
        assert!(
            (action - 2.0).abs() < 0.01,
            "Action should be 2.0, got {}",
            action
        );
    }
}
