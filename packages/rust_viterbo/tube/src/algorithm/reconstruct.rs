//! 4D orbit reconstruction from 2D fixed points.
//!
//! After finding a fixed point in trivialized 2D coordinates, this module
//! reconstructs the full 4D piecewise-linear Reeb orbit on the polytope boundary.

use nalgebra::{Vector2, Vector4};

use crate::constants::{EPS, EPS_CLOSURE};
use crate::preprocess::PolytopeData;
use crate::types::{ClosedReebOrbit, Tube, TubeError, TwoFaceData};

/// Reconstruct the 4D orbit from 2D fixed point and tube.
///
/// This converts the abstract 2D fixed point back to a concrete piecewise-linear
/// curve in ℝ⁴ that traces the Reeb flow on the polytope boundary.
pub(super) fn reconstruct_orbit(
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
    let start_two_face_idx = data
        .two_face_index(seq[0], seq[1])
        .ok_or_else(|| TubeError::InvalidPolytope("Start 2-face not found".to_string()))?;
    let start_two_face = data.get_two_face(start_two_face_idx);

    // Convert starting point to 4D
    let start_4d = untrivialize_point(fixed_point_2d, start_two_face);

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
    let closure_error = (breakpoints
        .last()
        .expect("breakpoints initialized with start_4d")
        - start_4d)
        .norm();
    if closure_error > EPS_CLOSURE {
        return Err(TubeError::NumericalInstability(format!(
            "Orbit failed to close: error = {:.2e}",
            closure_error
        )));
    }

    // Set last point exactly equal to first
    *breakpoints
        .last_mut()
        .expect("breakpoints initialized with start_4d") = start_4d;

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
///
/// The trivialization maps the 2-face tangent space to ℝ² using basis vectors
/// (jn, kn) where n is the facet normal. This inverts that map.
fn untrivialize_point(point_2d: &Vector2<f64>, tf: &TwoFaceData) -> Vector4<f64> {
    tf.centroid_4d + point_2d[0] * tf.basis_exit[0] + point_2d[1] * tf.basis_exit[1]
}
