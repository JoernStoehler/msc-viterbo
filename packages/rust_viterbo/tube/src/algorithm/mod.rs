//! Tube algorithm for computing EHZ capacity.
//!
//! This module implements the branch-and-bound search over "tubes" —
//! sets of Reeb trajectories sharing a combinatorial class (facet sequence).
//!
//! ## Algorithm Structure
//!
//! 1. **Preprocess**: Convert H-rep to enriched combinatorial data (see `preprocess` module)
//! 2. **Search**: Branch-and-bound over facet sequences, pruning by action and rotation bounds
//! 3. **Closure**: Detect fixed points of the return map (see `closure` submodule)
//! 4. **Reconstruct**: Convert 2D fixed point to 4D orbit (see `reconstruct` submodule)
//!
//! Source: This thesis (Stöhler 2026), building on CH2021's mathematical framework.

mod closure;
mod reconstruct;

use std::collections::BinaryHeap;

use crate::constants::{EPS_ROTATION, MAX_ROTATION, MIN_POLYGON_AREA};
use crate::geometry::{apply_affine_to_polygon, intersect_polygons};
use crate::preprocess::{preprocess, PolytopeData};
use crate::types::{
    AffineFunc, AffineMap2D, ClosedReebOrbit, PolytopeHRep, ThreeFacetData, Tube, TubeError,
    TubeResult, TwoFaceData,
};

use closure::find_closed_orbit;
use reconstruct::reconstruct_orbit;

/// Maximum expected heap size for sanity checking.
/// For a polytope with n facets, tubes have length O(n), and the branching factor
/// is bounded by the number of adjacent facets (~6 for regular polytopes).
/// With good pruning, the heap should stay much smaller than this.
#[cfg(debug_assertions)]
const MAX_EXPECTED_HEAP_SIZE: usize = 100_000;

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
    for tf in &data.two_face_data {
        let root = create_root_tube(tf);
        worklist.push(TubePriority::new(root));
    }

    // Branch and bound
    while let Some(tube_priority) = worklist.pop() {
        let tube = tube_priority.tube;
        tubes_explored += 1;

        // Sanity check: heap shouldn't grow unboundedly
        assert!(
            worklist.len() < MAX_EXPECTED_HEAP_SIZE,
            "Heap size {} exceeds expected maximum {} - possible infinite loop or bad pruning",
            worklist.len(),
            MAX_EXPECTED_HEAP_SIZE
        );

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

// ============================================================================
// Priority Queue Support
// ============================================================================

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

// ============================================================================
// Tube Operations
// ============================================================================

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
fn create_root_tube(tf: &TwoFaceData) -> Tube {
    Tube {
        facet_sequence: vec![tf.entry_facet, tf.exit_facet],
        p_start: tf.polygon.clone(),
        p_end: tf.polygon.clone(),
        flow_map: AffineMap2D::identity(),
        action_func: AffineFunc::zero(),
        rotation: 0.0,
    }
}

/// Get all valid extensions of a tube.
fn get_extensions(tube: &Tube, data: &PolytopeData) -> Vec<Extension> {
    let mut extensions = Vec::new();

    // Get current end 2-face index
    let (prev_facet, curr_facet) = tube.end_two_face();
    let end_2face_idx = match data.two_face_index(prev_facet, curr_facet) {
        Some(idx) => idx,
        None => return extensions, // No valid 2-face, shouldn't happen
    };

    // Find all transitions from this 2-face
    let transition_indices = data.transitions_from(end_2face_idx);

    for &trans_idx in transition_indices {
        let trans = data.get_transition(trans_idx);
        let exit_2face = data.get_two_face(trans.two_face_exit);

        if let Some(extended) = extend_tube_with_transition(tube, trans, exit_2face) {
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

/// Extend a tube using precomputed transition data.
fn extend_tube_with_transition(
    tube: &Tube,
    trans: &ThreeFacetData,
    exit_2face: &TwoFaceData,
) -> Option<Tube> {
    // Build the flow step from precomputed transition data
    let flow_step = AffineMap2D {
        matrix: trans.flow_matrix,
        offset: trans.flow_offset,
    };
    let time_step = AffineFunc {
        gradient: trans.time_gradient,
        constant: trans.time_constant,
    };

    // Compose with existing flow map
    let new_flow_map = flow_step.compose(&tube.flow_map);

    // Compose action function
    let new_action_func = tube
        .action_func
        .add(&time_step.compose_with_map(&tube.flow_map));

    // Apply flow to end polygon and intersect with exit 2-face
    let flowed_end = apply_affine_to_polygon(&flow_step, &tube.p_end);
    let new_p_end = intersect_polygons(&flowed_end, &exit_2face.polygon);

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
        assert!(false, "Flow map not invertible");
        tube.p_start.clone()
    };

    // Check p_start is non-empty (otherwise no valid orbits can start here)
    if new_p_start.is_empty() || new_p_start.area() < MIN_POLYGON_AREA {
        return None;
    }

    // Next facet is the exit facet of the exit 2-face
    let next_facet = exit_2face.exit_facet;

    Some(Tube {
        facet_sequence: [&tube.facet_sequence[..], &[next_facet]].concat(),
        p_start: new_p_start,
        p_end: new_p_end,
        flow_map: new_flow_map,
        action_func: new_action_func,
        rotation: tube.rotation + exit_2face.rotation,
    })
}

// ============================================================================
// Tests
// ============================================================================

#[cfg(test)]
mod tests {
    use super::*;
    use crate::fixtures::unit_cross_polytope;
    use approx::assert_relative_eq;

    #[test]
    fn test_debug_tube_algorithm() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        println!("Num facets: {}", data.num_facets);
        println!("Num 2-faces: {}", data.two_face_data.len());
        println!("Num transitions: {}", data.transitions.len());

        // Check adjacency via transitions
        for (k, tf) in data.two_face_data.iter().enumerate() {
            let trans = data.transitions_from(k);
            if !trans.is_empty() {
                println!(
                    "2-face {} ({} -> {}) has {} outgoing transitions",
                    k,
                    tf.entry_facet,
                    tf.exit_facet,
                    trans.len()
                );
            }
        }

        // Try extending one root tube
        let tf = &data.two_face_data[0];
        println!(
            "\nRoot tube on 2-face ({} -> {})",
            tf.entry_facet, tf.exit_facet
        );
        let root = create_root_tube(tf);
        println!(
            "Root facet_sequence: {:?}, p_start area: {}",
            root.facet_sequence,
            root.p_start.area()
        );

        let trans_indices = data.transitions_from(0);
        println!("Transitions from 2-face 0: {:?}", trans_indices);

        for &trans_idx in trans_indices {
            let trans = data.get_transition(trans_idx);
            let exit_2face = data.get_two_face(trans.two_face_exit);
            println!(
                "  Trying transition {} to 2-face {}",
                trans_idx, trans.two_face_exit
            );
            match extend_tube_with_transition(&root, trans, exit_2face) {
                Some(extended) => {
                    println!(
                        "    Extended! seq={:?}, p_end area={}",
                        extended.facet_sequence,
                        extended.p_end.area()
                    );
                }
                None => {
                    println!("    Could not extend (empty intersection)");
                }
            }
        }
    }

    #[test]
    fn test_tube_capacity_cross_polytope() {
        let hrep = unit_cross_polytope();
        let result = tube_capacity(&hrep).expect("Should find capacity");

        println!("Capacity: {}", result.capacity);
        println!("Tubes explored: {}", result.tubes_explored);
        println!("Tubes pruned: {}", result.tubes_pruned);

        // Cross-polytope capacity is 1.0
        assert_relative_eq!(result.capacity, 1.0, epsilon = 0.01);
    }

    #[test]
    fn test_root_tube_invariants() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        for tf in &data.two_face_data {
            let root = create_root_tube(tf);

            // p_start should equal p_end for root tube
            assert_eq!(root.p_start.vertices.len(), root.p_end.vertices.len());

            // Flow map should be identity
            assert_relative_eq!(root.flow_map.matrix[(0, 0)], 1.0, epsilon = 1e-10);
            assert_relative_eq!(root.flow_map.matrix[(1, 1)], 1.0, epsilon = 1e-10);
            assert_relative_eq!(root.flow_map.matrix[(0, 1)], 0.0, epsilon = 1e-10);
            assert_relative_eq!(root.flow_map.matrix[(1, 0)], 0.0, epsilon = 1e-10);

            // Action should be zero
            assert_relative_eq!(root.action_func.constant, 0.0, epsilon = 1e-10);

            // Rotation should be zero
            assert_relative_eq!(root.rotation, 0.0, epsilon = 1e-10);
        }
    }

    #[test]
    fn test_flow_map_is_symplectic() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        // Extend a root tube and check that flow maps are symplectic (det = 1)
        let tf = &data.two_face_data[0];
        let root = create_root_tube(tf);

        let trans_indices = data.transitions_from(0);

        for &trans_idx in trans_indices {
            let trans = data.get_transition(trans_idx);
            let exit_2face = data.get_two_face(trans.two_face_exit);
            if let Some(extended) = extend_tube_with_transition(&root, trans, exit_2face) {
                let det = extended.flow_map.matrix.determinant();
                assert_relative_eq!(det, 1.0, epsilon = 1e-6);
            }
        }
    }

    // ========================================================================
    // Rejection path tests
    // ========================================================================

    #[test]
    fn test_rejects_too_few_facets() {
        use nalgebra::Vector4;

        // 4 facets is too few for a 4D polytope
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
        ];
        let heights = vec![1.0, 1.0, 1.0, 1.0];
        let hrep = PolytopeHRep::new(normals, heights);

        let result = tube_capacity(&hrep);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            matches!(err, TubeError::InvalidPolytope(_)),
            "Expected InvalidPolytope, got {:?}",
            err
        );
    }

    #[test]
    fn test_rejects_non_unit_normals() {
        use nalgebra::Vector4;

        // Non-unit normal (magnitude 2)
        let normals = vec![
            Vector4::new(2.0, 0.0, 0.0, 0.0), // Not unit!
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
        ];
        let heights = vec![1.0, 1.0, 1.0, 1.0, 1.0];
        let hrep = PolytopeHRep::new(normals, heights);

        let result = tube_capacity(&hrep);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            matches!(err, TubeError::InvalidPolytope(_)),
            "Expected InvalidPolytope for non-unit normal, got {:?}",
            err
        );
    }

    #[test]
    fn test_rejects_non_positive_height() {
        use nalgebra::Vector4;

        // Zero height
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
        ];
        let heights = vec![0.0, 1.0, 1.0, 1.0, 1.0]; // First height is 0!
        let hrep = PolytopeHRep::new(normals, heights);

        let result = tube_capacity(&hrep);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            matches!(err, TubeError::InvalidPolytope(_)),
            "Expected InvalidPolytope for non-positive height, got {:?}",
            err
        );
    }

    #[test]
    fn test_rejects_lagrangian_polytope() {
        use crate::fixtures::unit_tesseract;

        // Tesseract has Lagrangian 2-faces
        let hrep = unit_tesseract();
        let result = tube_capacity(&hrep);
        assert!(result.is_err());
        let err = result.unwrap_err();
        assert!(
            matches!(err, TubeError::HasLagrangianTwoFaces),
            "Expected HasLagrangianTwoFaces, got {:?}",
            err
        );
    }
}
