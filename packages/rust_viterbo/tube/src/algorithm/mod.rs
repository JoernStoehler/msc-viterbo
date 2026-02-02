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
    let end_two_face_idx = match data.two_face_index(prev_facet, curr_facet) {
        Some(idx) => idx,
        None => return extensions, // No valid 2-face, shouldn't happen
    };

    // Find all transitions from this 2-face
    let transition_indices = data.transitions_from(end_two_face_idx);

    for &trans_idx in transition_indices {
        let trans = data.get_transition(trans_idx);
        let exit_two_face = data.get_two_face(trans.two_face_exit);

        if let Some(extended) = extend_tube_with_transition(tube, trans, exit_two_face) {
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
    exit_two_face: &TwoFaceData,
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
    let new_p_end = intersect_polygons(&flowed_end, &exit_two_face.polygon);

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
        panic!("Flow map not invertible");
    };

    // Check p_start is non-empty (otherwise no valid orbits can start here)
    if new_p_start.is_empty() || new_p_start.area() < MIN_POLYGON_AREA {
        return None;
    }

    // Next facet is the exit facet of the exit 2-face
    let next_facet = exit_two_face.exit_facet;

    Some(Tube {
        facet_sequence: [&tube.facet_sequence[..], &[next_facet]].concat(),
        p_start: new_p_start,
        p_end: new_p_end,
        flow_map: new_flow_map,
        action_func: new_action_func,
        rotation: tube.rotation + exit_two_face.rotation,
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
    use nalgebra::Vector2;

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
            let exit_two_face = data.get_two_face(trans.two_face_exit);
            println!(
                "  Trying transition {} to 2-face {}",
                trans_idx, trans.two_face_exit
            );
            match extend_tube_with_transition(&root, trans, exit_two_face) {
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
            let exit_two_face = data.get_two_face(trans.two_face_exit);
            if let Some(extended) = extend_tube_with_transition(&root, trans, exit_two_face) {
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

    // ========================================================================
    // A1: Flow composition order test
    // ========================================================================

    /// Verify flow composition is done as compose(step, tube.flow_map), not the reverse.
    ///
    /// Flow composition for affine maps: (f compose g)(x) = f(g(x)).
    /// When extending a tube, we want new_map(x) = step(tube.flow_map(x)),
    /// so new_map = step.compose(&tube.flow_map).
    #[test]
    fn test_flow_composition_order() {
        use nalgebra::Matrix2;

        // Create two non-commuting affine maps
        let tube_map = AffineMap2D {
            matrix: Matrix2::new(1.0, 2.0, 0.0, 1.0), // Shear: [[1,2],[0,1]]
            offset: Vector2::new(1.0, 0.0),
        };
        let step_map = AffineMap2D {
            matrix: Matrix2::new(2.0, 0.0, 0.0, 1.0), // Scale x: [[2,0],[0,1]]
            offset: Vector2::new(0.0, 1.0),
        };

        // The correct composition: step.compose(&tube_map)
        // This gives: step(tube(x)) = step(Ax + b) = A_step * (A_tube * x + b_tube) + b_step
        let correct_composition = step_map.compose(&tube_map);

        // The wrong composition would be: tube_map.compose(&step_map)
        let wrong_composition = tube_map.compose(&step_map);

        // These should be different (the maps don't commute)
        let test_point = Vector2::new(1.0, 1.0);
        let correct_result = correct_composition.apply(&test_point);
        let wrong_result = wrong_composition.apply(&test_point);

        // Verify they're different
        assert!(
            (correct_result - wrong_result).norm() > 0.1,
            "Test maps should not commute"
        );

        // Verify the correct composition matches step(tube(x))
        let expected = step_map.apply(&tube_map.apply(&test_point));
        assert_relative_eq!(correct_result, expected, epsilon = 1e-10);

        // Verify extend_tube_with_transition uses the correct order
        // by checking the flow_map composition in the code:
        // new_flow_map = flow_step.compose(&tube.flow_map);
        // This is correct: flow_step.compose(&tube.flow_map) means
        // new_flow_map(x) = flow_step(tube.flow_map(x))
    }

    // ========================================================================
    // A2: Action accumulation test
    // ========================================================================

    /// Verify action accumulation pulls back time through flow maps correctly.
    ///
    /// When extending a tube, the new action function should be:
    /// new_action_func = tube.action_func + time_step.compose_with_map(&tube.flow_map)
    ///
    /// This is because action accumulates: total_action(x) = action_so_far(x) + time_for_this_step(flow_map(x))
    /// The time_step is a function of the endpoint, so we need to pull it back to the start point.
    #[test]
    fn test_action_accumulation() {
        use nalgebra::Matrix2;

        // Flow map: maps start point to current position
        let flow_map = AffineMap2D {
            matrix: Matrix2::new(2.0, 0.0, 0.0, 1.0), // Scale x by 2
            offset: Vector2::new(1.0, 0.0),           // Then translate
        };

        // Existing action function (action as function of start point)
        let existing_action = AffineFunc {
            gradient: Vector2::new(1.0, 0.0),
            constant: 5.0,
        };

        // Time step for the new segment (function of position at end of existing flow)
        let time_step = AffineFunc {
            gradient: Vector2::new(0.0, 1.0), // time = y + 2
            constant: 2.0,
        };

        // New action = existing_action + time_step composed with flow_map
        let time_pullback = time_step.compose_with_map(&flow_map);
        let new_action = existing_action.add(&time_pullback);

        // Test at a point
        let start_point = Vector2::new(1.0, 3.0);
        let end_point = flow_map.apply(&start_point); // = (2*1 + 1, 3) = (3, 3)

        // Expected action:
        // existing_action(start) = 1*1 + 5 = 6
        // time_step(end) = 0*3 + 1*3 + 2 = 5
        // total = 6 + 5 = 11
        let expected_action = existing_action.eval(&start_point) + time_step.eval(&end_point);

        // Actual from composed function
        let actual_action = new_action.eval(&start_point);

        assert_relative_eq!(actual_action, expected_action, epsilon = 1e-10);
        assert_relative_eq!(actual_action, 11.0, epsilon = 1e-10);
    }

    // ========================================================================
    // A4: Action lower bound validity test
    // ========================================================================

    /// Verify that action_lower_bound() correctly computes the minimum over vertices.
    ///
    /// For an affine function over a convex polygon, the minimum is achieved at a vertex.
    /// Tubes pruned by action_lower_bound >= best_action are guaranteed to not contain
    /// any orbit with action < best_action.
    #[test]
    fn test_action_lower_bound_valid() {
        use crate::types::Polygon2D;

        // Create a tube with a specific polygon and action function
        let polygon = Polygon2D::new(vec![
            Vector2::new(0.0, 0.0),
            Vector2::new(2.0, 0.0),
            Vector2::new(2.0, 1.0),
            Vector2::new(0.0, 1.0),
        ]);

        let tube = Tube {
            facet_sequence: vec![0, 1],
            p_start: polygon.clone(),
            p_end: polygon,
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc {
                gradient: Vector2::new(1.0, 2.0), // action = x + 2y + 3
                constant: 3.0,
            },
            rotation: 0.0,
        };

        let lower_bound = tube.action_lower_bound();

        // Minimum should be at (0,0): action = 0 + 0 + 3 = 3
        assert_relative_eq!(lower_bound, 3.0, epsilon = 1e-10);

        // Verify this is indeed the minimum by checking all vertices
        for v in &tube.p_start.vertices {
            let action_at_v = tube.action_func.eval(v);
            assert!(
                action_at_v >= lower_bound - 1e-10,
                "Action at {:?} = {} is less than lower bound {}",
                v,
                action_at_v,
                lower_bound
            );
        }

        // Verify the pruning logic: if best_action <= lower_bound,
        // the tube cannot contain a better orbit
        let best_action = 3.0;
        assert!(
            tube.action_lower_bound() >= best_action,
            "This tube would be correctly pruned when best_action = {}",
            best_action
        );

        // A tube with lower action_lower_bound should NOT be pruned
        let better_tube = Tube {
            action_func: AffineFunc {
                gradient: Vector2::new(0.5, 0.5),
                constant: 1.0, // lower constant = lower minimum
            },
            ..tube.clone()
        };
        assert!(
            better_tube.action_lower_bound() < best_action,
            "Better tube should not be pruned"
        );
    }

    // ========================================================================
    // A5: Pruning soundness test
    // ========================================================================

    /// Verify pruning is sound: pruning gives the correct capacity.
    ///
    /// The tube algorithm prunes tubes whose action_lower_bound >= best_action.
    /// This test verifies that pruning doesn't discard any tube containing the optimal orbit
    /// by checking that the computed capacity matches the known analytical value.
    ///
    /// For a more thorough soundness test, we would need to run the algorithm without
    /// pruning and compare, but that's not practical (exponential blowup). Instead,
    /// we verify against known capacities and check that pruned tubes genuinely have
    /// worse action bounds.
    #[test]
    fn test_pruning_soundness() {
        // Test 1: Cross-polytope - known capacity is 1.0
        let hrep = unit_cross_polytope();
        let result = tube_capacity(&hrep).expect("Should find capacity");

        // Verify the capacity matches the known analytical value
        assert_relative_eq!(result.capacity, 1.0, epsilon = 0.01);

        // The algorithm explores and prunes tubes
        println!(
            "Cross-polytope: capacity={}, explored={}, pruned={}",
            result.capacity, result.tubes_explored, result.tubes_pruned
        );

        // Test 2: Scaled cross-polytope - capacity should scale as lambda^2
        use crate::fixtures::scaled_cross_polytope;
        let lambda = 2.0;
        let scaled = scaled_cross_polytope(lambda);
        let result_scaled = tube_capacity(&scaled).expect("Should find capacity");

        // Capacity scales as lambda^2
        assert_relative_eq!(
            result_scaled.capacity,
            lambda * lambda * 1.0,
            epsilon = 0.05
        );

        // Test 3: Verify action_lower_bound semantics
        // Create a tube and verify that any point in p_start has action >= action_lower_bound
        let data = preprocess(&hrep).unwrap();
        let tf = &data.two_face_data[0];
        let root = create_root_tube(tf);

        // Root tube has zero action, so lower bound should be 0
        assert_relative_eq!(root.action_lower_bound(), 0.0, epsilon = 1e-10);

        // Extend the root tube and check the invariant
        let trans_indices = data.transitions_from(0);
        if !trans_indices.is_empty() {
            let trans = data.get_transition(trans_indices[0]);
            let exit_two_face = data.get_two_face(trans.two_face_exit);
            if let Some(extended) = extend_tube_with_transition(&root, trans, exit_two_face) {
                let lower_bound = extended.action_lower_bound();
                // Verify all vertices have action >= lower_bound
                for v in &extended.p_start.vertices {
                    let action_at_v = extended.action_func.eval(v);
                    assert!(
                        action_at_v >= lower_bound - 1e-10,
                        "Action at vertex should be >= lower bound"
                    );
                }
            }
        }
    }

    // ========================================================================
    // A7: Symplectic after many transitions test
    // ========================================================================

    /// Verify flow maps remain symplectic (det ≈ 1) after many compositions.
    ///
    /// Each flow step should be a symplectic (area-preserving) transformation.
    /// After composing many steps, the cumulative flow map should still have det ≈ 1.
    /// This tests numerical stability of the composition.
    #[test]
    fn test_symplectic_after_many_transitions() {
        let hrep = unit_cross_polytope();
        let data = preprocess(&hrep).unwrap();

        // We'll manually extend a tube multiple times and track the determinant
        // Use BFS to find long tubes
        let mut tubes_by_length: Vec<Vec<Tube>> = vec![Vec::new(); 15];

        // Start with root tubes
        for tf in &data.two_face_data {
            tubes_by_length[2].push(create_root_tube(tf));
        }

        // Extend tubes to build longer ones
        for len in 2..14 {
            // Collect extensions separately to avoid borrow conflicts
            let mut extensions = Vec::new();
            for tube in &tubes_by_length[len] {
                let (prev_facet, curr_facet) = tube.end_two_face();
                if let Some(end_two_face_idx) = data.two_face_index(prev_facet, curr_facet) {
                    for &trans_idx in data.transitions_from(end_two_face_idx) {
                        let trans = data.get_transition(trans_idx);
                        let exit_two_face = data.get_two_face(trans.two_face_exit);
                        if let Some(extended) =
                            extend_tube_with_transition(tube, trans, exit_two_face)
                        {
                            extensions.push(extended);
                            // Only keep a few tubes per length to avoid explosion
                            if extensions.len() >= 20 {
                                break;
                            }
                        }
                    }
                }
                if extensions.len() >= 20 {
                    break;
                }
            }
            tubes_by_length[len + 1].extend(extensions);
        }

        // Check determinants of long tubes (10+ transitions)
        let mut checked = 0;
        for len in 10..15 {
            for tube in &tubes_by_length[len] {
                let det = tube.flow_map.matrix.determinant();
                assert!(
                    (det - 1.0).abs() < 1e-6,
                    "Flow map determinant after {} transitions: {}",
                    len - 2,
                    det
                );
                checked += 1;
            }
        }

        assert!(
            checked > 0,
            "Should have found tubes with 10+ transitions to test"
        );
        println!("Verified det ≈ 1 for {} long tubes", checked);
    }

    // ========================================================================
    // A8: Closure detection test
    // ========================================================================

    /// Verify is_closed() correctly identifies closed tubes (start 2-face == end 2-face).
    #[test]
    fn test_closure_detection() {
        use crate::types::Polygon2D;

        // A closed tube: facet sequence starts and ends on same 2-face
        // 2-face is identified by (facet_sequence[0], facet_sequence[1]) == (facet_sequence[n-2], facet_sequence[n-1])
        let closed_tube = Tube {
            facet_sequence: vec![0, 1, 2, 0, 1], // Starts on (0,1), ends on (0,1) -> closed
            p_start: Polygon2D::new(vec![
                Vector2::new(0.0, 0.0),
                Vector2::new(1.0, 0.0),
                Vector2::new(0.5, 1.0),
            ]),
            p_end: Polygon2D::new(vec![
                Vector2::new(0.0, 0.0),
                Vector2::new(1.0, 0.0),
                Vector2::new(0.5, 1.0),
            ]),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
        };

        assert!(
            closed_tube.is_closed(),
            "Tube with matching start/end 2-faces should be closed"
        );
        assert_eq!(closed_tube.start_two_face(), (0, 1));
        assert_eq!(closed_tube.end_two_face(), (0, 1));

        // An open tube: different start and end 2-faces
        let open_tube = Tube {
            facet_sequence: vec![0, 1, 2, 3], // Starts on (0,1), ends on (2,3) -> open
            p_start: closed_tube.p_start.clone(),
            p_end: closed_tube.p_end.clone(),
            flow_map: AffineMap2D::identity(),
            action_func: AffineFunc::zero(),
            rotation: 0.0,
        };

        assert!(
            !open_tube.is_closed(),
            "Tube with different start/end 2-faces should be open"
        );
        assert_eq!(open_tube.start_two_face(), (0, 1));
        assert_eq!(open_tube.end_two_face(), (2, 3));

        // Another open tube: same facets but in different positions
        let another_open = Tube {
            facet_sequence: vec![0, 1, 2, 1, 0], // Starts on (0,1), ends on (1,0) -> different!
            ..closed_tube.clone()
        };

        // Note: (0,1) != (1,0) as ordered pairs, but the 2-face check uses ordered pairs
        assert!(
            !another_open.is_closed(),
            "(0,1) and (1,0) are different ordered pairs"
        );
    }
}
