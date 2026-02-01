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

use nalgebra::{Matrix2, Vector2};
use std::collections::BinaryHeap;

use crate::constants::{EPS, EPS_ROTATION, MAX_ROTATION, MIN_POLYGON_AREA};
use crate::geometry::{apply_affine_to_polygon, intersect_polygons};
use crate::preprocess::{preprocess, PolytopeData};
use crate::quaternion::{apply_quat_j, apply_quat_k};
use crate::types::{
    AffineFunc, AffineMap2D, ClosedReebOrbit, FlowDirection, PolytopeHRep, Tube, TubeError,
    TubeResult, TwoFaceEnriched,
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
    for tfe in &data.two_faces_enriched {
        let root = create_root_tube(tfe);
        worklist.push(TubePriority::new(root));
    }

    // Branch and bound
    while let Some(tube_priority) = worklist.pop() {
        let tube = tube_priority.tube;
        tubes_explored += 1;

        // Sanity check: heap shouldn't grow unboundedly
        #[cfg(debug_assertions)]
        debug_assert!(
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

// ============================================================================
// Flow Map Computation
// ============================================================================

/// Compute the affine flow map and time function for flowing across a facet.
///
/// Given entry and exit 2-faces on a facet, computes:
/// - The affine map φ: ℝ² → ℝ² that transforms trivialized entry coordinates to exit coordinates
/// - The affine time function t: ℝ² → ℝ giving the flow time as a function of starting position
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
                    println!("    Could not extend (empty intersection or no 2-face)");
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

        for tfe in &data.two_faces_enriched {
            let root = create_root_tube(tfe);

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
        let tfe = &data.two_faces_enriched[0];
        let root = create_root_tube(tfe);

        let curr_facet = *root.facet_sequence.last().unwrap();
        let next_facets = data.adjacent_facets_forward(curr_facet);

        for &next_facet in &next_facets {
            if let Some(extended) = extend_tube(&root, next_facet, &data) {
                let det = extended.flow_map.matrix.determinant();
                assert_relative_eq!(det, 1.0, epsilon = 1e-6);
            }
        }
    }
}
