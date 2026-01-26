//! Branch-and-bound algorithm for computing EHZ capacity.
//!
//! The tube algorithm explores "tubes" (sets of Reeb trajectories with fixed combinatorics)
//! using branch-and-bound search:
//!
//! 1. Initialize: Create root tube at each 2-face
//! 2. Branch: Extend tube to all adjacent 2-faces
//! 3. Bound: Prune tubes by action lower bound and rotation bound
//! 4. Find orbits: Check for closed orbits in closed tubes

use std::collections::BinaryHeap;
use std::cmp::Ordering;

use crate::error::{TubeError, TubeResult};
use crate::polytope::{PolytopeData, PolytopeHRep};
use crate::tube::{extend_tube, find_closed_orbits, reconstruct_orbit, ClosedReebOrbit, Tube, TubeResult2};

/// A tube with priority (lower action bound = higher priority).
#[derive(Debug)]
struct PrioritizedTube {
    tube: Tube,
    action_bound: f64,
}

impl PartialEq for PrioritizedTube {
    fn eq(&self, other: &Self) -> bool {
        self.action_bound == other.action_bound
    }
}

impl Eq for PrioritizedTube {}

impl PartialOrd for PrioritizedTube {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl Ord for PrioritizedTube {
    fn cmp(&self, other: &Self) -> Ordering {
        // Reverse ordering: smaller action_bound = higher priority
        other.action_bound.partial_cmp(&self.action_bound)
            .unwrap_or(Ordering::Equal)
    }
}

/// Maximum number of tubes to explore before giving up.
const MAX_TUBES: usize = 100_000;

/// Compute the EHZ capacity using the tube algorithm.
///
/// # Arguments
/// - `hrep`: H-representation of the polytope
///
/// # Returns
/// - `Ok(result)`: The capacity and optimal orbit
/// - `Err`: If the polytope has Lagrangian 2-faces or other errors
pub fn tube_capacity(hrep: &PolytopeHRep) -> TubeResult<TubeResult2> {
    // Preprocess polytope
    let data = PolytopeData::from_hrep(hrep)?;

    // Check for Lagrangian 2-faces (tube algorithm requires NONE)
    if data.has_lagrangian_two_faces() {
        let indices = data.lagrangian_two_face_indices();
        return Err(TubeError::LagrangianTwoFaces {
            count: indices.len(),
            indices,
        });
    }

    // Initialize worklist with root tubes
    let mut worklist: BinaryHeap<PrioritizedTube> = BinaryHeap::new();

    for two_face in &data.two_faces_enriched {
        let root = Tube::root(two_face);
        let action_bound = root.action_lower_bound();
        worklist.push(PrioritizedTube { tube: root, action_bound });
    }

    // Track best solution
    let mut best_action = f64::INFINITY;
    let mut best_orbit: Option<ClosedReebOrbit> = None;
    let mut tubes_explored = 0;
    let mut orbits_found = 0;

    // Branch and bound
    while let Some(PrioritizedTube { tube, action_bound }) = worklist.pop() {
        tubes_explored += 1;

        // Safety limit to prevent infinite exploration
        if tubes_explored >= MAX_TUBES {
            break;
        }

        // Prune by action bound
        if action_bound >= best_action {
            continue;
        }

        // Check if tube should be pruned
        if tube.should_prune(best_action) {
            continue;
        }

        // Get possible extensions
        let extensions = get_extensions(&tube, &data)?;

        for extension in extensions {
            match extension {
                Extension::Closed(orbit_result) => {
                    orbits_found += 1;
                    let (action, fixed_point_2d) = orbit_result;

                    if action < best_action {
                        // Reconstruct and validate orbit
                        match reconstruct_orbit(&fixed_point_2d, &tube, &data) {
                            Ok(orbit) => {
                                // Validate orbit
                                if orbit.validate(&data).is_ok() {
                                    best_action = action;
                                    best_orbit = Some(orbit);
                                }
                            }
                            Err(e) => {
                                // Log but continue
                                eprintln!("Warning: Could not reconstruct orbit: {}", e);
                            }
                        }
                    }
                }
                Extension::Open(new_tube) => {
                    if !new_tube.should_prune(best_action) {
                        let action_bound = new_tube.action_lower_bound();
                        worklist.push(PrioritizedTube { tube: new_tube, action_bound });
                    }
                }
            }
        }
    }

    if best_orbit.is_none() && orbits_found == 0 {
        return Err(TubeError::NoClosedOrbitFound { tubes_explored });
    }

    Ok(TubeResult2 {
        capacity: best_action,
        orbit: best_orbit,
        tubes_explored,
        orbits_found,
    })
}

/// Result of extending a tube.
enum Extension {
    /// A closed tube with a closed orbit (action, fixed point in 2D).
    Closed((f64, nalgebra::Vector2<f64>)),
    /// An open tube that can be extended further.
    Open(Tube),
}

/// Get all extensions of a tube.
fn get_extensions(tube: &Tube, data: &PolytopeData) -> TubeResult<Vec<Extension>> {
    let mut extensions = Vec::new();
    let current_facet = tube.facet_sequence[tube.facet_sequence.len() - 1];

    // Try extending to each adjacent facet
    for next_facet in 0..data.num_facets {
        if next_facet == current_facet {
            continue; // Can't stay on same facet
        }

        // Check if there's a valid 2-face
        if data.get_two_face_enriched(current_facet, next_facet).is_none() {
            continue;
        }

        // Try extending
        match extend_tube(tube, next_facet, data)? {
            Some(extended) => {
                // Check if this creates a closed tube
                if extended.is_closed() {
                    // Find closed orbits
                    match find_closed_orbits(&extended) {
                        Ok(orbits) => {
                            for orbit in orbits {
                                extensions.push(Extension::Closed(orbit));
                            }
                        }
                        Err(TubeError::NearSingularFlowMap { .. }) => {
                            // Near-singular: skip this tube
                            continue;
                        }
                        Err(e) => return Err(e),
                    }
                } else {
                    extensions.push(Extension::Open(extended));
                }
            }
            None => {
                // Extension failed (empty intersection)
                continue;
            }
        }
    }

    Ok(extensions)
}

#[cfg(test)]
mod tests {
    use super::*;
    use nalgebra::Vector4;

    fn unit_tesseract() -> PolytopeHRep {
        PolytopeHRep::new(
            vec![
                Vector4::new(1.0, 0.0, 0.0, 0.0),
                Vector4::new(-1.0, 0.0, 0.0, 0.0),
                Vector4::new(0.0, 1.0, 0.0, 0.0),
                Vector4::new(0.0, -1.0, 0.0, 0.0),
                Vector4::new(0.0, 0.0, 1.0, 0.0),
                Vector4::new(0.0, 0.0, -1.0, 0.0),
                Vector4::new(0.0, 0.0, 0.0, 1.0),
                Vector4::new(0.0, 0.0, 0.0, -1.0),
            ],
            vec![1.0; 8],
        )
    }

    #[test]
    fn test_tesseract_rejected_for_lagrangian_2faces() {
        // The tesseract has Lagrangian 2-faces, so the tube algorithm should reject it
        let tesseract = unit_tesseract();
        let result = tube_capacity(&tesseract);

        assert!(matches!(result, Err(TubeError::LagrangianTwoFaces { .. })),
            "Expected LagrangianTwoFaces error, got {:?}", result);
    }
}
