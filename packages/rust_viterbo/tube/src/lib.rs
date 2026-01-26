//! Tube algorithm for computing EHZ capacity of convex polytopes.
//!
//! This crate implements the Tube algorithm from Stöhler 2026 thesis for computing
//! the Ekeland-Hofer-Zehnder (EHZ) capacity of convex polytopes in R^4 with **no
//! Lagrangian 2-faces**.
//!
//! # Algorithm Overview
//!
//! The Tube algorithm uses branch-and-bound search over "tubes" — sets of Reeb
//! trajectories sharing a combinatorial class (facet sequence). Key features:
//!
//! - Works on polytopes with NO Lagrangian 2-faces (ω(n_i, n_j) ≠ 0 for all adjacent pairs)
//! - Uses trivialization (CH2021 Def 2.15) to reduce 4D flow to 2D affine maps
//! - Prunes tubes by action lower bound and rotation bound (≤ 2 turns)
//! - Finds closed orbits as fixed points of the composed flow map
//!
//! # Usage
//!
//! ```
//! use tube::{tube_capacity, PolytopeHRep, TubeError};
//!
//! // Create a unit cross-polytope conv{±e₁, ±e₂, ±e₃, ±e₄}
//! let polytope = tube::fixtures::unit_cross_polytope();
//!
//! // Cross-polytope has NO Lagrangian 2-faces, so tube algorithm accepts it
//! // (it won't return LagrangianTwoFaces error)
//! let result = tube_capacity(&polytope);
//! assert!(!matches!(result, Err(TubeError::LagrangianTwoFaces { .. })));
//! ```
//!
//! # Applicability
//!
//! **Requires:** Polytope with NO Lagrangian 2-faces.
//!
//! Use the Billiard algorithm or HK2017 for polytopes with Lagrangian 2-faces.
//!
//! # References
//!
//! - CH2021: Chaidez-Hutchings, "Computing Reeb Dynamics on Four-Dimensional Convex Polytopes"
//! - Stöhler 2026: This thesis (tube algorithm design)

pub mod consts;
pub mod error;
pub mod fixtures;
pub mod geom;
pub mod polytope;
pub mod polygon;
pub mod symplectic;
pub mod trivialization;
pub mod tube;
pub mod algorithm;

// Re-export main public API
pub use algorithm::tube_capacity;
pub use error::TubeError;
pub use polytope::{PolytopeHRep, PolytopeData};
pub use tube::{Tube, ClosedReebOrbit};

#[cfg(test)]
mod integration_tests {
    use super::*;
    use tube::extend_tube;

    #[test]
    fn test_cross_polytope_accepted_no_lagrangian_error() {
        // The cross-polytope has NO Lagrangian 2-faces (with proper vertex-based adjacency),
        // so the tube algorithm should NOT return a LagrangianTwoFaces error.
        let cross = fixtures::unit_cross_polytope();
        let result = tube_capacity(&cross);

        // Verify it's not rejected for Lagrangian 2-faces
        assert!(
            !matches!(result, Err(TubeError::LagrangianTwoFaces { .. })),
            "Cross-polytope should NOT be rejected for Lagrangian 2-faces, got {:?}",
            result
        );

        // The algorithm may or may not find an orbit depending on search parameters
        // For now, we just verify the Lagrangian check passes
        match &result {
            Ok(r) => eprintln!("Found orbit with capacity: {}", r.capacity),
            Err(TubeError::NoClosedOrbitFound { tubes_explored }) => {
                eprintln!("No orbit found after {} tubes (search may need tuning)", tubes_explored);
            }
            Err(e) => panic!("Unexpected error: {:?}", e),
        }
    }

    #[test]
    fn test_cross_polytope_tube_diagnostics() {
        // Debug test to understand the tube search
        let cross = fixtures::unit_cross_polytope();
        let data = PolytopeData::from_hrep(&cross).unwrap();

        eprintln!("\n=== Cross-polytope tube diagnostics ===");
        eprintln!("Enriched 2-faces: {}", data.two_faces_enriched.len());

        // Look at a few 2-face properties
        for (i, tf) in data.two_faces_enriched.iter().take(3).enumerate() {
            eprintln!("\n2-face {}: entry={}, exit={}", i, tf.entry_facet, tf.exit_facet);
            eprintln!("  rotation: {:.4}", tf.rotation);
            eprintln!("  polygon vertices: {}", tf.polygon_2d.vertices.len());
            eprintln!("  polygon area: {:.6}", tf.polygon_2d.area());
        }

        // BFS to find shortest closed tubes
        eprintln!("\n=== Searching for closed tubes ===");
        let root = Tube::root(&data.two_faces_enriched[0]);
        eprintln!("Start: entry={}, exit={}", root.facet_sequence[0], root.facet_sequence[1]);

        let mut tubes = vec![root];
        let mut closed_found = 0;
        let mut max_depth = 0;

        for depth in 0..15 {
            let mut next_tubes = Vec::new();
            for tube in &tubes {
                let curr = tube.facet_sequence[tube.facet_sequence.len() - 1];
                for next in 0..data.num_facets {
                    if next == curr { continue; }
                    if data.get_two_face_enriched(curr, next).is_none() { continue; }

                    match extend_tube(tube, next, &data) {
                        Ok(Some(ext)) => {
                            if ext.is_closed() {
                                closed_found += 1;
                                if closed_found <= 3 {
                                    eprintln!("CLOSED tube at depth {}: seq={:?} rot={:.4}",
                                        depth + 1, ext.facet_sequence, ext.rotation);
                                }
                            } else if ext.rotation <= 2.0 && !ext.p_end.is_empty() {
                                next_tubes.push(ext);
                            }
                        }
                        Ok(None) => {}
                        Err(_) => {}
                    }
                }
            }

            if next_tubes.is_empty() && closed_found == 0 {
                eprintln!("No more tubes at depth {}", depth + 1);
                break;
            }
            max_depth = depth + 1;
            tubes = next_tubes;
            if depth < 5 {
                eprintln!("Depth {}: {} tubes (sample rot: {:.4})",
                    depth + 1, tubes.len(),
                    tubes.first().map(|t| t.rotation).unwrap_or(0.0));
            }
        }
        eprintln!("Max depth reached: {}, closed tubes found: {}", max_depth, closed_found);

        // Now test find_closed_orbits on a closed tube
        eprintln!("\n=== Testing find_closed_orbits ===");
        let root = Tube::root(&data.two_faces_enriched[0]);
        // Build the closed tube [1, 0, 4, 5, 1, 0]
        let mut tube = root;
        for &next in &[4, 5, 1, 0] {
            tube = extend_tube(&tube, next, &data).unwrap().unwrap();
        }
        eprintln!("Built tube: {:?}", tube.facet_sequence);
        eprintln!("is_closed: {}", tube.is_closed());
        eprintln!("p_start vertices: {}", tube.p_start.vertices.len());
        eprintln!("p_end vertices: {}", tube.p_end.vertices.len());
        eprintln!("flow_map.matrix:\n{}", tube.flow_map.matrix);
        eprintln!("flow_map.offset: {}", tube.flow_map.offset);

        // Check det(A - I)
        let a_minus_i = tube.flow_map.matrix - nalgebra::Matrix2::identity();
        let det = a_minus_i.determinant();
        eprintln!("det(A - I) = {:.6}", det);

        match tube::find_closed_orbits(&tube) {
            Ok(orbits) => {
                eprintln!("Found {} orbits", orbits.len());
                for (i, (action, fp)) in orbits.iter().enumerate() {
                    eprintln!("  Orbit {}: action={:.4}, fixed_point={}", i, action, fp);
                    eprintln!("    In p_start: {}", tube.p_start.contains(fp));
                }
            }
            Err(e) => eprintln!("find_closed_orbits error: {:?}", e),
        }
    }
}
