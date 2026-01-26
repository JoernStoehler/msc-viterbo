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
                eprintln!("Found {} parabolic fixed points", orbits.len());
                for (i, (action, fp)) in orbits.iter().enumerate() {
                    eprintln!("  Fixed point {}: 2D_action={:.4}, in_p_start={}, in_p_end={}",
                        i, action, tube.p_start.contains(fp), tube.p_end.contains(fp));

                    // Verify flow_map(fp) = fp
                    let mapped = tube.flow_map.apply(fp);
                    let fp_error = (mapped - fp).norm();
                    eprintln!("    |flow_map(fp) - fp| = {:.2e}", fp_error);

                    // Try reconstruction
                    match tube::reconstruct_orbit(fp, &tube, &data) {
                        Ok(orbit) => eprintln!("    Reconstructed period: {:.4}", orbit.period),
                        Err(e) => eprintln!("    Reconstruction error: {}", e),
                    }
                }
            }
            Err(e) => eprintln!("find_closed_orbits error: {:?}", e),
        }
    }

    /// Test the Mahler-type capacity bound: c(K) · c(K°) ≥ 4 for centrally symmetric K.
    ///
    /// The tesseract and 16-cell (cross-polytope) are polar duals.
    /// We verify that c(tesseract) · c(16-cell) = 4, achieving the conjectured equality.
    ///
    /// References:
    /// - c(tesseract) = 4.0: Haim-Kislev 2019, Example 4.6; Rudolf 2022, Example 3.5
    /// - c(16-cell) = 1.0: Computed by tube algorithm (not independently verified)
    #[test]
    fn test_mahler_type_capacity_bound() {
        use hk2017::{hk2017_capacity, Hk2017Config, PolytopeHRep as HkPolytopeHRep};
        use nalgebra::Vector4;

        // Construct tesseract [-1, 1]^4 using hk2017 types
        let tesseract = HkPolytopeHRep::new(
            vec![
                Vector4::new( 1.0,  0.0,  0.0,  0.0),
                Vector4::new(-1.0,  0.0,  0.0,  0.0),
                Vector4::new( 0.0,  1.0,  0.0,  0.0),
                Vector4::new( 0.0, -1.0,  0.0,  0.0),
                Vector4::new( 0.0,  0.0,  1.0,  0.0),
                Vector4::new( 0.0,  0.0, -1.0,  0.0),
                Vector4::new( 0.0,  0.0,  0.0,  1.0),
                Vector4::new( 0.0,  0.0,  0.0, -1.0),
            ],
            vec![1.0; 8],
        );

        // Compute c(tesseract) via HK2017 algorithm
        let hk_config = Hk2017Config::default();
        let tesseract_result = hk2017_capacity(&tesseract, &hk_config)
            .expect("HK2017 should compute tesseract capacity");
        let c_tesseract = tesseract_result.capacity;

        // Compute c(16-cell) via tube algorithm
        let cross_polytope = fixtures::unit_cross_polytope();
        let cross_result = tube_capacity(&cross_polytope)
            .expect("Tube algorithm should compute cross-polytope capacity");
        let c_cross = cross_result.capacity;

        // Verify individual capacities
        assert!(
            (c_tesseract - 4.0).abs() < 1e-6,
            "c(tesseract) = {} (expected 4.0)",
            c_tesseract
        );
        assert!(
            (c_cross - 1.0).abs() < 1e-6,
            "c(16-cell) = {} (expected 1.0)",
            c_cross
        );

        // Verify Mahler-type bound: c(K) · c(K°) ≥ 4
        let product = c_tesseract * c_cross;
        assert!(
            product >= 4.0 - 1e-6,
            "Mahler-type bound violated: c(tesseract) · c(16-cell) = {} < 4",
            product
        );

        // Verify equality (conjectured for cube/cross-polytope duality)
        assert!(
            (product - 4.0).abs() < 1e-6,
            "Expected equality: c(tesseract) · c(16-cell) = {} (expected 4.0)",
            product
        );

        eprintln!("\n=== Mahler-type capacity bound ===");
        eprintln!("c(tesseract) = {:.6}", c_tesseract);
        eprintln!("c(16-cell) = {:.6}", c_cross);
        eprintln!("Product = {:.6} (conjectured bound: 4)", product);
    }
}
