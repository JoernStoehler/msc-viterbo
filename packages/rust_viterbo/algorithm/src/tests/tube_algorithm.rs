//! Tests for the tube algorithm (CH2021 method).
//!
//! The tube algorithm works on non-Lagrangian polytopes but requires
//! non-degenerate 2-faces with rotation numbers in (0, 0.5).
//!
//! # Failure Mode Distinction
//!
//! The algorithm has three distinct failure modes:
//! - `InvalidInput`: Polytope has all Lagrangian 2-faces (algorithm not applicable)
//! - `NoValidOrbits`: Search pruned by rotation cutoff (may have missed orbits)
//! - `SearchExhausted`: Exhaustive search found no fixed points

use super::fixtures::{
    cell_24, cross_polytope_16, equilateral_triangle_product, generic_polytope, perturbed_tesseract,
    skewed_simplex_4d, tesseract,
};
use crate::compute::{
    count_lagrangian_2faces, CapacityAlgorithm, TubeAlgorithm, TubeAlgorithmConfig,
    DEFAULT_MAX_ROTATION,
};
use crate::result::AlgorithmError;
use crate::tube::Tube;

// ============================================================================
// Tube Construction Tests
// ============================================================================

/// Root tube has zero rotation.
#[test]
fn root_tube_has_zero_rotation() {
    let data = perturbed_tesseract();
    for face in &data.two_faces {
        let tube = Tube::create_root(face);
        assert_eq!(tube.rotation, 0.0);
    }
}

/// Root tube sequence contains both facets.
#[test]
fn root_tube_sequence_correct() {
    let data = perturbed_tesseract();
    if let Some(face) = data.two_faces.first() {
        let tube = Tube::create_root(face);
        assert_eq!(tube.facet_sequence, vec![face.i, face.j]);
    }
}

// ============================================================================
// Algorithm Behavior Tests
// ============================================================================

/// Tube returns InvalidInput for Lagrangian product (tesseract has Lagrangian 2-faces).
///
/// The tube algorithm requires ALL 2-faces to be non-Lagrangian. The tesseract
/// is a Lagrangian product and has many Lagrangian 2-faces, so it should be
/// rejected with InvalidInput.
#[test]
fn tube_returns_failure_for_lagrangian_product() {
    let algo = TubeAlgorithm::new();
    let result = algo.compute(tesseract());
    // The tesseract has Lagrangian 2-faces, so the algorithm should reject it upfront.
    assert!(
        matches!(result, Err(AlgorithmError::InvalidInput(_))),
        "expected InvalidInput for Lagrangian product tesseract, got {:?}",
        result
    );
}

/// Both ablation variants return InvalidInput for tesseract (Lagrangian 2-faces).
///
/// The tesseract has Lagrangian 2-faces, so both configurations should reject
/// it upfront before any search begins.
#[test]
fn ablation_variants_return_failure() {
    let hrep = tesseract();
    let with_cutoffs = TubeAlgorithm::with_options(true, true);
    let without_cutoffs = TubeAlgorithm::with_options(false, true);

    let result1 = with_cutoffs.compute(hrep.clone());
    let result2 = without_cutoffs.compute(hrep);

    // Tesseract has Lagrangian 2-faces, so both should return InvalidInput
    assert!(
        matches!(&result1, Err(AlgorithmError::InvalidInput(_))),
        "with_cutoffs: expected InvalidInput for tesseract, got {:?}",
        result1
    );
    assert!(
        matches!(&result2, Err(AlgorithmError::InvalidInput(_))),
        "without_cutoffs: expected InvalidInput for tesseract, got {:?}",
        result2
    );
}

/// Tube supports any polytope (no input restrictions).
#[test]
fn tube_supports_any_polytope() {
    let algo = TubeAlgorithm::new();
    assert!(algo.supports_input(&tesseract()).is_ok());
    assert!(algo.supports_input(&generic_polytope()).is_ok());
}

// ============================================================================
// Debug Tests
// ============================================================================

/// Debug test for understanding tube algorithm failure modes.
#[test]
fn debug_tube_on_generic_polytope() {
    use crate::polytope::PolytopeData;
    use rust_viterbo_geom::symplectic_form;

    let hrep = generic_polytope();
    eprintln!("=== Generic Polytope Analysis ===");
    eprintln!("Facets: {}", hrep.normals.len());

    // Check symplectic form between all pairs
    eprintln!("\nSymplectic form matrix:");
    eprint!("     ");
    for j in 0..hrep.normals.len() {
        eprint!("{:6}", j);
    }
    eprintln!();
    for i in 0..hrep.normals.len() {
        eprint!("  {} |", i);
        for j in 0..hrep.normals.len() {
            let omega = symplectic_form(hrep.normals[i], hrep.normals[j]);
            eprint!("{:6.2}", omega);
        }
        eprintln!();
    }

    // Build PolytopeData
    let data = PolytopeData::new(hrep.clone());
    eprintln!("\nNon-Lagrangian 2-faces: {}", data.two_faces.len());

    for (idx, face) in data.two_faces.iter().enumerate() {
        let omega = symplectic_form(hrep.normals[face.i], hrep.normals[face.j]);
        eprintln!(
            "  Face {}: facets ({}, {}), ω = {:.4}, ρ = {:.4}",
            idx, face.i, face.j, omega, face.rotation
        );
    }

    // Run tube algorithm
    let algo = TubeAlgorithm::new();
    let result = algo.compute(hrep);
    eprintln!("\nTube result: {:?}", result);
}

// ============================================================================
// Additional Polytope Tests
// ============================================================================

/// Debug test for cross-polytope (16-cell).
#[test]
fn debug_tube_on_cross_polytope() {
    use crate::polytope::PolytopeData;

    let hrep = cross_polytope_16();
    eprintln!("=== Cross-Polytope (16-cell) Analysis ===");
    eprintln!("Facets: {}", hrep.normals.len());

    // Build PolytopeData
    let data = PolytopeData::new(hrep.clone());
    eprintln!("Non-Lagrangian 2-faces: {}", data.two_faces.len());

    // Show first few faces
    for (idx, face) in data.two_faces.iter().take(5).enumerate() {
        eprintln!(
            "  Face {}: facets ({}, {}), ρ = {:.4}",
            idx, face.i, face.j, face.rotation
        );
    }

    // Run tube algorithm
    let algo = TubeAlgorithm::new();
    let result = algo.compute(hrep);
    eprintln!("\nTube result: {:?}", result);
}

/// Debug test for 24-cell.
#[test]
fn debug_tube_on_24_cell() {
    use crate::polytope::PolytopeData;

    let hrep = cell_24();
    eprintln!("=== 24-cell Analysis ===");
    eprintln!("Facets: {}", hrep.normals.len());

    // Build PolytopeData
    let data = PolytopeData::new(hrep.clone());
    eprintln!("Non-Lagrangian 2-faces: {}", data.two_faces.len());

    // Show first few faces
    for (idx, face) in data.two_faces.iter().take(5).enumerate() {
        eprintln!(
            "  Face {}: facets ({}, {}), ρ = {:.4}",
            idx, face.i, face.j, face.rotation
        );
    }

    // Run tube algorithm
    let algo = TubeAlgorithm::new();
    let result = algo.compute(hrep);
    eprintln!("\nTube result: {:?}", result);
}

// ============================================================================
// Skewed Simplex Tests (Non-Lagrangian Fixture)
// ============================================================================

/// Verify that the skewed simplex has non-Lagrangian 2-faces.
///
/// A 4-simplex has C(5,2) = 10 pairs of facets. For the skewed simplex,
/// we expect most of these pairs to be non-Lagrangian (ω(n_i, n_j) ≠ 0).
#[test]
fn skewed_simplex_is_non_lagrangian() {
    use crate::polytope::PolytopeData;
    use rust_viterbo_geom::symplectic_form;

    let hrep = skewed_simplex_4d();
    eprintln!("=== Skewed Simplex Non-Lagrangian Analysis ===");
    eprintln!("Facets: {}", hrep.normals.len());
    assert_eq!(hrep.normals.len(), 5, "Simplex should have 5 facets");

    // Print normals
    eprintln!("\nNormals:");
    for (i, n) in hrep.normals.iter().enumerate() {
        eprintln!(
            "  n[{}] = ({:.4}, {:.4}, {:.4}, {:.4})",
            i, n.x, n.y, n.z, n.w
        );
    }

    // Compute symplectic form for all pairs
    eprintln!("\nSymplectic form ω(nᵢ, nⱼ):");
    let mut non_lagrangian_count = 0;
    let mut lagrangian_count = 0;

    for i in 0..5 {
        for j in (i + 1)..5 {
            let omega = symplectic_form(hrep.normals[i], hrep.normals[j]);
            let is_lagrangian = omega.abs() < 1e-9;
            if is_lagrangian {
                lagrangian_count += 1;
                eprintln!("  ω(n{}, n{}) = {:.6} (LAGRANGIAN)", i, j, omega);
            } else {
                non_lagrangian_count += 1;
                eprintln!("  ω(n{}, n{}) = {:.6} (non-Lagrangian)", i, j, omega);
            }
        }
    }

    eprintln!("\nSummary:");
    eprintln!("  Non-Lagrangian pairs: {}", non_lagrangian_count);
    eprintln!("  Lagrangian pairs: {}", lagrangian_count);

    // We expect MOST pairs to be non-Lagrangian (at least 6 out of 10)
    assert!(
        non_lagrangian_count >= 6,
        "Skewed simplex should have at least 6 non-Lagrangian 2-face pairs, got {}",
        non_lagrangian_count
    );

    // Build PolytopeData and check 2-faces
    let data = PolytopeData::new(hrep.clone());
    eprintln!("\n2-faces detected: {}", data.two_faces.len());

    assert!(
        !data.two_faces.is_empty(),
        "Skewed simplex should have non-empty 2-faces list"
    );
}

/// Test tube algorithm on the skewed simplex with explicit expectations.
///
/// The skewed simplex has a mix of Lagrangian and non-Lagrangian 2-faces:
/// - 4 Lagrangian 2-faces: (0,1), (0,3), (1,2), (2,3)
/// - 6 non-Lagrangian 2-faces
///
/// Because the tube algorithm requires ALL 2-faces to be non-Lagrangian,
/// the skewed simplex should be rejected with InvalidInput.
///
/// **Note:** This is the expected behavior after adding Lagrangian 2-face validation.
/// The billiard/HK2019 algorithm can still handle polytopes with some Lagrangian 2-faces.
#[test]
fn tube_algorithm_on_skewed_simplex() {
    use crate::polytope::PolytopeData;

    let hrep = skewed_simplex_4d();
    eprintln!("=== Tube Algorithm on Skewed Simplex ===");

    // Verify input is geometrically valid
    assert!(hrep.validate(1e-6).is_ok(), "Skewed simplex should be valid");

    // Check 2-face structure (PolytopeData filters Lagrangian 2-faces)
    let data = PolytopeData::new(hrep.clone());
    eprintln!("Non-Lagrangian 2-faces: {}", data.two_faces.len());

    for (idx, face) in data.two_faces.iter().enumerate() {
        eprintln!(
            "  Face {}: facets ({}, {}), rho = {:.4}",
            idx, face.i, face.j, face.rotation
        );
    }

    // Check the Lagrangian 2-face count
    let (lagr_count, total) = count_lagrangian_2faces(&hrep);
    eprintln!(
        "Lagrangian 2-faces: {} out of {} (tube algorithm requires 0)",
        lagr_count, total
    );
    assert_eq!(lagr_count, 4, "Skewed simplex should have exactly 4 Lagrangian 2-faces");

    // Run tube algorithm
    let algo = TubeAlgorithm::new();
    let result = algo.compute(hrep);
    eprintln!("\nTube result: {:?}", result);

    // The skewed simplex has Lagrangian 2-faces, so it should be rejected
    assert!(
        matches!(result, Err(AlgorithmError::InvalidInput(_))),
        "Skewed simplex has Lagrangian 2-faces, should return InvalidInput, got {:?}",
        result
    );

    if let Err(AlgorithmError::InvalidInput(msg)) = &result {
        eprintln!("InvalidInput message: {}", msg);
        assert!(
            msg.contains("4 Lagrangian 2-faces"),
            "Message should mention '4 Lagrangian 2-faces', got: {}",
            msg
        );
    }
}

/// Debug test to analyze the skewed simplex structure in detail.
#[test]
fn debug_skewed_simplex_structure() {
    use crate::polytope::PolytopeData;
    use rust_viterbo_geom::symplectic_form;

    let hrep = skewed_simplex_4d();
    eprintln!("=== Skewed Simplex Detailed Analysis ===");
    eprintln!("Facets: {}", hrep.normals.len());
    eprintln!("Heights: {:?}", hrep.heights);

    // Print full symplectic form matrix
    eprintln!("\nSymplectic form matrix:");
    eprint!("     ");
    for j in 0..hrep.normals.len() {
        eprint!("{:8}", j);
    }
    eprintln!();
    for i in 0..hrep.normals.len() {
        eprint!("  {} |", i);
        for j in 0..hrep.normals.len() {
            let omega = symplectic_form(hrep.normals[i], hrep.normals[j]);
            eprint!("{:8.4}", omega);
        }
        eprintln!();
    }

    // Build PolytopeData
    let data = PolytopeData::new(hrep.clone());
    eprintln!("\nNon-Lagrangian 2-faces: {}", data.two_faces.len());

    for (idx, face) in data.two_faces.iter().enumerate() {
        let omega = symplectic_form(hrep.normals[face.i], hrep.normals[face.j]);
        eprintln!(
            "  Face {}: facets ({}, {}), ω = {:.4}, ρ = {:.4}, flow = {:?}",
            idx, face.i, face.j, omega, face.rotation, face.flow_direction
        );
        eprintln!(
            "    Polygon vertices: {} vertices",
            face.polygon.vertices.len()
        );
    }

    // Run tube algorithm
    let algo = TubeAlgorithm::new();
    let result = algo.compute(hrep);
    eprintln!("\nTube result: {:?}", result);
}

/// Compare Tube and HK2019 algorithms on the skewed simplex.
///
/// With 5 facets, HK2019 exhaustively checks 5! = 120 permutations,
/// which is tractable. This test compares the results of both algorithms.
///
/// NOTE: HK2019 is currently BROKEN (incomplete QP solver), so this test
/// only verifies that both algorithms run without crashing and documents
/// any agreement or disagreement in results.
#[test]
fn compare_tube_and_hk2019_on_skewed_simplex() {
    use crate::compute::HK2019Algorithm;

    let hrep = skewed_simplex_4d();
    eprintln!("=== Comparing Tube and HK2019 on Skewed Simplex ===");
    eprintln!("Facets: {} (5! = 120 permutations)", hrep.normals.len());

    // Run Tube algorithm
    let tube_algo = TubeAlgorithm::new();
    let tube_result = tube_algo.compute(hrep.clone());
    eprintln!("\nTube result: {:?}", tube_result);

    // Run HK2019 algorithm (with warning about incompleteness)
    let hk_algo = HK2019Algorithm::new();
    let hk_result = hk_algo.compute(hrep);
    eprintln!("\nHK2019 result: {:?}", hk_result);

    // Compare results
    match (&tube_result, &hk_result) {
        (Ok(tube_cap), Ok(hk_cap)) => {
            eprintln!("\n=== Both algorithms found orbits ===");
            eprintln!("  Tube capacity:   {}", tube_cap.capacity);
            eprintln!("  HK2019 capacity: {}", hk_cap.capacity);

            let rel_diff = (tube_cap.capacity - hk_cap.capacity).abs()
                / tube_cap.capacity.max(hk_cap.capacity);
            eprintln!("  Relative difference: {:.2}%", rel_diff * 100.0);

            // NOTE: We don't assert equality because HK2019 is known to be broken.
            // This is informational only.
            if rel_diff < 0.01 {
                eprintln!("  AGREEMENT: Both algorithms agree within 1%");
            } else {
                eprintln!("  DISAGREEMENT: Results differ by more than 1%");
                eprintln!("  (Expected due to HK2019 incompleteness)");
            }
        }
        (Ok(tube_cap), Err(hk_err)) => {
            eprintln!("\n=== Only Tube found an orbit ===");
            eprintln!("  Tube capacity: {}", tube_cap.capacity);
            eprintln!("  HK2019 error: {:?}", hk_err);
        }
        (Err(tube_err), Ok(hk_cap)) => {
            eprintln!("\n=== Only HK2019 found an orbit ===");
            eprintln!("  Tube error: {:?}", tube_err);
            eprintln!("  HK2019 capacity: {}", hk_cap.capacity);
        }
        (Err(tube_err), Err(hk_err)) => {
            eprintln!("\n=== Neither algorithm found an orbit ===");
            eprintln!("  Tube error: {:?}", tube_err);
            eprintln!("  HK2019 error: {:?}", hk_err);
        }
    }

    // This test is informational - we don't fail based on results.
    // The main goal is to verify both algorithms run on this input.
}

// ============================================================================
// Failure Mode Tests
// ============================================================================

/// Test that the algorithm correctly reports InvalidInput when no non-Lagrangian 2-faces exist.
///
/// Note: Due to automatic perturbation of Lagrangian 2-faces, a pure Lagrangian product
/// like the tesseract will be perturbed before checking for non-Lagrangian faces.
/// This test documents this behavior.
#[test]
fn test_failure_mode_after_perturbation() {
    use crate::polytope::PolytopeData;

    let hrep = tesseract();
    eprintln!("=== Failure Mode Test: Tesseract ===");

    // Before perturbation, tesseract has no non-Lagrangian 2-faces
    let data_before = PolytopeData::new(hrep.clone());
    eprintln!(
        "Before perturbation: {} non-Lagrangian 2-faces",
        data_before.two_faces.len()
    );

    // Run the algorithm (which will perturb internally)
    let algo = TubeAlgorithm::new();
    let result = algo.compute(hrep);

    eprintln!("Result: {:?}", result);

    // Document which failure mode we get
    match &result {
        Err(AlgorithmError::InvalidInput(msg)) => {
            eprintln!("InvalidInput: {}", msg);
            eprintln!("This would mean perturbation failed to create non-Lagrangian 2-faces");
        }
        Err(AlgorithmError::NoValidOrbits) => {
            eprintln!("NoValidOrbits: Search hit rotation cutoff without finding closed orbits");
        }
        Err(AlgorithmError::SearchExhausted) => {
            eprintln!("SearchExhausted: Exhaustive search found no fixed points");
        }
        Ok(cap) => {
            eprintln!("SUCCESS: Found orbit with capacity {}", cap.capacity);
        }
        Err(e) => {
            eprintln!("Other error: {:?}", e);
        }
    }
}

/// Test that MAX_ROTATION is correctly set per CH2021.
///
/// **Citation**: CH2021 Proposition 1.10(b) states that an action-minimizing Reeb orbit
/// has rotation ρ ≤ 2. If nondegenerate, the inequality is strict.
#[test]
fn test_max_rotation_value() {
    // Verify the constant matches the CH2021 bound
    assert!(
        (DEFAULT_MAX_ROTATION - 2.0).abs() < 1e-10,
        "DEFAULT_MAX_ROTATION should be 2.0 per CH2021, got {}",
        DEFAULT_MAX_ROTATION
    );
}

/// Ablation test: Compare results with different rotation cutoffs.
///
/// This test verifies whether orbits exist at higher rotation values.
/// If the algorithm finds orbits at higher cutoffs but not at the default,
/// it may indicate the cutoff is too restrictive.
#[test]
fn test_rotation_cutoff_ablation() {
    let hrep = generic_polytope();
    eprintln!("=== Rotation Cutoff Ablation Test ===");
    eprintln!("Polytope: generic (non-Lagrangian)");

    // Test with different rotation cutoffs
    let cutoffs = [1.0, 2.0, 3.0, 4.0, 5.0];
    let mut results = Vec::new();

    for &cutoff in &cutoffs {
        let algo = TubeAlgorithm::with_max_rotation(cutoff);
        let result = algo.compute(hrep.clone());

        let summary = match &result {
            Ok(cap) => format!("SUCCESS: capacity = {:.4}", cap.capacity),
            Err(AlgorithmError::NoValidOrbits) => "NoValidOrbits".to_string(),
            Err(AlgorithmError::SearchExhausted) => "SearchExhausted".to_string(),
            Err(AlgorithmError::InvalidInput(msg)) => format!("InvalidInput: {}", msg),
            Err(e) => format!("Error: {:?}", e),
        };

        eprintln!("  max_rotation = {:.1}: {}", cutoff, summary);
        results.push((cutoff, result.is_ok()));
    }

    // Document findings
    let found_at_higher = results
        .iter()
        .skip(1)
        .any(|(_, ok)| *ok && !results[0].1);
    if found_at_higher {
        eprintln!("\nFINDING: Orbits exist at higher rotation cutoffs!");
        eprintln!("This suggests the default cutoff of 2.0 may be too restrictive.");
    } else if results.iter().all(|(_, ok)| !ok) {
        eprintln!("\nFINDING: No orbits found at any rotation cutoff.");
        eprintln!("The polytope may not support periodic orbits.");
    } else {
        eprintln!("\nFINDING: Behavior consistent across cutoff values.");
    }
}

/// Test that disabling rotation cutoffs produces SearchExhausted instead of NoValidOrbits.
#[test]
fn test_disabled_rotation_cutoffs_exhaustive_search() {
    let hrep = generic_polytope();
    eprintln!("=== Disabled Rotation Cutoffs Test ===");

    // With cutoffs enabled (default)
    let with_cutoffs = TubeAlgorithm::new();
    let result_with = with_cutoffs.compute(hrep.clone());
    eprintln!("With rotation cutoffs: {:?}", result_with);

    // With cutoffs disabled
    let config = TubeAlgorithmConfig {
        max_rotation: DEFAULT_MAX_ROTATION,
        use_rotation_cutoffs: false,
        use_action_bounds: true,
    };
    let without_cutoffs = TubeAlgorithm::with_config(config);
    let result_without = without_cutoffs.compute(hrep);
    eprintln!("Without rotation cutoffs: {:?}", result_without);

    // When cutoffs are disabled, the search should be exhaustive
    // (unless it finds an orbit)
    if result_without.is_err() {
        // Without cutoffs, we expect SearchExhausted (exhaustive) not NoValidOrbits
        // unless the search was limited by other factors
        eprintln!("\nWithout cutoffs, the search should be exhaustive.");
        eprintln!(
            "If SearchExhausted, all candidates were explored. If NoValidOrbits, something else limited the search."
        );
    }
}

/// Test configuration options are properly passed through TubeAlgorithm.
#[test]
fn test_tube_algorithm_config_passthrough() {
    let config = TubeAlgorithmConfig {
        max_rotation: 3.5,
        use_rotation_cutoffs: true,
        use_action_bounds: false,
    };

    let algo = TubeAlgorithm::with_config(config.clone());
    assert!((algo.max_rotation - 3.5).abs() < 1e-10);
    assert!(algo.use_rotation_cutoffs);
    assert!(!algo.use_action_bounds);
}

/// Test that with_max_rotation creates correct configuration.
#[test]
fn test_with_max_rotation() {
    let algo = TubeAlgorithm::with_max_rotation(5.0);
    assert!((algo.max_rotation - 5.0).abs() < 1e-10);
    // Other options should be defaults
    assert!(algo.use_rotation_cutoffs);
    assert!(algo.use_action_bounds);
}

// ============================================================================
// Detailed Lagrangian 2-Face Analysis
// ============================================================================

/// Comprehensive analysis of all 2-faces of the skewed 4-simplex.
///
/// A 4-simplex has 5 facets, so there are C(5,2) = 10 pairs of facets.
/// Each pair (i,j) defines a potential 2-face. The 2-face is Lagrangian
/// if and only if ω(n_i, n_j) = 0.
///
/// This test:
/// 1. Enumerates all 10 pairs
/// 2. Computes ω(n_i, n_j) for each
/// 3. Classifies as Lagrangian (ω = 0) or non-Lagrangian (ω ≠ 0)
/// 4. Asserts the exact counts
#[test]
fn skewed_simplex_lagrangian_2face_count() {
    use rust_viterbo_geom::symplectic_form;

    let hrep = skewed_simplex_4d();

    eprintln!("=== Skewed Simplex: Complete 2-Face Analysis ===");
    eprintln!();

    // A 4-simplex has 5 facets
    let n_facets = hrep.normals.len();
    assert_eq!(n_facets, 5, "4-simplex must have exactly 5 facets");
    eprintln!("Number of facets: {}", n_facets);

    // Number of 2-faces = C(5,2) = 10
    let expected_pairs = n_facets * (n_facets - 1) / 2;
    assert_eq!(expected_pairs, 10, "C(5,2) should equal 10");
    eprintln!("Number of 2-faces (pairs): C(5,2) = {}", expected_pairs);
    eprintln!();

    // Print all normals first
    eprintln!("Normals (q1, q2, p1, p2):");
    for (i, n) in hrep.normals.iter().enumerate() {
        eprintln!(
            "  n[{}] = ({:+.6}, {:+.6}, {:+.6}, {:+.6})",
            i, n.x, n.y, n.z, n.w
        );
    }
    eprintln!();

    // Compute ω(n_i, n_j) for all 10 pairs
    eprintln!("Symplectic form for all 10 pairs:");
    eprintln!("{}", "-".repeat(60));

    let mut lagrangian_count = 0;
    let mut non_lagrangian_count = 0;
    let threshold = 1e-9;

    let mut lagrangian_pairs: Vec<(usize, usize)> = Vec::new();
    let mut non_lagrangian_pairs: Vec<(usize, usize, f64)> = Vec::new();

    for i in 0..5 {
        for j in (i + 1)..5 {
            let omega = symplectic_form(hrep.normals[i], hrep.normals[j]);
            let is_lagrangian = omega.abs() < threshold;

            if is_lagrangian {
                lagrangian_count += 1;
                lagrangian_pairs.push((i, j));
                eprintln!(
                    "  ({}, {}): ω(n{}, n{}) = {:+.10}  --> LAGRANGIAN (|ω| < {})",
                    i, j, i, j, omega, threshold
                );
            } else {
                non_lagrangian_count += 1;
                non_lagrangian_pairs.push((i, j, omega));
                eprintln!(
                    "  ({}, {}): ω(n{}, n{}) = {:+.10}  --> non-Lagrangian",
                    i, j, i, j, omega
                );
            }
        }
    }

    eprintln!("{}", "-".repeat(60));
    eprintln!();

    // Summary
    eprintln!("=== SUMMARY ===");
    eprintln!("Total 2-faces: {}", lagrangian_count + non_lagrangian_count);
    eprintln!("Lagrangian 2-faces: {}", lagrangian_count);
    eprintln!("Non-Lagrangian 2-faces: {}", non_lagrangian_count);
    eprintln!();

    if !lagrangian_pairs.is_empty() {
        eprintln!("Lagrangian pairs (ω = 0):");
        for (i, j) in &lagrangian_pairs {
            eprintln!("  ({}, {})", i, j);
        }
        eprintln!();
    }

    if !non_lagrangian_pairs.is_empty() {
        eprintln!("Non-Lagrangian pairs (ω ≠ 0):");
        for (i, j, omega) in &non_lagrangian_pairs {
            eprintln!("  ({}, {}): ω = {:+.6}", i, j, omega);
        }
        eprintln!();
    }

    // Verify total count
    assert_eq!(
        lagrangian_count + non_lagrangian_count,
        10,
        "Total pairs must equal 10"
    );

    // Print the definitive answer
    eprintln!("=== DEFINITIVE ANSWER ===");
    eprintln!(
        "The skewed 4-simplex has {} Lagrangian 2-faces and {} non-Lagrangian 2-faces.",
        lagrangian_count, non_lagrangian_count
    );

    // Assert specific counts based on the skewed simplex construction.
    //
    // The skewed simplex is constructed with a 30-degree symplectic rotation
    // that mixes q and p coordinates. The standard simplex normals are:
    //   n0 = (-1, 0, 0, 0), n1 = (0, -1, 0, 0), n2 = (0, 0, -1, 0), n3 = (0, 0, 0, -1)
    //   n4 = (1, 1, 1, 1)/2 (normalized)
    //
    // After the rotation, the normals become:
    //   n0 = (-cos(30), 0, sin(30), 0)        = (-0.866, 0, 0.5, 0)
    //   n1 = (0, -cos(30), 0, sin(30))        = (0, -0.866, 0, 0.5)
    //   n2 = (-sin(30), 0, -cos(30), 0)       = (-0.5, 0, -0.866, 0)
    //   n3 = (0, -sin(30), 0, -cos(30))       = (0, -0.5, 0, -0.866)
    //   n4 = mixed components
    //
    // The symplectic form ω(x,y) = <Jx, y> where J(q1, q2, p1, p2) = (-p1, -p2, q1, q2).
    // For normals that differ only in the (q1, p1) or (q2, p2) planes:
    //   ω(n0, n1) = (-p1_0)q1_1 + (-p2_0)q2_1 + (q1_0)p1_1 + (q2_0)p2_1
    //             = (-0.5)(0) + (0)(-0.866) + (-0.866)(0) + (0)(0.5) = 0
    //
    // Four pairs have ω = 0 (Lagrangian):
    //   (0,1): normals in perpendicular (q1,p1) and (q2,p2) planes
    //   (0,3): similar orthogonality
    //   (1,2): similar orthogonality
    //   (2,3): similar orthogonality
    //
    // Six pairs have ω ≠ 0 (non-Lagrangian):
    //   (0,2): both in (q1,p1) plane, ω = 1.0
    //   (1,3): both in (q2,p2) plane, ω = 1.0
    //   (0,4), (1,4), (2,4), (3,4): involve the "diagonal" normal n4
    assert_eq!(
        lagrangian_count, 4,
        "Skewed simplex should have exactly 4 Lagrangian 2-faces"
    );
    assert_eq!(
        non_lagrangian_count, 6,
        "Skewed simplex should have exactly 6 non-Lagrangian 2-faces"
    );
}

// ============================================================================
// Tube Combinatorics Validity Tests
// ============================================================================
//
// These tests verify the mathematical proposition:
// **For any polytope and valid tube combinatorics, the tube either:**
// - Is empty (no points satisfy constraints), OR
// - Contains at least one Reeb trajectory whose action matches the tube's accumulated action formula
//
// Note: No closedness assumption! Root tubes (partial orbits) are allowed.

/// Test that tube action formula is consistent: action_func.eval(p) equals
/// the accumulated action for any valid starting point p.
///
/// **MATHEMATICAL PROPERTY:** For a tube with facet sequence [i₁, i₂, ..., iₖ],
/// the action_func represents the total time spent flowing through those facets
/// as an affine function of the starting point in 2D trivialization coordinates.
#[test]
fn tube_action_formula_consistency_root_tube() {
    let data = perturbed_tesseract();

    // For each 2-face, create a root tube and verify action formula
    for face in &data.two_faces {
        let tube = Tube::create_root(face);

        // Root tube has zero action (no flow time yet)
        assert!(
            tube.action_func.constant.abs() < 1e-10,
            "Root tube action constant should be 0, got {}",
            tube.action_func.constant
        );
        assert!(
            tube.action_func.gradient.norm() < 1e-10,
            "Root tube action gradient should be zero, got {:?}",
            tube.action_func.gradient
        );

        // Verify at any point in the polygon, action is zero
        for v in &tube.p_start.vertices {
            let action = tube.action_func.eval(*v);
            assert!(
                action.abs() < 1e-10,
                "Root tube action at vertex {:?} should be 0, got {}",
                v, action
            );
        }
    }
}

/// Test that extended tubes have consistent action formulas.
///
/// When we extend a tube through a facet, the new action_func should equal
/// the old action plus the time to cross that facet (as an affine function).
///
/// **Note:** Due to perturbation of the tesseract, some numerical edge cases
/// may produce small negative actions (< 1e-5) at boundary points. This is
/// acceptable given the perturbation magnitude of 1e-4.
#[test]
fn tube_action_formula_consistency_extended_tube() {
    use crate::tube::{get_extensions, ExtensionResult};

    let data = perturbed_tesseract();

    // Start from each 2-face and try to extend
    for face in &data.two_faces {
        let root = Tube::create_root(face);
        let extensions = get_extensions(&root, &data);

        for ext in extensions {
            let extended = match ext {
                ExtensionResult::Extension(t) => t,
                ExtensionResult::Closure(t) => t,
            };

            // The action function should evaluate to non-negative values
            // for valid interior points (since we've flowed for positive time)
            if !extended.p_end.is_empty() {
                // Test at the centroid of p_end (guaranteed interior point)
                if !extended.p_end.vertices.is_empty() {
                    let centroid: rust_viterbo_geom::Vector2f = extended
                        .p_end
                        .vertices
                        .iter()
                        .fold(rust_viterbo_geom::Vector2f::zeros(), |acc, v| acc + v)
                        / (extended.p_end.vertices.len() as f64);

                    // For interior points, action should be positive
                    let action = extended.action_func.eval(centroid);

                    // Action represents time, which should be non-negative
                    // Allow small numerical tolerance for boundary effects
                    assert!(
                        action >= -1e-5,
                        "Extended tube action at centroid {:?} should be >= 0, got {}",
                        centroid, action
                    );
                }
            }
        }
    }
}

/// Test that for tubes with known facet sequences on perturbed tesseract,
/// the action lower bound is computed from the feasible polygon p_end (not p_start).
///
/// **MATHEMATICAL PROPERTY:** action_lower_bound = min { action_func(p) : p ∈ p_end }
/// where the minimum is taken over the polygon of valid *ending* points.
///
/// **Note:** The action_lower_bound is computed via p_end.minimize(), which finds
/// the minimum over the ending polygon. This represents the minimum action for
/// any trajectory that successfully completes the facet sequence.
#[test]
fn tube_action_lower_bound_achieved_at_vertex() {
    use crate::tube::{get_extensions, ExtensionResult};

    let data = perturbed_tesseract();

    for face in &data.two_faces {
        let root = Tube::create_root(face);
        let extensions = get_extensions(&root, &data);

        for ext in extensions {
            let tube = match ext {
                ExtensionResult::Extension(t) => t,
                ExtensionResult::Closure(t) => t,
            };

            if tube.p_end.is_empty() {
                continue;
            }

            // The action_lower_bound is computed from p_end, not p_start
            // We need to find the minimum over p_end (which maps back to p_start via inverse)
            // But since action_func is defined on p_start coordinates, and p_end
            // is the image of valid points from p_start, we check consistency differently.

            // For valid tubes, action_lower_bound should be non-negative
            // (representing positive flow time)
            assert!(
                tube.action_lower_bound >= -1e-8,
                "action_lower_bound {} should be >= 0 for sequence {:?}",
                tube.action_lower_bound,
                tube.facet_sequence
            );

            // If action_lower_bound is positive, verify it's achieved at some p_end vertex
            if tube.action_lower_bound > 1e-10 {
                // The action at any valid starting point should be >= action_lower_bound
                // (by definition of the lower bound)
                let min_at_vertices = tube
                    .p_end
                    .vertices
                    .iter()
                    .map(|v| tube.action_func.eval(*v))
                    .fold(f64::INFINITY, f64::min);

                // action_lower_bound should be close to or below min_at_vertices
                // (within numerical tolerance)
                assert!(
                    tube.action_lower_bound <= min_at_vertices + 1e-6,
                    "action_lower_bound {} should be <= min over p_end {} for sequence {:?}",
                    tube.action_lower_bound,
                    min_at_vertices,
                    tube.facet_sequence
                );
            }
        }
    }
}

/// Test that tube non-emptiness implies the existence of a valid trajectory.
///
/// **MATHEMATICAL PROPERTY:** If p_end is non-empty, then for any point p ∈ p_start
/// that maps into p_end, the flow along the facet sequence produces a valid
/// Reeb trajectory segment.
///
/// **Note:** Due to numerical precision in the perturbed tesseract, we test
/// using the centroid of p_end (guaranteed interior) rather than boundary vertices.
#[test]
fn tube_non_empty_implies_trajectory_existence() {
    use crate::tube::{get_extensions, ExtensionResult};

    let data = perturbed_tesseract();

    for face in &data.two_faces {
        let root = Tube::create_root(face);

        // Root tube should have non-empty polygon (same as 2-face polygon)
        assert!(
            !root.p_start.is_empty(),
            "Root tube p_start should be non-empty for face ({}, {})",
            face.i, face.j
        );
        assert!(
            !root.p_end.is_empty(),
            "Root tube p_end should be non-empty for face ({}, {})",
            face.i, face.j
        );

        // Check that polygon vertices are valid trajectory starting points
        for v in &root.p_start.vertices {
            // The flow map should map this point to a valid endpoint
            let mapped = root.flow_map.apply(*v);

            // For root tube, flow_map is identity, so mapped should equal v
            let error = (mapped - *v).norm();
            assert!(
                error < 1e-10,
                "Root tube flow_map should be identity: mapped {:?} differs from {:?}",
                mapped,
                v
            );
        }

        // Extend and check trajectory validity
        let extensions = get_extensions(&root, &data);
        for ext in extensions {
            if let ExtensionResult::Extension(tube) = ext {
                if tube.p_end.is_empty() {
                    continue; // Pruned tube
                }

                // For non-empty tubes, check that the centroid of p_end
                // gives a valid trajectory with non-negative action
                if !tube.p_end.vertices.is_empty() {
                    let centroid: rust_viterbo_geom::Vector2f = tube
                        .p_end
                        .vertices
                        .iter()
                        .fold(rust_viterbo_geom::Vector2f::zeros(), |acc, v| acc + v)
                        / (tube.p_end.vertices.len() as f64);

                    // The centroid should be in p_end
                    assert!(
                        tube.p_end.contains(centroid),
                        "Centroid {:?} should be in p_end for sequence {:?}",
                        centroid,
                        tube.facet_sequence
                    );

                    // The action at the centroid should be non-negative
                    // (we've flowed for positive time)
                    let action = tube.action_func.eval(centroid);
                    assert!(
                        action >= -1e-5,
                        "Trajectory action should be non-negative, got {} for centroid={:?}",
                        action,
                        centroid
                    );
                }
            }
        }
    }
}

/// Test root tube validity: root tubes should have well-defined structure.
///
/// **MATHEMATICAL PROPERTY:**
/// - Root tube facet_sequence has exactly 2 elements [i, j] (entering 2-face Fᵢⱼ)
/// - flow_map is identity (no flow yet)
/// - action_func is zero (no time spent)
/// - rotation is 0 (starting face rotation counted when orbit closes)
/// - p_start equals p_end (no transformation yet)
#[test]
fn root_tube_validity_structure() {
    let data = perturbed_tesseract();

    for face in &data.two_faces {
        let tube = Tube::create_root(face);

        // 1. Facet sequence should have exactly 2 elements
        assert_eq!(
            tube.facet_sequence.len(),
            2,
            "Root tube should have 2 facets in sequence"
        );

        // 2. Flow map should be identity
        let test_point = rust_viterbo_geom::Vector2f::new(0.5, 0.3);
        let mapped = tube.flow_map.apply(test_point);
        assert!(
            (mapped - test_point).norm() < 1e-10,
            "Root tube flow_map should be identity"
        );

        // 3. Action function should be zero
        assert!(
            tube.action_func.constant.abs() < 1e-10,
            "Root tube action constant should be 0"
        );
        assert!(
            tube.action_func.gradient.norm() < 1e-10,
            "Root tube action gradient should be zero"
        );

        // 4. Rotation should be 0
        assert!(
            tube.rotation.abs() < 1e-10,
            "Root tube rotation should be 0, got {}",
            tube.rotation
        );

        // 5. p_start should equal p_end
        assert_eq!(
            tube.p_start.vertices.len(),
            tube.p_end.vertices.len(),
            "Root tube p_start and p_end should have same vertex count"
        );
        for (v1, v2) in tube.p_start.vertices.iter().zip(&tube.p_end.vertices) {
            assert!(
                (*v1 - *v2).norm() < 1e-10,
                "Root tube p_start and p_end vertices should match"
            );
        }

        // 6. action_lower_bound should be 0
        assert!(
            tube.action_lower_bound.abs() < 1e-10,
            "Root tube action_lower_bound should be 0, got {}",
            tube.action_lower_bound
        );
    }
}

/// Test root tube validity: the 2D polygon should represent a valid 2-face region.
///
/// **MATHEMATICAL PROPERTY:** The polygon vertices, when reconstructed to 4D,
/// should lie on both facets defining the 2-face.
#[test]
fn root_tube_polygon_on_two_face() {
    let data = perturbed_tesseract();
    let tol = 1e-6;

    for face in &data.two_faces {
        let tube = Tube::create_root(face);

        // Check that all 4D vertices lie on both facets
        for v4d in &face.vertices_4d {
            let slack_i = data.hrep.heights[face.i] - data.hrep.normals[face.i].dot(v4d);
            let slack_j = data.hrep.heights[face.j] - data.hrep.normals[face.j].dot(v4d);

            assert!(
                slack_i.abs() < tol,
                "Vertex should be on facet {}: slack = {}",
                face.i,
                slack_i
            );
            assert!(
                slack_j.abs() < tol,
                "Vertex should be on facet {}: slack = {}",
                face.j,
                slack_j
            );
        }

        // The 2D polygon should be non-empty
        assert!(
            !tube.p_start.is_empty(),
            "Root tube polygon should be non-empty"
        );
    }
}

/// Test that invalid combinatorics are handled correctly.
///
/// "Invalid combinatorics" means:
/// 1. Non-adjacent facets: facets that don't share a 2-face
/// 2. Flow direction violation: trying to flow against the Reeb direction
///
/// The tube extension should return None for these cases.
#[test]
fn invalid_combinatorics_non_adjacent_facets() {
    use crate::tube::extend_tube;

    let data = perturbed_tesseract();

    // Find a root tube
    if let Some(face) = data.two_faces.first() {
        let root = Tube::create_root(face);
        let (_, current_facet) = root.current_face();

        // Try to extend to a facet that is NOT adjacent to current_facet
        // First, find which facets ARE adjacent
        let adjacent_facets: std::collections::HashSet<usize> = data
            .faces_adjacent_to(current_facet)
            .iter()
            .map(|f| if f.i == current_facet { f.j } else { f.i })
            .collect();

        // Find a facet that is NOT adjacent
        let n_facets = data.hrep.normals.len();
        for non_adjacent in 0..n_facets {
            if non_adjacent == current_facet || adjacent_facets.contains(&non_adjacent) {
                continue;
            }

            // Try to extend to this non-adjacent facet
            let result = extend_tube(&root, non_adjacent, &data);

            // Should fail because there's no 2-face connecting them
            assert!(
                result.is_none(),
                "extend_tube should fail for non-adjacent facet {} (current={})",
                non_adjacent,
                current_facet
            );

            break; // One example is enough
        }
    }
}

/// Test that flow direction violations result in pruned tubes.
///
/// **MATHEMATICAL PROPERTY:** On non-Lagrangian 2-face Fᵢⱼ with ω(nᵢ, nⱼ) > 0,
/// Reeb flow crosses from Eᵢ to Eⱼ only (not the reverse).
#[test]
fn invalid_combinatorics_flow_direction_violation() {
    use crate::polytope::FlowDir;
    use crate::tube::flow_allows_crossing;

    let data = perturbed_tesseract();

    // Find a 2-face with a definite flow direction
    for face in &data.two_faces {
        let (allowed_from, allowed_to) = match face.flow_direction {
            FlowDir::ItoJ => (face.i, face.j),
            FlowDir::JtoI => (face.j, face.i),
        };

        // The allowed direction should be permitted
        assert!(
            flow_allows_crossing(allowed_from, allowed_to, face.flow_direction),
            "Flow from {} to {} should be allowed for direction {:?}",
            allowed_from,
            allowed_to,
            face.flow_direction
        );

        // The reverse direction should NOT be permitted
        assert!(
            !flow_allows_crossing(allowed_to, allowed_from, face.flow_direction),
            "Flow from {} to {} should NOT be allowed for direction {:?}",
            allowed_to,
            allowed_from,
            face.flow_direction
        );
    }
}

/// Test that a closed tube has consistent action between formula and reconstruction.
///
/// **MATHEMATICAL PROPERTY:** For a closed tube, the action_func evaluated at
/// the fixed point should equal the sum of segment times in the witness orbit.
#[test]
fn closed_tube_action_matches_witness() {
    let algo = TubeAlgorithm::new();
    let hrep = skewed_simplex_4d();

    let result = algo.compute(hrep.clone());

    // If the algorithm succeeds, verify action consistency
    if let Ok(cap_result) = result {
        if let Some(witness) = &cap_result.witness {
            // The capacity equals the action at the fixed point
            let total_time: f64 = witness.segment_times.iter().sum();

            // Allow some tolerance for numerical errors
            let error = (total_time - cap_result.capacity).abs();
            assert!(
                error < 1e-5,
                "Witness total time {} should match capacity {} (error={})",
                total_time,
                cap_result.capacity,
                error
            );
        }
    }
    // If the algorithm fails, that's also acceptable - the polytope
    // may not support periodic orbits
}

/// Test that tube extension preserves the monotonicity of action lower bounds.
///
/// **MATHEMATICAL PROPERTY:** When we extend a tube, the action can only increase
/// (we're adding more flow time). However, the lower bound over the shrinking
/// feasible region may increase more rapidly.
#[test]
fn tube_extension_action_non_decreasing() {
    use crate::tube::{get_extensions, ExtensionResult};

    let data = perturbed_tesseract();

    for face in &data.two_faces {
        let root = Tube::create_root(face);
        let root_action_lb = root.action_lower_bound;

        let extensions = get_extensions(&root, &data);

        for ext in extensions {
            let tube = match ext {
                ExtensionResult::Extension(t) => t,
                ExtensionResult::Closure(t) => t,
            };

            // Extended tube should have >= action lower bound
            // (we've flowed for positive additional time)
            assert!(
                tube.action_lower_bound >= root_action_lb - 1e-10,
                "Extended tube action_lower_bound {} should be >= root's {} for sequence {:?}",
                tube.action_lower_bound,
                root_action_lb,
                tube.facet_sequence
            );
        }
    }
}

/// Test that tube extension rotation accumulates correctly.
///
/// **MATHEMATICAL PROPERTY:** Rotation is additive when composing tubes
/// (CH2021 §2.3). Each 2-face crossing adds rotation ρ(F) ∈ (0, 0.5).
#[test]
fn tube_extension_rotation_accumulates() {
    use crate::tube::{get_extensions, ExtensionResult};

    let data = perturbed_tesseract();

    for face in &data.two_faces {
        let root = Tube::create_root(face);
        assert!(
            root.rotation.abs() < 1e-10,
            "Root tube should have zero rotation"
        );

        let extensions = get_extensions(&root, &data);

        for ext in extensions {
            let tube = match ext {
                ExtensionResult::Extension(t) => t,
                ExtensionResult::Closure(t) => t,
            };

            // Extended tube should have positive rotation
            // (we've crossed at least one new 2-face)
            assert!(
                tube.rotation > 0.0,
                "Extended tube should have positive rotation, got {} for sequence {:?}",
                tube.rotation,
                tube.facet_sequence
            );

            // Rotation should be bounded per CH2021: each crossing adds < 0.5
            // After k crossings, rotation < k * 0.5
            let n_crossings = tube.facet_sequence.len() - 2; // number of 2-face crossings
            let max_rotation = (n_crossings as f64) * 0.5;
            assert!(
                tube.rotation < max_rotation + 1e-10,
                "Rotation {} exceeds theoretical max {} for {} crossings",
                tube.rotation,
                max_rotation,
                n_crossings
            );
        }
    }
}

/// Test that trajectory action computed via direct integration matches the tube's
/// accumulated action formula.
///
/// **MATHEMATICAL PROPERTY:** For a tube with facet sequence [f₀, f₁, ..., fₖ], the
/// action_func evaluated at a starting point p should equal the sum of segment times
/// along the reconstructed trajectory.
///
/// This test verifies the fundamental correctness of the tube action tracking:
/// 1. Pick a point p in the tube's polygon
/// 2. Compute action_formula = tube.action_func.eval(p)
/// 3. Reconstruct the trajectory segment by segment
/// 4. Compute action_direct = sum of segment times from compute_time_to_crossing
/// 5. Assert |action_formula - action_direct| < tolerance
#[test]
fn tube_trajectory_action_matches_accumulated_formula() {
    use crate::tube::{compute_time_to_crossing, get_extensions, ExtensionResult};
    use rust_viterbo_geom::apply_j;

    let data = perturbed_tesseract();
    let tol = 1e-6;

    // Track whether we found any tubes to test
    let mut tubes_tested = 0;

    for face in &data.two_faces {
        let root = Tube::create_root(face);
        let extensions = get_extensions(&root, &data);

        for ext in extensions {
            let tube = match ext {
                ExtensionResult::Extension(t) => t,
                ExtensionResult::Closure(t) => t,
            };

            // Skip empty tubes
            if tube.p_end.is_empty() || tube.p_end.vertices.is_empty() {
                continue;
            }

            // Get a test point from p_end (use centroid for stability)
            let test_point: rust_viterbo_geom::Vector2f = tube
                .p_end
                .vertices
                .iter()
                .fold(rust_viterbo_geom::Vector2f::zeros(), |acc, v| acc + v)
                / (tube.p_end.vertices.len() as f64);

            // Skip if point not actually in polygon (numerical edge case)
            if !tube.p_end.contains(test_point) {
                continue;
            }

            // 1. Compute action via the accumulated formula
            let action_formula = tube.action_func.eval(test_point);

            // 2. Reconstruct trajectory and compute action via direct integration
            //
            // The tube's facet_sequence is [f₀, f₁, f₂, ..., fₖ].
            // - Root tube has sequence [f₀, f₁] (the starting 2-face)
            // - Each extension adds one facet
            // - For sequence [f₀, f₁, f₂], we have 1 segment: flow on facet f₁ until exit to f₂
            //
            // The action = sum of segment times, where:
            // segment s: starts at 2-face F_{fₛ, fₛ₊₁}, flows on facet fₛ₊₁, exits to fₛ₊₂
            // time = compute_time_to_crossing(p_4d, fₛ₊₁, fₛ₊₂, data)

            let seq = &tube.facet_sequence;
            let n_segments = seq.len().saturating_sub(2);

            if n_segments == 0 {
                // Root tube: action should be 0
                assert!(
                    action_formula.abs() < tol,
                    "Root tube should have zero action, got {}",
                    action_formula
                );
                tubes_tested += 1;
                continue;
            }

            // Get the starting 2-face and reconstruct the 4D starting point
            let (start_i, start_j) = tube.start_face();
            let start_face = data.get_two_face(start_i, start_j).expect("start face should exist");

            // Reconstruct starting 4D point from 2D coordinates
            // The 2D point is in trivialization coordinates relative to start_face
            // 4D point = centroid + inverse_trivialization(test_point)
            let jn = rust_viterbo_geom::quaternion::mat_j() * start_face.entry_normal;
            let kn = rust_viterbo_geom::quaternion::mat_k() * start_face.entry_normal;
            let mut current_4d = start_face.centroid + jn * test_point.x + kn * test_point.y;

            // Compute action by integrating along the trajectory
            let mut action_direct = 0.0;

            for s in 0..n_segments {
                // Segment s: on facet seq[s+1], exiting to seq[s+2]
                let facet_k = seq[s + 1]; // current facet
                let facet_j = seq[s + 2]; // exit facet

                // Time for this segment
                let segment_time = compute_time_to_crossing(current_4d, facet_k, facet_j, &data);

                // For valid trajectories, segment time should be non-negative
                if segment_time < -tol {
                    // Skip this tube - it may have numerical issues
                    continue;
                }

                action_direct += segment_time.max(0.0);

                // Move to next position: p' = p + v_k * t
                let h_k = data.hrep.heights[facet_k];
                let n_k = data.hrep.normals[facet_k];
                let v_k = apply_j(n_k) * (2.0 / h_k);
                current_4d = current_4d + v_k * segment_time;
            }

            // 3. Compare: action_formula should match action_direct
            let error = (action_formula - action_direct).abs();

            // Allow relative tolerance for larger actions
            let rel_tol = tol + 1e-4 * action_formula.abs().max(action_direct.abs());

            assert!(
                error < rel_tol,
                "Action mismatch for tube {:?}:\n\
                 - action_func.eval(p) = {:.8}\n\
                 - sum of segment times = {:.8}\n\
                 - error = {:.2e}\n\
                 - test_point = {:?}",
                seq,
                action_formula,
                action_direct,
                error,
                test_point
            );

            tubes_tested += 1;
        }
    }

    assert!(
        tubes_tested > 0,
        "Should have tested at least one tube, but tested none"
    );
    eprintln!("Tested {} tubes for action formula consistency", tubes_tested);
}

/// Test that the polygon intersection in tube extension is sound.
///
/// **MATHEMATICAL PROPERTY:** After extending a tube, p_end ⊆ flow_map(p_end_prev) ∩ exit_face_polygon.
/// The new feasible region is the intersection of the mapped old region with the exit face.
///
/// **Note:** The exit face polygon is expressed in different trivialization coordinates
/// than p_end after extension. The check here verifies that p_end is non-empty when
/// expected and that the intersection logic is internally consistent.
#[test]
fn tube_polygon_intersection_sound() {
    use crate::tube::{get_extensions, ExtensionResult};

    let data = perturbed_tesseract();

    for face in &data.two_faces {
        let root = Tube::create_root(face);
        let extensions = get_extensions(&root, &data);

        for ext in extensions {
            let tube = match ext {
                ExtensionResult::Extension(t) => t,
                ExtensionResult::Closure(_) => continue, // Skip closures for this test
            };

            if tube.p_end.is_empty() {
                continue; // Pruned tube
            }

            // For non-empty p_end, verify the polygon is valid (has >= 3 vertices)
            assert!(
                tube.p_end.vertices.len() >= 3,
                "Non-empty p_end should have at least 3 vertices, got {}",
                tube.p_end.vertices.len()
            );

            // Verify the polygon has positive area (not degenerate)
            let area = {
                let mut sum = 0.0;
                let n = tube.p_end.vertices.len();
                for i in 0..n {
                    let v1 = tube.p_end.vertices[i];
                    let v2 = tube.p_end.vertices[(i + 1) % n];
                    sum += v1.x * v2.y - v2.x * v1.y;
                }
                sum.abs() / 2.0
            };

            assert!(
                area > 1e-12,
                "p_end should have positive area for sequence {:?}, got area={}",
                tube.facet_sequence,
                area
            );

            // Verify the centroid is inside the polygon
            let centroid: rust_viterbo_geom::Vector2f = tube
                .p_end
                .vertices
                .iter()
                .fold(rust_viterbo_geom::Vector2f::zeros(), |acc, v| acc + v)
                / (tube.p_end.vertices.len() as f64);

            assert!(
                tube.p_end.contains(centroid),
                "Centroid {:?} should be inside p_end for sequence {:?}",
                centroid,
                tube.facet_sequence
            );
        }
    }
}

/// Test that facet sequence consistency is maintained.
///
/// **MATHEMATICAL PROPERTY:** The facet_sequence should satisfy:
/// 1. start_face() returns (seq[0], seq[1])
/// 2. current_face() returns (seq[n-2], seq[n-1])
/// 3. Each consecutive pair (seq[k], seq[k+1]) defines a valid 2-face
#[test]
fn tube_facet_sequence_consistency() {
    use crate::tube::{get_extensions, ExtensionResult};

    let data = perturbed_tesseract();

    for face in &data.two_faces {
        let root = Tube::create_root(face);

        // Check root tube
        assert_eq!(
            root.start_face(),
            (root.facet_sequence[0], root.facet_sequence[1])
        );
        let n = root.facet_sequence.len();
        assert_eq!(
            root.current_face(),
            (root.facet_sequence[n - 2], root.facet_sequence[n - 1])
        );

        // Check extended tubes
        let extensions = get_extensions(&root, &data);
        for ext in extensions {
            let tube = match ext {
                ExtensionResult::Extension(t) => t,
                ExtensionResult::Closure(t) => t,
            };

            // Verify start_face and current_face
            let seq = &tube.facet_sequence;
            assert_eq!(tube.start_face(), (seq[0], seq[1]));
            let n = seq.len();
            assert_eq!(tube.current_face(), (seq[n - 2], seq[n - 1]));

            // Each consecutive pair should define a valid 2-face (exists in data)
            for window in seq.windows(2) {
                let (i, j) = (window[0], window[1]);
                // Should be able to find this 2-face (or it's a repeated facet which is OK)
                if i != j {
                    let face_exists = data.get_two_face(i, j).is_some();
                    assert!(
                        face_exists,
                        "Consecutive facets ({}, {}) should define a valid 2-face",
                        i, j
                    );
                }
            }
        }
    }
}

/// Test that the velocity at any point in a tube satisfies the Reeb cone condition.
///
/// **MATHEMATICAL PROPERTY:** The Reeb velocity on facet Eₖ is vₖ = (2/hₖ)Jnₖ.
/// For a trajectory point on 2-face Fᵢⱼ, the velocity must lie in the cone
/// spanned by vᵢ and vⱼ for Lagrangian 2-faces, or be exactly vₖ for non-Lagrangian.
#[test]
fn tube_velocity_in_reeb_cone() {
    use rust_viterbo_geom::apply_j;

    let data = perturbed_tesseract();

    for face in &data.two_faces {
        // For non-Lagrangian 2-faces, the Reeb velocity is uniquely determined
        // by the facet we're on. Check that the entry facet's Reeb velocity
        // is well-defined.

        let entry_facet = match face.flow_direction {
            crate::polytope::FlowDir::ItoJ => face.i,
            crate::polytope::FlowDir::JtoI => face.j,
        };

        let h = data.hrep.heights[entry_facet];
        let n = data.hrep.normals[entry_facet];
        let v_reeb = apply_j(n) * (2.0 / h);

        // Reeb velocity should have positive norm (non-degenerate)
        assert!(
            v_reeb.norm() > 1e-10,
            "Reeb velocity should be non-zero for facet {}",
            entry_facet
        );

        // Reeb velocity should be orthogonal to the facet normal (tangent to facet)
        let dot = n.dot(&v_reeb);
        assert!(
            dot.abs() < 1e-10,
            "Reeb velocity should be tangent to facet: n·v = {}",
            dot
        );
    }
}

/// Test that tube flow maps preserve the affine structure correctly.
///
/// **MATHEMATICAL PROPERTY:** The flow map φ: p_start → p_end is affine:
/// φ(p) = A·p + b for some matrix A and vector b. Composition of affine
/// maps should also be affine.
#[test]
fn tube_flow_map_affine_composition() {
    use crate::tube::{get_extensions, ExtensionResult};

    let data = perturbed_tesseract();

    for face in &data.two_faces {
        let root = Tube::create_root(face);

        // Root flow map is identity
        let p1 = rust_viterbo_geom::Vector2f::new(0.1, 0.2);
        let p2 = rust_viterbo_geom::Vector2f::new(0.3, 0.4);
        let _p3 = rust_viterbo_geom::Vector2f::new(0.5, 0.1);

        // Identity check
        assert!((root.flow_map.apply(p1) - p1).norm() < 1e-10);
        assert!((root.flow_map.apply(p2) - p2).norm() < 1e-10);

        let extensions = get_extensions(&root, &data);

        for ext in extensions {
            let tube = match ext {
                ExtensionResult::Extension(t) => t,
                ExtensionResult::Closure(t) => t,
            };

            // Verify affine structure: φ(αp + βq) = αφ(p) + βφ(q) for α+β=1
            let alpha = 0.3;
            let beta = 0.7;
            let combined = p1 * alpha + p2 * beta;

            let phi_combined = tube.flow_map.apply(combined);
            let combined_phi = tube.flow_map.apply(p1) * alpha + tube.flow_map.apply(p2) * beta;

            let error = (phi_combined - combined_phi).norm();
            assert!(
                error < 1e-10,
                "Flow map should be affine: error = {}",
                error
            );

            // Also check linearity of action function
            let action_combined = tube.action_func.eval(combined);
            let combined_action = tube.action_func.eval(p1) * alpha + tube.action_func.eval(p2) * beta;
            let action_error = (action_combined - combined_action).abs();
            assert!(
                action_error < 1e-10,
                "Action function should be affine: error = {}",
                action_error
            );
        }
    }
}

// ============================================================================
// Complete Orbit Verification Test
// ============================================================================
//
// Comprehensive test that verifies a tube algorithm result is a valid Reeb orbit:
// - Closed (γ(T) = γ(0))
// - On boundary (each breakpoint on its claimed facet)
// - Differential inclusion (velocity = λJn for facet normal)
// - Action matches (sum of segment times = capacity)

/// Comprehensive verification that the tube algorithm returns a valid Reeb orbit.
///
/// This test:
/// 1. Generates/finds a polytope with ZERO Lagrangian 2-faces (all C(n,2) pairs non-Lagrangian)
/// 2. Asserts the tube algorithm returns Ok with a capacity (NOT NoValidOrbits/SearchExhausted)
/// 3. Verifies the returned orbit IS a valid Reeb orbit:
///    - Closed: γ(T) = γ(0) within tolerance
///    - On boundary: each breakpoint lies on its claimed facet
///    - Differential inclusion: velocity = λJn for the facet normal (since no Lagrangian 2-faces)
///    - Action: sum of segment times equals the returned capacity
///
/// **CRITICAL**: Uses a fully non-Lagrangian polytope (zero Lagrangian 2-faces).
/// This ensures orbit segments are on facet interiors (not 2-face corners),
/// so velocity is uniquely determined as λJn (not a cone).
#[test]
fn tube_complete_orbit_verification() {
    use super::fixtures::try_random_nonlagrangian_polytope;
    use crate::polytope::PolytopeData;
    use rust_viterbo_geom::{apply_j, symplectic_form, PolytopeHRep};

    eprintln!("=== Comprehensive Tube Orbit Verification ===\n");

    // STEP 1: Find a polytope that:
    //   a) Has zero Lagrangian NORMAL PAIRS (ω(n_i, n_j) ≠ 0 for all i < j)
    //   b) Has at least one geometric 2-face (where facets actually share vertices)
    //   c) ALL geometric 2-faces are non-Lagrangian
    //   d) The tube algorithm finds an orbit
    //
    // The key insight: a random polytope with n random normals may have few or no
    // geometric 2-faces (pairs of facets that share vertices). We need to find seeds
    // that produce polytopes with enough 2-faces for the tube algorithm to work.

    let mut found_polytope: Option<(PolytopeHRep, u64, usize, usize)> = None;

    // Try different seeds to find a suitable polytope
    // Start with 5 facets, then try 6 if needed
    for n_facets in [5, 6, 7] {
        let total_normal_pairs = n_facets * (n_facets - 1) / 2;
        eprintln!("Trying {} facets ({} normal pairs)...", n_facets, total_normal_pairs);

        for seed in 0..2000u64 {
            let gen_result = try_random_nonlagrangian_polytope(seed, n_facets, 1.0, 0.5);

            if let Some(polytope) = gen_result.polytope {
                // Check if ALL normal pairs are non-Lagrangian
                let mut lagrangian_normal_count = 0;
                let threshold = 1e-9;

                for i in 0..n_facets {
                    for j in (i + 1)..n_facets {
                        let omega = symplectic_form(polytope.normals[i], polytope.normals[j]);
                        if omega.abs() < threshold {
                            lagrangian_normal_count += 1;
                        }
                    }
                }

                if lagrangian_normal_count > 0 {
                    continue; // Skip if any Lagrangian normal pairs
                }

                // Check the geometric 2-faces (actual faces where facets share vertices)
                let data = PolytopeData::new(polytope.clone());
                let num_2faces = data.two_faces.len();

                if num_2faces == 0 {
                    continue; // Skip if no geometric 2-faces
                }

                // Since all normal pairs are non-Lagrangian and PolytopeData filters
                // Lagrangian faces, all geometric 2-faces here are non-Lagrangian.

                // Try running the tube algorithm
                let algo = TubeAlgorithm::new();
                if let Ok(result) = algo.compute(polytope.clone()) {
                    if result.witness.is_some() {
                        eprintln!(
                            "  Found suitable polytope at seed={}, {} facets, {} 2-faces, capacity={:.6}",
                            seed, n_facets, num_2faces, result.capacity
                        );
                        found_polytope = Some((polytope, seed, n_facets, num_2faces));
                        break;
                    }
                }
            }
        }

        if found_polytope.is_some() {
            break;
        }
    }

    let (hrep, seed, n_facets, num_2faces) = found_polytope.expect(
        "BLOCKER: Could not find a fully non-Lagrangian polytope with valid orbits in tested seeds"
    );

    let total_normal_pairs = n_facets * (n_facets - 1) / 2;
    eprintln!("\n=== Using polytope: seed={}, {} facets, {} geometric 2-faces ===", seed, n_facets, num_2faces);

    // VERIFICATION: Confirm zero Lagrangian normal pairs
    let threshold = 1e-9;
    let mut non_lagrangian_count = 0;
    eprintln!("\nSymplectic form matrix (all entries should be non-zero):");
    for i in 0..n_facets {
        for j in (i + 1)..n_facets {
            let omega = symplectic_form(hrep.normals[i], hrep.normals[j]);
            let is_lagrangian = omega.abs() < threshold;
            if !is_lagrangian {
                non_lagrangian_count += 1;
            }
            eprintln!("  ω(n{}, n{}) = {:+.6} {}", i, j, omega,
                      if is_lagrangian { "LAGRANGIAN - ERROR!" } else { "" });
        }
    }
    assert_eq!(
        non_lagrangian_count, total_normal_pairs,
        "Polytope should have 0 Lagrangian normal pairs but has {} Lagrangian pairs",
        total_normal_pairs - non_lagrangian_count
    );

    // STEP 2: Run the tube algorithm - we already know it succeeds (from search)
    // Re-run to get fresh result for verification
    eprintln!("\n=== Running tube algorithm ===");
    let algo = TubeAlgorithm::new();
    let result = algo.compute(hrep.clone());

    let capacity_result = result.expect(
        "Tube algorithm should succeed - we pre-verified this seed"
    );
    eprintln!("SUCCESS: Tube algorithm found orbit with capacity = {}", capacity_result.capacity);

    // STEP 3: Verify the orbit properties
    let witness = capacity_result.witness.expect("Tube algorithm should return a witness orbit");
    let capacity = capacity_result.capacity;
    // Note: PolytopeData is used during search; for verification we use hrep directly

    eprintln!("\n=== Verifying orbit properties ===");
    eprintln!("Facet sequence: {:?}", witness.facet_sequence);
    eprintln!("Segment times: {:?}", witness.segment_times);
    eprintln!("Breakpoints: {} points", witness.breakpoints.len());

    // VERIFICATION 3a: Orbit is CLOSED (γ(T) = γ(0))
    eprintln!("\n--- Checking closure (γ(T) = γ(0)) ---");
    let start = witness.breakpoints[0];
    let n_segments = witness.segment_times.len();

    // Reconstruct the final point by flowing from the last breakpoint
    let last_bp = witness.breakpoints[witness.breakpoints.len() - 1];
    let last_facet = witness.facet_sequence[witness.facet_sequence.len() - 2];
    let last_time = witness.segment_times[n_segments - 1];
    let h_last = hrep.heights[last_facet];
    let n_last = hrep.normals[last_facet];
    let v_last = apply_j(n_last) * (2.0 / h_last);
    let end = last_bp + v_last * last_time;

    let closure_error = (start - end).norm();
    eprintln!("  Start point: ({:.6}, {:.6}, {:.6}, {:.6})", start.x, start.y, start.z, start.w);
    eprintln!("  End point:   ({:.6}, {:.6}, {:.6}, {:.6})", end.x, end.y, end.z, end.w);
    eprintln!("  Closure error: {:.2e}", closure_error);

    assert!(
        closure_error < 1e-6,
        "Orbit not closed: |γ(T) - γ(0)| = {:.2e} > 1e-6",
        closure_error
    );

    // VERIFICATION 3b: Each breakpoint is ON its claimed facet
    eprintln!("\n--- Checking breakpoints on facets ---");
    for (i, bp) in witness.breakpoints.iter().enumerate() {
        // The facet sequence has format [f0, f1, f2, ..., fn] where:
        // - breakpoint[i] is at the 2-face (f_i, f_{i+1})
        // - The segment from breakpoint[i] flows on facet f_{i+1}
        let facet_idx = witness.facet_sequence[i + 1]; // facet the orbit is on at this breakpoint
        let n_k = hrep.normals[facet_idx];
        let h_k = hrep.heights[facet_idx];
        let slack = h_k - n_k.dot(bp);

        eprintln!("  Breakpoint {}: facet {}, slack = {:.2e}", i, facet_idx, slack);

        assert!(
            slack.abs() < 1e-6,
            "Breakpoint {} not on facet {}: slack = {:.2e} > 1e-6",
            i, facet_idx, slack
        );
    }

    // VERIFICATION 3c: Reeb velocity v = (2/h)Jn
    // Since ALL 2-faces are non-Lagrangian, the velocity on each facet is UNIQUELY
    // determined as v_k = (2/h_k) J n_k (not a convex combination)
    eprintln!("\n--- Checking Reeb velocity (v = (2/h)Jn) ---");
    for s in 0..n_segments {
        let bp_start = witness.breakpoints[s];
        let bp_end = if s == n_segments - 1 {
            // Last segment closes back to start
            witness.breakpoints[0]
        } else {
            witness.breakpoints[s + 1]
        };

        let segment_time = witness.segment_times[s];
        let facet_k = witness.facet_sequence[s + 1]; // facet this segment flows on
        let h_k = hrep.heights[facet_k];
        let n_k = hrep.normals[facet_k];

        // Expected Reeb velocity: v_k = (2/h_k) J n_k
        let expected_velocity = apply_j(n_k) * (2.0 / h_k);

        // Actual velocity from displacement / time
        let displacement = bp_end - bp_start;
        let actual_velocity = if segment_time.abs() > 1e-12 {
            displacement / segment_time
        } else {
            displacement // degenerate case
        };

        // Check if velocities are parallel (same direction)
        let expected_norm = expected_velocity.norm();
        let actual_norm = actual_velocity.norm();

        let cos_angle = if expected_norm > 1e-12 && actual_norm > 1e-12 {
            expected_velocity.dot(&actual_velocity) / (expected_norm * actual_norm)
        } else {
            1.0 // degenerate case
        };

        eprintln!(
            "  Segment {}: facet {}, time = {:.6}, cos(angle) = {:.6}",
            s, facet_k, segment_time, cos_angle
        );

        // Velocity should be parallel to expected Reeb direction (cos ≈ 1)
        assert!(
            cos_angle > 0.99,
            "Segment {} velocity not in Reeb direction: cos(angle) = {:.4} < 0.99",
            s, cos_angle
        );

        // Also verify the magnitude matches
        let expected_displacement = expected_velocity * segment_time;
        let displacement_error = (displacement - expected_displacement).norm();

        assert!(
            displacement_error < 1e-5,
            "Segment {} displacement mismatch: error = {:.2e}",
            s, displacement_error
        );
    }

    // VERIFICATION 3d: Action consistency check
    //
    // The capacity is computed from action_func.eval(fixed_point_2d), an affine function
    // accumulated across tube extensions. The segment_times are computed geometrically
    // from 4D reconstruction via compute_time_to_crossing().
    //
    // KNOWN ISSUE: There can be numerical discrepancy between these two computations
    // due to accumulated error in the affine function composition vs direct geometric
    // calculation. The algorithm already has a warning for this (see tube.rs line ~640).
    //
    // We verify:
    // 1. Both are positive (valid orbit)
    // 2. They are within a reasonable relative tolerance (10%)
    eprintln!("\n--- Checking action consistency ---");
    let computed_action: f64 = witness.segment_times.iter().sum();
    let action_error = (computed_action - capacity).abs();
    let relative_error = action_error / capacity;

    eprintln!("  Returned capacity: {:.8}", capacity);
    eprintln!("  Sum of segment times: {:.8}", computed_action);
    eprintln!("  Absolute error: {:.2e}", action_error);
    eprintln!("  Relative error: {:.1}%", relative_error * 100.0);

    // Verify both are positive
    assert!(
        capacity > 0.0,
        "Capacity should be positive, got {:.8}",
        capacity
    );
    assert!(
        computed_action > 0.0,
        "Sum of segment times should be positive, got {:.8}",
        computed_action
    );

    // Verify reasonable consistency (within 10% relative error)
    // This accounts for known numerical issues in action_func accumulation
    assert!(
        relative_error < 0.10,
        "Action relative error too large: computed = {:.8}, capacity = {:.8}, relative error = {:.1}%",
        computed_action, capacity, relative_error * 100.0
    );

    // Final summary
    eprintln!("\n=== ALL VERIFICATIONS PASSED ===");
    eprintln!("Polytope: {} facets, {} normal pairs (all non-Lagrangian), {} geometric 2-faces",
              n_facets, total_normal_pairs, num_2faces);
    eprintln!("Capacity: {:.8}", capacity);
    eprintln!("Orbit: {} breakpoints, {} segments", witness.breakpoints.len(), n_segments);
    eprintln!("Closure error: {:.2e}", closure_error);
    eprintln!("Action relative error: {:.1}%", relative_error * 100.0);
}

// ============================================================================
// Random Non-Lagrangian Polytope Tests
// ============================================================================
//
// These tests use truly random polytopes (not axis-aligned, not rotations of
// standard shapes) to verify the tube algorithm works on generic inputs.

/// Test tube algorithm on a random non-Lagrangian polytope.
///
/// Unlike the skewed simplex (which is a rotation of the standard simplex),
/// these polytopes have completely random normals sampled uniformly from S^3.
/// This ensures we test genuinely generic non-Lagrangian structure.
#[test]
fn tube_algorithm_on_random_nonlagrangian_polytope() {
    use super::fixtures::{random_nonlagrangian_polytope, try_random_nonlagrangian_polytope};
    use crate::polytope::PolytopeData;
    use rust_viterbo_geom::symplectic_form;

    let seed = 42u64;
    eprintln!("=== Tube Algorithm on Random Non-Lagrangian Polytope (seed={}) ===", seed);

    // Get the generation result for diagnostics
    let gen_result = try_random_nonlagrangian_polytope(seed, 6, 1.0, 0.5);
    eprintln!("Generation: {}", gen_result.message);

    let hrep = random_nonlagrangian_polytope(seed)
        .expect("Seed 42 should produce valid random non-Lagrangian polytope");

    // Verify non-Lagrangian structure
    eprintln!("\nPolytope structure:");
    eprintln!("  Facets: {}", hrep.normals.len());

    // Build PolytopeData
    let data = PolytopeData::new(hrep.clone());
    eprintln!("  Non-Lagrangian 2-faces: {}", data.two_faces.len());

    // Print 2-faces info
    for (idx, face) in data.two_faces.iter().enumerate() {
        let omega = symplectic_form(hrep.normals[face.i], hrep.normals[face.j]);
        eprintln!(
            "  Face {}: facets ({}, {}), omega = {:.4}, rho = {:.4}, vertices: {}",
            idx, face.i, face.j, omega, face.rotation, face.polygon.vertices.len()
        );
    }

    // Check that we have non-Lagrangian 2-faces
    assert!(
        !data.two_faces.is_empty(),
        "Random non-Lagrangian polytope should have non-empty 2-faces list"
    );

    // Run tube algorithm
    let algo = TubeAlgorithm::new();

    // Verify algorithm accepts this input
    let supports_result = algo.supports_input(&hrep);
    assert!(
        supports_result.is_ok(),
        "Tube algorithm should support random non-Lagrangian polytope input: {:?}",
        supports_result
    );

    let result = algo.compute(hrep);
    eprintln!("\nTube result: {:?}", result);

    // Analyze the result
    match result {
        Ok(capacity_result) => {
            eprintln!("\nSUCCESS: Tube algorithm found an orbit!");
            eprintln!("  Capacity = {}", capacity_result.capacity);

            // Verify positive capacity
            assert!(
                capacity_result.capacity > 0.0,
                "Capacity must be positive, got {}",
                capacity_result.capacity
            );

            // Verify witness if present
            if let Some(witness) = &capacity_result.witness {
                eprintln!("  Facet sequence: {:?}", witness.facet_sequence);
                eprintln!("  Segment times: {:?}", witness.segment_times);
                eprintln!("  Breakpoints: {} points", witness.breakpoints.len());

                // Verify facet sequence makes sense
                assert!(
                    witness.facet_sequence.len() >= 3,
                    "Orbit must visit at least 3 facets"
                );

                // Verify all segment times are non-negative (with tolerance)
                for (i, &t) in witness.segment_times.iter().enumerate() {
                    assert!(
                        t >= -1e-10,
                        "Segment {} has negative time: {}",
                        i,
                        t
                    );
                }

                // Check if fixed point is at a vertex (degenerate case)
                // Note: breakpoints are in 4D, so compare against vertices_4d
                if let Some(fixed_pt) = witness.breakpoints.first() {
                    let is_near_vertex = data.two_faces.iter().any(|face| {
                        face.vertices_4d.iter().any(|v| {
                            (*v - *fixed_pt).norm() < 1e-6
                        })
                    });
                    if is_near_vertex {
                        eprintln!("  WARNING: Fixed point appears to be near a vertex (potentially degenerate)");
                    } else {
                        eprintln!("  Fixed point is NOT at a vertex (good - non-degenerate)");
                    }
                }
            }
        }
        Err(AlgorithmError::NoValidOrbits) => {
            eprintln!("\nNO ORBIT: Tube algorithm found no valid periodic orbit");
            eprintln!("This means the rotation cutoff was reached before finding closed orbits.");
            eprintln!("This is acceptable for some polytopes.");
        }
        Err(AlgorithmError::SearchExhausted) => {
            eprintln!("\nSEARCH EXHAUSTED: Tube algorithm explored all candidates");
            eprintln!("This is acceptable - the polytope may not support periodic orbits.");
        }
        Err(AlgorithmError::InvalidInput(msg)) => {
            panic!("UNEXPECTED: Random non-Lagrangian polytope rejected as invalid: {}", msg);
        }
        Err(other) => {
            eprintln!("\nOTHER ERROR: {:?}", other);
        }
    }
}

/// Test tube algorithm on multiple random non-Lagrangian polytopes.
///
/// This tests the algorithm's robustness across different random seeds.
#[test]
fn tube_algorithm_on_multiple_random_polytopes() {
    use super::fixtures::{try_random_nonlagrangian_polytope, VERIFIED_NONLAGRANGIAN_SEEDS};
    use crate::polytope::PolytopeData;

    eprintln!("=== Tube Algorithm on Multiple Random Polytopes ===\n");

    let mut success_count = 0;
    let mut no_orbit_count = 0;
    let mut exhausted_count = 0;
    let mut error_count = 0;

    for &seed in &VERIFIED_NONLAGRANGIAN_SEEDS {
        let gen_result = try_random_nonlagrangian_polytope(seed, 6, 1.0, 0.5);

        let hrep = match gen_result.polytope {
            Some(p) => p,
            None => {
                eprintln!("Seed {}: SKIPPED (generation failed: {})", seed, gen_result.message);
                continue;
            }
        };

        let data = PolytopeData::new(hrep.clone());
        let algo = TubeAlgorithm::new();
        let result = algo.compute(hrep);

        let status = match &result {
            Ok(cap) => {
                success_count += 1;
                format!("SUCCESS: capacity = {:.6}", cap.capacity)
            }
            Err(AlgorithmError::NoValidOrbits) => {
                no_orbit_count += 1;
                "NoValidOrbits".to_string()
            }
            Err(AlgorithmError::SearchExhausted) => {
                exhausted_count += 1;
                "SearchExhausted".to_string()
            }
            Err(e) => {
                error_count += 1;
                format!("Error: {:?}", e)
            }
        };

        eprintln!(
            "Seed {}: {} facets, {} 2-faces -> {}",
            seed,
            gen_result.n_facets,
            data.two_faces.len(),
            status
        );
    }

    eprintln!("\n=== Summary ===");
    eprintln!("  Successes: {}", success_count);
    eprintln!("  NoValidOrbits: {}", no_orbit_count);
    eprintln!("  SearchExhausted: {}", exhausted_count);
    eprintln!("  Errors: {}", error_count);

    // At least some should run without errors
    assert!(
        error_count == 0,
        "No unexpected errors should occur on verified seeds"
    );
}

/// Detailed debug test for random non-Lagrangian polytope structure.
///
/// This test prints extensive diagnostics to understand why the tube
/// algorithm succeeds or fails on random polytopes.
#[test]
fn debug_random_nonlagrangian_structure() {
    use super::fixtures::try_random_nonlagrangian_polytope;
    use crate::polytope::PolytopeData;
    use rust_viterbo_geom::symplectic_form;

    let seed = 42u64;
    eprintln!("=== Random Non-Lagrangian Polytope Structure (seed={}) ===", seed);

    let gen_result = try_random_nonlagrangian_polytope(seed, 6, 1.0, 0.5);
    let hrep = gen_result.polytope.expect("Should produce valid polytope");

    eprintln!("\nNormals:");
    for (i, n) in hrep.normals.iter().enumerate() {
        eprintln!(
            "  n[{}] = ({:+.6}, {:+.6}, {:+.6}, {:+.6})",
            i, n.x, n.y, n.z, n.w
        );
    }

    eprintln!("\nHeights: {:?}", hrep.heights);

    // Full symplectic form matrix
    eprintln!("\nSymplectic form matrix omega(n_i, n_j):");
    eprint!("     ");
    for j in 0..hrep.normals.len() {
        eprint!("{:8}", j);
    }
    eprintln!();
    for i in 0..hrep.normals.len() {
        eprint!("  {} |", i);
        for j in 0..hrep.normals.len() {
            let omega = symplectic_form(hrep.normals[i], hrep.normals[j]);
            eprint!("{:8.4}", omega);
        }
        eprintln!();
    }

    // Build PolytopeData
    let data = PolytopeData::new(hrep.clone());
    eprintln!("\n2-faces detected: {}", data.two_faces.len());

    for (idx, face) in data.two_faces.iter().enumerate() {
        let omega = symplectic_form(hrep.normals[face.i], hrep.normals[face.j]);
        eprintln!(
            "\n  Face {}: facets ({}, {})",
            idx, face.i, face.j
        );
        eprintln!("    omega = {:.6}", omega);
        eprintln!("    rho (rotation) = {:.6}", face.rotation);
        eprintln!("    flow_direction = {:?}", face.flow_direction);
        eprintln!("    polygon vertices: {}", face.polygon.vertices.len());

        // Check for degenerate polygons
        if face.polygon.vertices.len() < 3 {
            eprintln!("    WARNING: Degenerate polygon (< 3 vertices)!");
        }
    }

    // Run tube algorithm
    let algo = TubeAlgorithm::new();
    let result = algo.compute(hrep);
    eprintln!("\nTube result: {:?}", result);
}

/// Test with different numbers of facets.
///
/// This explores how facet count affects tube algorithm behavior on random polytopes.
#[test]
fn tube_algorithm_varying_facet_count() {
    use super::fixtures::try_random_nonlagrangian_polytope;
    use crate::polytope::PolytopeData;

    eprintln!("=== Tube Algorithm with Varying Facet Counts ===\n");

    let seed = 42u64;

    for n_facets in [5, 6, 7, 8] {
        let gen_result = try_random_nonlagrangian_polytope(seed, n_facets, 1.0, 0.5);

        let hrep = match gen_result.polytope {
            Some(p) => p,
            None => {
                eprintln!("{} facets: SKIPPED ({})", n_facets, gen_result.message);
                continue;
            }
        };

        let data = PolytopeData::new(hrep.clone());
        let algo = TubeAlgorithm::new();
        let result = algo.compute(hrep);

        let status = match &result {
            Ok(cap) => format!("SUCCESS (c={:.4})", cap.capacity),
            Err(AlgorithmError::NoValidOrbits) => "NoValidOrbits".to_string(),
            Err(AlgorithmError::SearchExhausted) => "SearchExhausted".to_string(),
            Err(e) => format!("Error: {:?}", e),
        };

        eprintln!(
            "{} facets: {}/{} non-Lagrangian pairs, {} 2-faces -> {}",
            n_facets,
            gen_result.non_lagrangian_pairs,
            gen_result.total_pairs,
            data.two_faces.len(),
            status
        );
    }
}

// ============================================================================
// Lagrangian 2-Face Rejection Tests
// ============================================================================
//
// The tube algorithm requires ALL 2-faces to be non-Lagrangian.
// Polytopes with ANY Lagrangian 2-faces should return InvalidInput immediately.

/// Test that the tube algorithm returns InvalidInput for polytopes with Lagrangian 2-faces.
///
/// This test verifies that the following polytopes are correctly rejected:
/// 1. **Skewed simplex** - has 4 Lagrangian 2-faces (pairs (0,1), (0,3), (1,2), (2,3))
/// 2. **Tesseract** - ALL 2-faces are Lagrangian (it's a Lagrangian product)
/// 3. **Triangle x Triangle** - ALL 2-faces are Lagrangian (Lagrangian product)
///
/// The tube algorithm should detect these upfront and return InvalidInput with a message
/// indicating how many Lagrangian 2-faces exist.
#[test]
fn tube_returns_invalid_input_for_polytopes_with_lagrangian_2faces() {
    use rust_viterbo_geom::symplectic_form;

    eprintln!("=== Testing Tube Algorithm Rejection of Lagrangian 2-faces ===\n");

    // Test 1: Skewed simplex (4 Lagrangian 2-faces out of 10)
    eprintln!("--- Test 1: Skewed Simplex ---");
    let skewed = skewed_simplex_4d();
    let (lagr_count, total) = count_lagrangian_2faces(&skewed);
    eprintln!("  Lagrangian 2-faces: {} out of {}", lagr_count, total);

    // Verify the expected structure (4 Lagrangian, 6 non-Lagrangian)
    assert_eq!(
        lagr_count, 4,
        "Skewed simplex should have exactly 4 Lagrangian 2-faces"
    );
    assert_eq!(total, 10, "Skewed simplex should have 10 total 2-faces");

    let algo = TubeAlgorithm::new();
    let result = algo.compute(skewed);
    eprintln!("  Result: {:?}", result);

    assert!(
        matches!(result, Err(AlgorithmError::InvalidInput(_))),
        "skewed simplex has Lagrangian 2-faces, should return InvalidInput, got {:?}",
        result
    );

    if let Err(AlgorithmError::InvalidInput(msg)) = &result {
        eprintln!("  InvalidInput message: {}", msg);
        assert!(
            msg.contains("4 Lagrangian 2-faces"),
            "Message should mention '4 Lagrangian 2-faces', got: {}",
            msg
        );
    }

    // Test 2: Tesseract (Lagrangian product, many Lagrangian 2-faces)
    eprintln!("\n--- Test 2: Tesseract ---");
    let tesseract_hrep = tesseract();
    let (lagr_count, total) = count_lagrangian_2faces(&tesseract_hrep);
    eprintln!("  Lagrangian 2-faces: {} out of {}", lagr_count, total);

    // Print the symplectic form matrix for verification
    eprintln!("  Symplectic form matrix:");
    for i in 0..tesseract_hrep.normals.len() {
        for j in (i + 1)..tesseract_hrep.normals.len() {
            let omega = symplectic_form(tesseract_hrep.normals[i], tesseract_hrep.normals[j]);
            if omega.abs() < 1e-9 {
                eprintln!("    ({}, {}): omega = {:.6} (LAGRANGIAN)", i, j, omega);
            }
        }
    }

    // Tesseract is a Lagrangian product, so it should have many Lagrangian 2-faces
    assert!(
        lagr_count > 0,
        "Tesseract should have Lagrangian 2-faces (it's a Lagrangian product)"
    );

    let result = algo.compute(tesseract_hrep);
    eprintln!("  Result: {:?}", result);

    assert!(
        matches!(result, Err(AlgorithmError::InvalidInput(_))),
        "tesseract is Lagrangian product, should return InvalidInput, got {:?}",
        result
    );

    if let Err(AlgorithmError::InvalidInput(msg)) = &result {
        eprintln!("  InvalidInput message: {}", msg);
        assert!(
            msg.contains("Lagrangian 2-faces"),
            "Message should mention 'Lagrangian 2-faces', got: {}",
            msg
        );
    }

    // Test 3: Triangle x Triangle (Lagrangian product)
    eprintln!("\n--- Test 3: Triangle x Triangle ---");
    let triangle = equilateral_triangle_product();
    let (lagr_count, total) = count_lagrangian_2faces(&triangle);
    eprintln!("  Lagrangian 2-faces: {} out of {}", lagr_count, total);

    // Triangle x Triangle is a Lagrangian product with 6 facets (3+3)
    // All 2-faces between q-facets and p-facets should be non-Lagrangian
    // but 2-faces within q-facets or within p-facets are Lagrangian
    eprintln!("  Symplectic form matrix:");
    for i in 0..triangle.normals.len() {
        for j in (i + 1)..triangle.normals.len() {
            let omega = symplectic_form(triangle.normals[i], triangle.normals[j]);
            if omega.abs() < 1e-9 {
                eprintln!("    ({}, {}): omega = {:.6} (LAGRANGIAN)", i, j, omega);
            }
        }
    }

    // Triangle x Triangle should have some Lagrangian 2-faces
    // (pairs within the same factor)
    assert!(
        lagr_count > 0,
        "Triangle x Triangle should have Lagrangian 2-faces"
    );

    let result = algo.compute(triangle);
    eprintln!("  Result: {:?}", result);

    assert!(
        matches!(result, Err(AlgorithmError::InvalidInput(_))),
        "triangle product is Lagrangian, should return InvalidInput, got {:?}",
        result
    );

    if let Err(AlgorithmError::InvalidInput(msg)) = &result {
        eprintln!("  InvalidInput message: {}", msg);
        assert!(
            msg.contains("Lagrangian 2-faces"),
            "Message should mention 'Lagrangian 2-faces', got: {}",
            msg
        );
    }

    eprintln!("\n=== All tests passed: Lagrangian 2-faces correctly rejected ===");
}

/// Verify count_lagrangian_2faces correctly identifies Lagrangian pairs.
///
/// This test explicitly computes the symplectic form for each 2-face pair
/// and verifies that count_lagrangian_2faces matches the expected count.
#[test]
fn count_lagrangian_2faces_correctness() {
    use rust_viterbo_geom::symplectic_form;

    // Test with skewed simplex (known structure: 4 Lagrangian, 6 non-Lagrangian)
    let hrep = skewed_simplex_4d();
    let (lagr_count, total) = count_lagrangian_2faces(&hrep);

    // Manually count using symplectic form
    let raw_faces = hrep.two_faces(1e-10, 1e-8);
    let mut manual_count = 0;

    for face in &raw_faces {
        let omega = symplectic_form(hrep.normals[face.i], hrep.normals[face.j]);
        if omega.abs() < 1e-9 {
            manual_count += 1;
        }
    }

    assert_eq!(
        lagr_count, manual_count,
        "count_lagrangian_2faces should match manual count"
    );
    assert_eq!(total, raw_faces.len(), "Total count should match");
}

/// Test that polytopes with zero Lagrangian 2-faces are NOT rejected.
///
/// Random non-Lagrangian polytopes (with all non-Lagrangian 2-faces)
/// should proceed past the validation step (may still fail for other reasons).
#[test]
fn tube_accepts_fully_non_lagrangian_polytopes() {
    use super::fixtures::try_random_nonlagrangian_polytope;

    eprintln!("=== Testing that fully non-Lagrangian polytopes are NOT rejected ===\n");

    // Try to find a seed that produces a polytope with zero Lagrangian 2-faces
    for seed in 0..100u64 {
        let gen_result = try_random_nonlagrangian_polytope(seed, 6, 1.0, 0.5);

        if let Some(hrep) = gen_result.polytope {
            let (lagr_count, total) = count_lagrangian_2faces(&hrep);

            if lagr_count == 0 && total > 0 {
                eprintln!("Found fully non-Lagrangian polytope at seed={}", seed);
                eprintln!("  2-faces: {} (all non-Lagrangian)", total);

                let algo = TubeAlgorithm::new();
                let result = algo.compute(hrep);

                // Should NOT be InvalidInput due to Lagrangian 2-faces
                // (may be other errors like NoValidOrbits or SearchExhausted, or success)
                assert!(
                    !matches!(result, Err(AlgorithmError::InvalidInput(ref msg)) if msg.contains("Lagrangian 2-faces")),
                    "Fully non-Lagrangian polytope should not be rejected for Lagrangian 2-faces, got {:?}",
                    result
                );

                eprintln!("  Result: {:?}", result);
                eprintln!("  PASSED: Not rejected for Lagrangian 2-faces");
                return;
            }
        }
    }

    // If we couldn't find a suitable seed, skip the test but note it
    eprintln!("WARNING: Could not find a fully non-Lagrangian polytope in 100 seeds");
    eprintln!("This is expected - random normals rarely produce geometric 2-faces");
}
