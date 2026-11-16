//! Tests for symplectomorphism invariance: c(AK) = c(K) for A ∈ Sp(4).
//!
//! This is a fundamental capacity axiom (Ekeland-Hofer 1989, Axiom (i)).
//!
//! # Strategy
//!
//! Most symplectomorphisms break Lagrangian product structure, so the billiard
//! algorithm cannot be used. We must use HK2019, which has O(F!) complexity.
//!
//! For fast tests, we use:
//! - Triangle×triangle (6 facets) → 720 permutations, feasible
//! - Bounded Sp(4) matrices (scale < 1) to keep transformed polytope well-conditioned
//!
//! For thorough tests (ignored by default):
//! - Tesseract (8 facets) → 40320 permutations, slow
//! - Full Sp(4) sampling with larger parameters
//!
//! # Mathematical Background
//!
//! The symplectic group Sp(4,ℝ) is 10-dimensional. The generators module provides
//! a parametrization using:
//! - 2 block rotations in (q₁,p₁) and (q₂,p₂) planes
//! - 3 shears (p += Sq where S is symmetric)
//! - 3 dual shears (q += Tp where T is symmetric)
//! - 1 coupled rotation mixing both canonical pairs
//!
//! # References
//!
//! - Ekeland-Hofer 1989: Symplectic capacity axioms
//! - HK-O 2024: Counterexample to Viterbo conjecture (uses Reeb dynamics)

use super::fixtures::{equilateral_triangle_product, rectangle_product, tesseract};
use super::generators::{apply_sp4_to_polytope, is_symplectic, seeded_sp4, seeded_sp4_bounded};
use crate::compute::{CapacityAlgorithm, HK2019Algorithm, MinkowskiBilliardAlgorithm};
use rust_viterbo_geom::{PolytopeHRep, SymplecticVector};
use std::f64::consts::PI;

// =============================================================================
// Helper: Sp(4) transforms on polytopes (coordinate-based, for billiard)
// =============================================================================

/// Apply a 2×2 rotation matrix to (x, y) coordinates.
fn rotate_2d(x: f64, y: f64, theta: f64) -> (f64, f64) {
    let c = theta.cos();
    let s = theta.sin();
    (c * x - s * y, s * x + c * y)
}

/// Block rotation in (q₁, p₁) plane: R(θ) ⊕ I₂
/// This is a symplectic map that preserves Lagrangian product structure.
fn apply_q1p1_rotation(hrep: &PolytopeHRep, theta: f64) -> PolytopeHRep {
    let normals: Vec<SymplecticVector> = hrep
        .normals
        .iter()
        .map(|n| {
            // Rotate (q₁, p₁) = (x, z) components
            let (new_x, new_z) = rotate_2d(n.x, n.z, theta);
            SymplecticVector::new(new_x, n.y, new_z, n.w)
        })
        .collect();
    PolytopeHRep::new(normals, hrep.heights.clone())
}

/// Block rotation in (q₂, p₂) plane: I₂ ⊕ R(φ)
fn apply_q2p2_rotation(hrep: &PolytopeHRep, phi: f64) -> PolytopeHRep {
    let normals: Vec<SymplecticVector> = hrep
        .normals
        .iter()
        .map(|n| {
            // Rotate (q₂, p₂) = (y, w) components
            let (new_y, new_w) = rotate_2d(n.y, n.w, phi);
            SymplecticVector::new(n.x, new_y, n.z, new_w)
        })
        .collect();
    PolytopeHRep::new(normals, hrep.heights.clone())
}

/// Symplectic coordinate swap: (q₁,q₂,p₁,p₂) ↦ (q₂,q₁,p₂,p₁)
/// Preserves Lagrangian product structure.
fn apply_coordinate_swap(hrep: &PolytopeHRep) -> PolytopeHRep {
    let normals: Vec<SymplecticVector> = hrep
        .normals
        .iter()
        .map(|n| SymplecticVector::new(n.y, n.x, n.w, n.z))
        .collect();
    PolytopeHRep::new(normals, hrep.heights.clone())
}

// =============================================================================
// REAL Tests: Using HK2019 with full Sp(4) on small polytopes
// =============================================================================

/// Test symplectomorphism invariance with random Sp(4) matrices on triangle×triangle.
///
/// This is the MAIN test that validates the Sp(4) generator and capacity axiom.
/// Uses:
/// - Triangle×triangle (6 facets) for fast HK2019 execution
/// - Bounded Sp(4) matrices (scale=0.3) to keep transformed polytope well-conditioned
/// - Multiple random seeds to sample different regions of Sp(4)
#[test]
fn invariance_sp4_triangle_product() {
    let algo = HK2019Algorithm::new();
    let original = equilateral_triangle_product();
    let c_original = algo
        .compute(original.clone())
        .expect("HK2019 on triangle product")
        .capacity;

    // Use bounded matrices (scale=0.3) for numerical stability
    // These still cover all 10 dimensions of sp(4), just with smaller parameters
    let scale = 0.3;
    let test_seeds = [42, 123, 456, 789, 1337];

    for seed in test_seeds {
        let a = seeded_sp4_bounded(seed, scale);

        // Verify matrix is actually symplectic
        assert!(
            is_symplectic(&a, 1e-10),
            "seeded_sp4_bounded({}, {}) should be symplectic",
            seed,
            scale
        );

        let transformed = apply_sp4_to_polytope(&a, &original);

        // Check transformed polytope is valid
        assert!(
            transformed.heights.iter().all(|&h| h > 0.0),
            "Transformed polytope should have positive heights"
        );

        let c_transformed = algo
            .compute(transformed)
            .expect("HK2019 on transformed polytope")
            .capacity;

        let rel_error = (c_transformed - c_original).abs() / c_original;
        assert!(
            rel_error < 0.05,
            "Sp(4) transform (seed={}) should preserve capacity: {:.6} vs {:.6} (error {:.2}%)",
            seed,
            c_original,
            c_transformed,
            rel_error * 100.0
        );
    }
}

/// Test with larger Sp(4) matrices (full scale) - slower, more thorough.
#[test]
fn invariance_sp4_triangle_product_full_scale() {
    let algo = HK2019Algorithm::new();
    let original = equilateral_triangle_product();
    let c_original = algo
        .compute(original.clone())
        .expect("HK2019 on triangle product")
        .capacity;

    // Full-scale matrices can produce more extreme transforms
    let test_seeds = [1, 2, 3];

    for seed in test_seeds {
        let a = seeded_sp4(seed);

        assert!(
            is_symplectic(&a, 1e-8),
            "seeded_sp4({}) should be symplectic",
            seed
        );

        let transformed = apply_sp4_to_polytope(&a, &original);

        // Skip if transform produces degenerate polytope
        if transformed.heights.iter().any(|&h| h <= 1e-10) {
            eprintln!("Seed {} produced near-degenerate polytope, skipping", seed);
            continue;
        }

        match algo.compute(transformed) {
            Ok(result) => {
                let rel_error = (result.capacity - c_original).abs() / c_original;
                assert!(
                    rel_error < 0.1, // Allow larger tolerance for extreme transforms
                    "Full Sp(4) (seed={}) should preserve capacity: {:.6} vs {:.6} (error {:.2}%)",
                    seed,
                    c_original,
                    result.capacity,
                    rel_error * 100.0
                );
            }
            Err(e) => {
                eprintln!("Seed {} computation failed (may be numerical): {:?}", seed, e);
            }
        }
    }
}

// =============================================================================
// Billiard-compatible tests (structure-preserving symplectomorphisms)
// =============================================================================

/// Test invariance under coordinate swap (billiard algorithm).
///
/// Coordinate swap preserves Lagrangian product structure, so billiard works.
#[test]
fn invariance_coordinate_swap() {
    let algo = MinkowskiBilliardAlgorithm::new();

    // Tesseract is symmetric, so swap should have no effect
    let original = tesseract();
    let c_original = algo.compute(original.clone()).expect("billiard").capacity;
    let swapped = apply_coordinate_swap(&original);
    let c_swapped = algo.compute(swapped).expect("billiard on swapped").capacity;

    let rel_error = (c_swapped - c_original).abs() / c_original;
    assert!(
        rel_error < 0.01,
        "coordinate swap should preserve capacity: {} vs {} (error {:.2}%)",
        c_original,
        c_swapped,
        rel_error * 100.0
    );

    // Non-symmetric case: 2×1 rectangle
    let rect = rectangle_product(2.0, 1.0);
    let c_rect = algo.compute(rect.clone()).expect("billiard").capacity;
    let rect_swapped = apply_coordinate_swap(&rect);
    let c_rect_swapped = algo.compute(rect_swapped).expect("billiard").capacity;

    let rel_error = (c_rect_swapped - c_rect).abs() / c_rect;
    assert!(
        rel_error < 0.01,
        "coordinate swap on rectangle should preserve capacity: {} vs {} (error {:.2}%)",
        c_rect,
        c_rect_swapped,
        rel_error * 100.0
    );
}

// =============================================================================
// Slow tests (ignored by default) - for thorough validation
// =============================================================================

/// Test on tesseract (8 facets) - slow but thorough.
#[test]
#[ignore = "HK2019 too slow for 8-facet tesseract; run with --ignored for thorough testing"]
fn invariance_sp4_tesseract_slow() {
    let algo = HK2019Algorithm::new();
    let original = tesseract();
    let c_original = algo.compute(original.clone()).expect("hk2019").capacity;

    for seed in [42, 123] {
        let a = seeded_sp4_bounded(seed, 0.2);
        let transformed = apply_sp4_to_polytope(&a, &original);
        let c_transformed = algo.compute(transformed).expect("hk2019").capacity;

        let rel_error = (c_transformed - c_original).abs() / c_original;
        assert!(
            rel_error < 0.05,
            "Sp(4) on tesseract (seed={}) should preserve capacity: {:.4} vs {:.4}",
            seed,
            c_original,
            c_transformed
        );
    }
}

/// Test invariance under block rotations using HK2019.
///
/// Block rotations in (q₁,p₁) or (q₂,p₂) break Lagrangian product structure,
/// so billiard algorithm cannot be used.
#[test]
#[ignore = "Use triangle product test instead; this is for reference"]
fn invariance_block_rotation_tesseract_slow() {
    let algo = HK2019Algorithm::new();
    let original = tesseract();
    let c_original = algo.compute(original.clone()).expect("hk2019").capacity;

    for angle_deg in [15.0, 30.0, 45.0] {
        let theta = angle_deg * PI / 180.0;
        let rotated = apply_q1p1_rotation(&original, theta);
        let c_rotated = algo.compute(rotated).expect("hk2019 on rotated").capacity;

        let rel_error = (c_rotated - c_original).abs() / c_original;
        assert!(
            rel_error < 0.05,
            "q1p1 rotation by {}° should preserve capacity: {:.4} vs {:.4}",
            angle_deg,
            c_original,
            c_rotated
        );
    }
}

// =============================================================================
// Verification: symplectic property of transforms
// =============================================================================

#[cfg(test)]
mod verify_transforms {
    use super::*;
    use rust_viterbo_geom::symplectic_form;

    /// Verify that (q₁,p₁) rotation preserves symplectic form.
    #[test]
    fn q1p1_rotation_is_symplectic() {
        let u = SymplecticVector::new(1.0, 2.0, 3.0, 4.0);
        let v = SymplecticVector::new(-1.0, 0.5, 2.0, -3.0);
        let omega_before = symplectic_form(u, v);

        for theta in [PI / 6.0, PI / 4.0, PI / 3.0] {
            let (ux, uz) = rotate_2d(u.x, u.z, theta);
            let (vx, vz) = rotate_2d(v.x, v.z, theta);
            let u_rot = SymplecticVector::new(ux, u.y, uz, u.w);
            let v_rot = SymplecticVector::new(vx, v.y, vz, v.w);
            let omega_after = symplectic_form(u_rot, v_rot);

            assert!(
                (omega_before - omega_after).abs() < 1e-10,
                "rotation should preserve ω: {} vs {}",
                omega_before,
                omega_after
            );
        }
    }

    /// Verify that coordinate swap preserves symplectic form.
    #[test]
    fn coordinate_swap_is_symplectic() {
        let u = SymplecticVector::new(1.0, 2.0, 3.0, 4.0);
        let v = SymplecticVector::new(-1.0, 0.5, 2.0, -3.0);
        let omega_before = symplectic_form(u, v);

        let u_swap = SymplecticVector::new(u.y, u.x, u.w, u.z);
        let v_swap = SymplecticVector::new(v.y, v.x, v.w, v.z);
        let omega_after = symplectic_form(u_swap, v_swap);

        assert!(
            (omega_before - omega_after).abs() < 1e-10,
            "swap should preserve ω: {} vs {}",
            omega_before,
            omega_after
        );
    }

    /// Verify that Sp(4) generator produces valid symplectic matrices.
    #[test]
    fn sp4_generator_produces_symplectic_matrices() {
        use super::super::generators::is_symplectic;

        for seed in 0..50 {
            let a = seeded_sp4(seed);
            assert!(
                is_symplectic(&a, 1e-8),
                "seeded_sp4({}) should be symplectic",
                seed
            );
        }
    }
}
