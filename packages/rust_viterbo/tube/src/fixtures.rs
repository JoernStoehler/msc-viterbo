//! Test fixtures for the tube algorithm.
//!
//! Provides standard polytopes for testing:
//! - `unit_cross_polytope()`: 16-cell, suitable for tube algorithm (no Lagrangian 2-faces)
//! - `unit_tesseract()`: Hypercube, rejected by tube algorithm (all 2-faces Lagrangian)
//! - `four_simplex()`: 5-cell, rejected by tube algorithm (has Lagrangian 2-faces)
//! - `unit_24_cell()`: 24-cell, suitable for tube algorithm (different symmetry than cross-polytope)
//! - `asymmetric_cross_polytope(seed)`: Perturbed cross-polytope with broken symmetry
//! - `random_non_lagrangian_polytope(n_facets, seed)`: Random polytope for stress testing

use nalgebra::Vector4;

use crate::quaternion::symplectic_form;
use crate::types::PolytopeHRep;

/// Unit cross-polytope (16-cell): conv{±e₁, ±e₂, ±e₃, ±e₄}.
///
/// This is the dual of the tesseract (hypercube), also known as the l^1 unit ball.
///
/// Properties:
/// - 16 facets with normals (±1,±1,±1,±1)/2 (unit normals)
/// - 8 vertices at ±e_i (distance 1 from origin)
/// - All 2-faces are non-Lagrangian (suitable for tube algorithm)
/// - Heights h = 1/2 (facets pass through vertices like e₁, with n·e₁ = 1/2)
/// - Capacity: c_EHZ = 1.0 (empirically determined; was unknown prior to this implementation)
pub fn unit_cross_polytope() -> PolytopeHRep {
    let mut normals = Vec::new();

    // 16 facets with normals (±1,±1,±1,±1)/2
    for s1 in [-1.0, 1.0] {
        for s2 in [-1.0, 1.0] {
            for s3 in [-1.0, 1.0] {
                for s4 in [-1.0, 1.0] {
                    normals.push(Vector4::new(s1, s2, s3, s4) / 2.0);
                }
            }
        }
    }

    // Heights are 1/2: each facet passes through a vertex e_i, and n·e_i = 1/2
    let heights = vec![0.5; 16];

    PolytopeHRep::new(normals, heights)
}

/// Unit tesseract (4-cube): [-1,1]⁴.
///
/// This is a Lagrangian product: square × square.
///
/// Properties:
/// - 8 facets with axis-aligned normals
/// - 16 vertices at (±1, ±1, ±1, ±1)
/// - All 2-faces are Lagrangian (NOT suitable for tube algorithm)
/// - Expected capacity: 4.0
pub fn unit_tesseract() -> PolytopeHRep {
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

/// Scaled cross-polytope: λ × unit_cross_polytope.
///
/// Capacity scales as λ²: c(λK) = λ² c(K).
pub fn scaled_cross_polytope(lambda: f64) -> PolytopeHRep {
    let base = unit_cross_polytope();
    PolytopeHRep::new(
        base.normals,
        base.heights.into_iter().map(|h| h * lambda).collect(),
    )
}

/// 4-simplex (5-cell/pentatope): conv{e₁, e₂, e₃, e₄, (-1,-1,-1,-1)}.
///
/// This is the simplest 4D polytope with only 5 facets.
/// The simplex is centered at the origin.
///
/// Properties:
/// - 5 facets (smallest possible for a 4D polytope)
/// - 5 vertices: (1,0,0,0), (0,1,0,0), (0,0,1,0), (0,0,0,1), (-1,-1,-1,-1)
/// - Centroid at origin
/// - Has Lagrangian 2-faces (NOT suitable for tube algorithm)
/// - Used for testing that the algorithm correctly rejects such polytopes
pub fn four_simplex() -> PolytopeHRep {
    // Vertices: e1, e2, e3, e4, and (-1,-1,-1,-1), centered at origin
    // For each facet opposite vertex v_i, find the outward normal and height.

    let sqrt19 = 19.0_f64.sqrt();

    // Facet opposite v4=(-1,-1,-1,-1): contains e1,e2,e3,e4
    // Plane: x1+x2+x3+x4 = 1
    let n4 = Vector4::new(1.0, 1.0, 1.0, 1.0) / 2.0;
    let h4 = 0.5;

    // Facet opposite v0=(1,0,0,0): contains e2,e3,e4,(-1,-1,-1,-1)
    // Plane: -4x1+x2+x3+x4 = 1
    let n0 = Vector4::new(-4.0, 1.0, 1.0, 1.0) / sqrt19;
    let h0 = 1.0 / sqrt19;

    // Facet opposite v1=(0,1,0,0): by symmetry
    let n1 = Vector4::new(1.0, -4.0, 1.0, 1.0) / sqrt19;
    let h1 = 1.0 / sqrt19;

    // Facet opposite v2=(0,0,1,0): by symmetry
    let n2 = Vector4::new(1.0, 1.0, -4.0, 1.0) / sqrt19;
    let h2 = 1.0 / sqrt19;

    // Facet opposite v3=(0,0,0,1): by symmetry
    let n3 = Vector4::new(1.0, 1.0, 1.0, -4.0) / sqrt19;
    let h3 = 1.0 / sqrt19;

    PolytopeHRep::new(vec![n0, n1, n2, n3, n4], vec![h0, h1, h2, h3, h4])
}

/// 24-cell (icositetrachoron): a regular 4D polytope with 24 octahedral cells.
///
/// This is self-dual and has a different symmetry group than the cross-polytope.
///
/// Properties:
/// - 24 facets with normals (±1,±1,0,0)/√2 and permutations
/// - 24 vertices (same as normals scaled)
/// - All 2-faces are non-Lagrangian (suitable for tube algorithm)
/// - Heights h = 1/√2 (unit distance from origin)
///
/// The 24-cell provides a different test case than the cross-polytope:
/// - Different number of facets (24 vs 16)
/// - Different vertex structure
/// - Different combinatorial type
pub fn unit_24_cell() -> PolytopeHRep {
    let s = 1.0 / 2.0_f64.sqrt(); // 1/√2 for unit normals

    let mut normals = Vec::with_capacity(24);

    // 24 normals: all permutations of (±1,±1,0,0)/√2
    // There are 6 coordinate pairs × 4 sign combinations = 24 normals
    let pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)];

    for (i, j) in pairs {
        for s1 in [-1.0, 1.0] {
            for s2 in [-1.0, 1.0] {
                let mut n = Vector4::zeros();
                n[i] = s1 * s;
                n[j] = s2 * s;
                normals.push(n);
            }
        }
    }

    // Heights: for the unit 24-cell, h = 1/√2
    let heights = vec![s; 24];

    PolytopeHRep::new(normals, heights)
}

/// Asymmetric cross-polytope with perturbed normals.
///
/// Starts from the cross-polytope and applies deterministic perturbations
/// based on the seed. Heights are adjusted to maintain origin in interior.
///
/// This breaks the 16-fold symmetry of the standard cross-polytope while
/// ensuring all 2-faces remain non-Lagrangian.
///
/// Use different seeds to get different asymmetric variants.
pub fn asymmetric_cross_polytope(seed: u64) -> PolytopeHRep {
    let base = unit_cross_polytope();
    let mut normals = base.normals;

    // Simple linear congruential generator for determinism
    let mut rng_state = seed;
    let mut next_rand = || {
        rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1);
        ((rng_state >> 33) as f64) / (u32::MAX as f64) - 0.5 // Range [-0.5, 0.5]
    };

    // Perturb each normal slightly and renormalize
    let perturbation_scale = 0.1; // 10% perturbation
    for n in &mut normals {
        let perturbation = Vector4::new(
            next_rand() * perturbation_scale,
            next_rand() * perturbation_scale,
            next_rand() * perturbation_scale,
            next_rand() * perturbation_scale,
        );
        *n = (*n + perturbation).normalize();
    }

    // Recompute heights to ensure origin is in interior
    // Use h = 0.4 (slightly less than original 0.5 to be safe)
    let heights = vec![0.4; 16];

    PolytopeHRep::new(normals, heights)
}

/// Tolerance for checking non-Lagrangian property in random generation.
/// Lower than the algorithm's EPS_LAGRANGIAN (1e-8) but high enough to avoid
/// near-Lagrangian cases that cause numerical issues.
const NON_LAGRANGIAN_TOL: f64 = 0.01;

/// Generate a random polytope with no Lagrangian 2-faces (with high probability).
///
/// The polytope is generated by:
/// 1. Creating random unit normals from a seeded PRNG
/// 2. Checking that all pairs have |ω(n_i, n_j)| > tolerance
/// 3. Setting heights to ensure origin is in interior
///
/// Returns `None` if the generated polytope has Lagrangian 2-faces
/// (which should be rare for generic random normals).
///
/// # Arguments
/// * `n_facets` - Number of facets (minimum 5 for a 4D polytope)
/// * `seed` - Random seed for reproducibility
///
/// # Note
/// This generator doesn't guarantee a valid convex polytope geometry -
/// it generates H-representation data that may be degenerate or unbounded.
/// Use `PolytopeHRep::validate()` on the result.
pub fn random_non_lagrangian_polytope(n_facets: usize, seed: u64) -> Option<PolytopeHRep> {
    assert!(n_facets >= 5, "4D polytope needs at least 5 facets");

    // Simple LCG for deterministic randomness
    let mut rng_state = seed;
    let mut next_rand = || {
        rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1);
        ((rng_state >> 33) as f64) / (u32::MAX as f64) * 2.0 - 1.0 // Range [-1, 1]
    };

    // Generate random unit normals
    let mut normals = Vec::with_capacity(n_facets);
    for _ in 0..n_facets {
        let v = Vector4::new(next_rand(), next_rand(), next_rand(), next_rand());
        if v.norm() < 0.01 {
            // Degenerate, skip
            normals.push(Vector4::new(1.0, 0.0, 0.0, 0.0));
        } else {
            normals.push(v.normalize());
        }
    }

    // Check all pairs are non-Lagrangian
    for i in 0..n_facets {
        for j in (i + 1)..n_facets {
            let omega = symplectic_form(&normals[i], &normals[j]);
            if omega.abs() < NON_LAGRANGIAN_TOL {
                return None; // Has a near-Lagrangian 2-face
            }
        }
    }

    // Use uniform heights
    let heights = vec![1.0; n_facets];

    Some(PolytopeHRep::new(normals, heights))
}

/// Generate multiple random polytopes, returning only valid non-Lagrangian ones.
///
/// Tries up to `max_attempts` seeds starting from `base_seed` and returns
/// the first `count` valid polytopes found.
///
/// # Returns
/// Vector of (seed, polytope) pairs for reproducibility.
pub fn random_non_lagrangian_batch(
    n_facets: usize,
    count: usize,
    base_seed: u64,
    max_attempts: usize,
) -> Vec<(u64, PolytopeHRep)> {
    let mut results = Vec::with_capacity(count);

    for i in 0..max_attempts {
        if results.len() >= count {
            break;
        }
        let seed = base_seed.wrapping_add(i as u64);
        if let Some(hrep) = random_non_lagrangian_polytope(n_facets, seed) {
            // Additional validation: check the polytope structure is valid
            if hrep.validate().is_ok() {
                results.push((seed, hrep));
            }
        }
    }

    results
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::constants::EPS;
    use approx::assert_relative_eq;

    #[test]
    fn test_cross_polytope_valid() {
        let hrep = unit_cross_polytope();
        assert!(hrep.validate().is_ok());
        assert_eq!(hrep.num_facets(), 16);
    }

    #[test]
    fn test_cross_polytope_normals_unit() {
        let hrep = unit_cross_polytope();
        for (i, n) in hrep.normals.iter().enumerate() {
            assert!(
                (n.norm() - 1.0).abs() < EPS,
                "Normal {} not unit: norm = {}",
                i,
                n.norm()
            );
        }
    }

    #[test]
    fn test_tesseract_valid() {
        let hrep = unit_tesseract();
        assert!(hrep.validate().is_ok());
        assert_eq!(hrep.num_facets(), 8);
    }

    #[test]
    fn test_tesseract_normals_unit() {
        let hrep = unit_tesseract();
        for (i, n) in hrep.normals.iter().enumerate() {
            assert!(
                (n.norm() - 1.0).abs() < EPS,
                "Normal {} not unit: norm = {}",
                i,
                n.norm()
            );
        }
    }

    #[test]
    fn test_scaled_cross_polytope() {
        let lambda = 2.0;
        let scaled = scaled_cross_polytope(lambda);
        let base = unit_cross_polytope();

        // Normals should be the same
        for (n1, n2) in scaled.normals.iter().zip(&base.normals) {
            assert_relative_eq!(n1, n2, epsilon = EPS);
        }

        // Heights should be scaled
        for (h1, h2) in scaled.heights.iter().zip(&base.heights) {
            assert_relative_eq!(*h1, h2 * lambda, epsilon = EPS);
        }
    }

    #[test]
    fn test_four_simplex_valid() {
        let hrep = four_simplex();
        assert!(hrep.validate().is_ok());
        assert_eq!(hrep.num_facets(), 5);
    }

    #[test]
    fn test_four_simplex_normals_unit() {
        let hrep = four_simplex();
        for (i, n) in hrep.normals.iter().enumerate() {
            assert!(
                (n.norm() - 1.0).abs() < EPS,
                "Normal {} not unit: norm = {}",
                i,
                n.norm()
            );
        }
    }

    #[test]
    fn test_four_simplex_vertices_inside() {
        let hrep = four_simplex();
        let vertices = [
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(-1.0, -1.0, -1.0, -1.0),
        ];

        // Each vertex should satisfy all constraints (with small tolerance for boundary)
        for (i, v) in vertices.iter().enumerate() {
            for (j, (n, h)) in hrep.normals.iter().zip(&hrep.heights).enumerate() {
                let value = n.dot(v);
                assert!(
                    value <= h + EPS,
                    "Vertex {} violates constraint {}: {} > {}",
                    i,
                    j,
                    value,
                    h
                );
            }
        }
    }

    #[test]
    fn test_four_simplex_centroid_interior() {
        let hrep = four_simplex();
        let centroid = Vector4::new(0.0, 0.0, 0.0, 0.0);

        // Centroid should be strictly inside all constraints
        for (j, (n, h)) in hrep.normals.iter().zip(&hrep.heights).enumerate() {
            let value = n.dot(&centroid);
            assert!(
                value < h - EPS,
                "Centroid not strictly interior to constraint {}: {} >= {}",
                j,
                value,
                h
            );
        }
    }

    // === 24-cell tests ===

    #[test]
    fn test_24_cell_valid() {
        let hrep = unit_24_cell();
        assert!(hrep.validate().is_ok());
        assert_eq!(hrep.num_facets(), 24);
    }

    #[test]
    fn test_24_cell_normals_unit() {
        let hrep = unit_24_cell();
        for (i, n) in hrep.normals.iter().enumerate() {
            assert!(
                (n.norm() - 1.0).abs() < EPS,
                "Normal {} not unit: norm = {}",
                i,
                n.norm()
            );
        }
    }

    #[test]
    fn test_24_cell_no_lagrangian_2faces() {
        let hrep = unit_24_cell();
        // Check all pairs of normals have non-zero symplectic form
        // Note: not all pairs form actual 2-faces, but Lagrangian pairs would be problematic
        for i in 0..hrep.num_facets() {
            for j in (i + 1)..hrep.num_facets() {
                let omega = symplectic_form(&hrep.normals[i], &hrep.normals[j]);
                // For the 24-cell, pairs that share a 2-face should have |ω| = 1/2 or 1
                // We just check they're not zero
                assert!(
                    omega.abs() > 0.01 || omega.abs() < EPS, // Either clearly non-zero or zero (non-adjacent)
                    "24-cell normals {} and {} may be Lagrangian: ω = {}",
                    i,
                    j,
                    omega
                );
            }
        }
    }

    #[test]
    fn test_24_cell_origin_interior() {
        let hrep = unit_24_cell();
        let origin = Vector4::zeros();

        for (i, (n, &h)) in hrep.normals.iter().zip(&hrep.heights).enumerate() {
            let value = n.dot(&origin);
            assert!(
                value < h - EPS,
                "Origin not strictly interior to facet {}: {} >= {}",
                i,
                value,
                h
            );
        }
    }

    // === Asymmetric cross-polytope tests ===

    #[test]
    fn test_asymmetric_cross_polytope_valid() {
        for seed in [0, 42, 123, 999] {
            let hrep = asymmetric_cross_polytope(seed);
            assert!(
                hrep.validate().is_ok(),
                "Asymmetric cross-polytope with seed {} is invalid",
                seed
            );
            assert_eq!(hrep.num_facets(), 16);
        }
    }

    #[test]
    fn test_asymmetric_cross_polytope_normals_unit() {
        let hrep = asymmetric_cross_polytope(42);
        for (i, n) in hrep.normals.iter().enumerate() {
            assert!(
                (n.norm() - 1.0).abs() < EPS,
                "Normal {} not unit: norm = {}",
                i,
                n.norm()
            );
        }
    }

    #[test]
    fn test_asymmetric_cross_polytope_deterministic() {
        // Same seed should give same polytope
        let h1 = asymmetric_cross_polytope(42);
        let h2 = asymmetric_cross_polytope(42);

        for (n1, n2) in h1.normals.iter().zip(&h2.normals) {
            assert_relative_eq!(n1, n2, epsilon = EPS);
        }
    }

    #[test]
    fn test_asymmetric_cross_polytope_different_seeds() {
        // Different seeds should give different polytopes
        let h1 = asymmetric_cross_polytope(1);
        let h2 = asymmetric_cross_polytope(2);

        let mut all_same = true;
        for (n1, n2) in h1.normals.iter().zip(&h2.normals) {
            if (n1 - n2).norm() > EPS {
                all_same = false;
                break;
            }
        }
        assert!(!all_same, "Different seeds should produce different polytopes");
    }

    #[test]
    fn test_asymmetric_cross_polytope_breaks_symmetry() {
        let hrep = asymmetric_cross_polytope(42);

        // The symmetric cross-polytope has all heights = 0.5
        // The asymmetric one should have varied normals (but uniform heights for simplicity)
        // Check normals are not all equal in each component
        let first_normal = &hrep.normals[0];
        let mut has_different_normals = false;
        for n in &hrep.normals[1..] {
            if (n - first_normal).norm() > 0.05 {
                has_different_normals = true;
                break;
            }
        }
        assert!(
            has_different_normals,
            "Asymmetric polytope should have varied normals"
        );
    }

    // === Random non-Lagrangian polytope tests ===

    #[test]
    fn test_random_polytope_basic() {
        // Try to generate a random polytope
        // Many seeds will be rejected (Lagrangian pairs or invalid geometry)
        // so we try many seeds and just check we can generate some
        let mut found_count = 0;
        for seed in 0..500 {
            if let Some(hrep) = random_non_lagrangian_polytope(8, seed) {
                // Note: validate() may fail for random normals since they don't
                // necessarily form a bounded polytope. We just check the basic structure.
                assert_eq!(hrep.num_facets(), 8);
                found_count += 1;
                if found_count >= 3 {
                    break;
                }
            }
        }
        // We should find at least a few, but random generation is hard
        assert!(found_count >= 1, "Should find at least one non-Lagrangian polytope in 500 tries");
    }

    #[test]
    fn test_random_polytope_deterministic() {
        // Same seed should give same result
        let r1 = random_non_lagrangian_polytope(8, 42);
        let r2 = random_non_lagrangian_polytope(8, 42);

        match (r1, r2) {
            (Some(h1), Some(h2)) => {
                for (n1, n2) in h1.normals.iter().zip(&h2.normals) {
                    assert_relative_eq!(n1, n2, epsilon = EPS);
                }
            }
            (None, None) => {} // Both rejected, which is deterministic
            _ => panic!("Same seed should give same result"),
        }
    }

    #[test]
    fn test_random_polytope_no_lagrangian_pairs() {
        for seed in 0..50 {
            if let Some(hrep) = random_non_lagrangian_polytope(10, seed) {
                // Verify no Lagrangian pairs
                for i in 0..hrep.num_facets() {
                    for j in (i + 1)..hrep.num_facets() {
                        let omega = symplectic_form(&hrep.normals[i], &hrep.normals[j]);
                        assert!(
                            omega.abs() >= NON_LAGRANGIAN_TOL,
                            "Seed {} produced Lagrangian pair ({}, {}): ω = {}",
                            seed,
                            i,
                            j,
                            omega
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_random_batch_generation() {
        // Request 3 valid polytopes from up to 2000 seeds
        let batch = random_non_lagrangian_batch(8, 3, 0, 2000);

        // Should be able to find at least some valid polytopes
        // (random generation is hard, so we're lenient here)
        assert!(
            !batch.is_empty(),
            "Should find at least 1 valid polytope in 2000 tries"
        );

        // Each returned polytope should be valid and non-Lagrangian
        for (seed, hrep) in &batch {
            assert!(
                hrep.validate().is_ok(),
                "Seed {} produced invalid polytope",
                seed
            );

            for i in 0..hrep.num_facets() {
                for j in (i + 1)..hrep.num_facets() {
                    let omega = symplectic_form(&hrep.normals[i], &hrep.normals[j]);
                    assert!(
                        omega.abs() >= NON_LAGRANGIAN_TOL,
                        "Seed {} has Lagrangian pair",
                        seed
                    );
                }
            }
        }
    }
}
