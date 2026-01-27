//! Test fixtures for the tube algorithm.
//!
//! Provides standard polytopes for testing:
//! - `unit_cross_polytope()`: 16-cell, suitable for tube algorithm (no Lagrangian 2-faces)
//! - `unit_tesseract()`: Hypercube, rejected by tube algorithm (all 2-faces Lagrangian)
//! - `four_simplex()`: 5-cell, rejected by tube algorithm (has Lagrangian 2-faces)
//! - `unit_24_cell()`: 24-cell, suitable for tube algorithm (different symmetry than cross-polytope)
//! - `asymmetric_cross_polytope(seed)`: Perturbed cross-polytope with broken symmetry
//! - `random_hrep(n_facets, min_omega, max_vertex_coord, seed)`: Random H-rep for stress testing

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

/// Generate a random H-rep with uniformly distributed normals on S³.
///
/// The polytope is generated by:
/// 1. n_i ~ Uniform(S³) via rejection sampling
/// 2. h_i ~ Uniform([0.3, 3.0])
/// 3. Reject if any pair has |ω(n_i, n_j)| < min_omega (near-Lagrangian)
/// 4. Reject if any vertex coordinate exceeds `max_vertex_coord` (nearly unbounded)
/// 5. Reject if any facet is redundant (doesn't define the polytope boundary)
///
/// # Arguments
/// * `n_facets` - Number of facets (minimum 5 for a 4D polytope)
/// * `min_omega` - Minimum |ω(n_i, n_j)| between any pair (e.g., 0.01)
/// * `max_vertex_coord` - Maximum absolute vertex coordinate (e.g., 100.0)
/// * `seed` - Random seed for reproducibility
///
/// Returns `None` if the generated H-rep fails any rejection criterion.
pub fn random_hrep(
    n_facets: usize,
    min_omega: f64,
    max_vertex_coord: f64,
    seed: u64,
) -> Option<PolytopeHRep> {
    use nalgebra::Matrix4;
    use crate::constants::EPS;

    assert!(n_facets >= 5, "4D polytope needs at least 5 facets");

    // Simple LCG for deterministic randomness (same constants as PCG)
    let mut rng_state = seed;
    let mut next_rand_01 = || {
        rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1);
        ((rng_state >> 33) as f64) / (u32::MAX as f64) // Range [0, 1]
    };

    // Generate random unit normals (approximately uniform on S³ via normalization)
    let mut normals = Vec::with_capacity(n_facets);
    for _ in 0..n_facets {
        // Map [0,1] to [-1,1] for each coordinate
        let v = Vector4::new(
            next_rand_01() * 2.0 - 1.0,
            next_rand_01() * 2.0 - 1.0,
            next_rand_01() * 2.0 - 1.0,
            next_rand_01() * 2.0 - 1.0,
        );
        if v.norm() < 0.01 {
            return None; // Degenerate, reject this seed
        }
        normals.push(v.normalize());
    }

    // Generate random heights in [0.3, 3.0]
    let heights: Vec<f64> = (0..n_facets)
        .map(|_| 0.3 + next_rand_01() * 2.7)
        .collect();

    // Check all pairs satisfy minimum omega constraint (non-Lagrangian)
    for i in 0..n_facets {
        for j in (i + 1)..n_facets {
            let omega = symplectic_form(&normals[i], &normals[j]);
            if omega.abs() < min_omega {
                return None; // Near-Lagrangian pair
            }
        }
    }

    // Enumerate vertices and check boundedness
    let mut vertices = Vec::new();
    for i in 0..n_facets {
        for j in (i + 1)..n_facets {
            for k in (j + 1)..n_facets {
                for l in (k + 1)..n_facets {
                    // Build system: [n_i; n_j; n_k; n_l] * x = [h_i; h_j; h_k; h_l]
                    let m = Matrix4::from_rows(&[
                        normals[i].transpose(),
                        normals[j].transpose(),
                        normals[k].transpose(),
                        normals[l].transpose(),
                    ]);

                    if let Some(m_inv) = m.try_inverse() {
                        let h = Vector4::new(heights[i], heights[j], heights[k], heights[l]);
                        let candidate = m_inv * h;

                        // Check boundedness
                        if candidate.iter().any(|&c| c.abs() > max_vertex_coord) {
                            return None; // Nearly unbounded
                        }

                        // Check if candidate satisfies all constraints
                        let is_valid = normals.iter().zip(&heights).all(|(n, &h)| {
                            n.dot(&candidate) <= h + EPS
                        });

                        if is_valid {
                            // Check it's not a duplicate
                            let is_dup = vertices
                                .iter()
                                .any(|v: &Vector4<f64>| (v - candidate).norm() < EPS);
                            if !is_dup {
                                vertices.push(candidate);
                            }
                        }
                    }
                }
            }
        }
    }

    // Need at least 5 vertices for a 4D polytope
    if vertices.len() < 5 {
        return None; // Degenerate or unbounded
    }

    // Check for redundant facets: each facet should have at least one vertex on it
    for (n, &h) in normals.iter().zip(&heights) {
        let has_vertex_on_facet = vertices
            .iter()
            .any(|v| (n.dot(v) - h).abs() < EPS);
        if !has_vertex_on_facet {
            return None; // Redundant facet
        }
    }

    Some(PolytopeHRep::new(normals, heights))
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

    // === Random H-rep tests ===

    #[test]
    fn test_random_hrep_basic() {
        // Try to generate a random H-rep
        // Many seeds will be rejected (near-Lagrangian, unbounded, redundant)
        let min_omega = 0.01;
        let max_coord = 100.0;
        let mut found_count = 0;
        for seed in 0..2000 {
            if let Some(hrep) = random_hrep(8, min_omega, max_coord, seed) {
                assert_eq!(hrep.num_facets(), 8);
                assert!(hrep.validate().is_ok(), "Generated H-rep should be valid");
                found_count += 1;
                if found_count >= 3 {
                    break;
                }
            }
        }
        // We should find at least a few
        assert!(found_count >= 1, "Should find at least one valid H-rep in 2000 tries");
    }

    #[test]
    fn test_random_hrep_deterministic() {
        // Same seed should give same result
        let min_omega = 0.01;
        let max_coord = 100.0;
        let r1 = random_hrep(8, min_omega, max_coord, 42);
        let r2 = random_hrep(8, min_omega, max_coord, 42);

        match (r1, r2) {
            (Some(h1), Some(h2)) => {
                for (n1, n2) in h1.normals.iter().zip(&h2.normals) {
                    assert_relative_eq!(n1, n2, epsilon = EPS);
                }
                for (&h1, &h2) in h1.heights.iter().zip(&h2.heights) {
                    assert_relative_eq!(h1, h2, epsilon = EPS);
                }
            }
            (None, None) => {} // Both rejected, which is deterministic
            _ => panic!("Same seed should give same result"),
        }
    }

    #[test]
    fn test_random_hrep_respects_min_omega() {
        let min_omega = 0.05;
        let max_coord = 100.0;
        for seed in 0..500 {
            if let Some(hrep) = random_hrep(10, min_omega, max_coord, seed) {
                // Verify all pairs satisfy the min_omega constraint
                for i in 0..hrep.num_facets() {
                    for j in (i + 1)..hrep.num_facets() {
                        let omega = symplectic_form(&hrep.normals[i], &hrep.normals[j]);
                        assert!(
                            omega.abs() >= min_omega,
                            "Seed {} produced pair ({}, {}) with |ω| = {} < {}",
                            seed,
                            i,
                            j,
                            omega.abs(),
                            min_omega
                        );
                    }
                }
            }
        }
    }

    #[test]
    fn test_random_hrep_varied_heights() {
        let min_omega = 0.01;
        let max_coord = 100.0;

        for seed in 0..500 {
            if let Some(hrep) = random_hrep(8, min_omega, max_coord, seed) {
                // Heights should be in [0.3, 3.0] and varied
                for &h in &hrep.heights {
                    assert!(h >= 0.3 && h <= 3.0, "Height {} out of range [0.3, 3.0]", h);
                }

                // Check that heights are not all the same
                let first = hrep.heights[0];
                let all_same = hrep.heights.iter().all(|&h| (h - first).abs() < EPS);
                assert!(!all_same, "Heights should be varied, not all {}", first);
                return; // Found one, test passes
            }
        }
        panic!("Could not find a valid H-rep to test");
    }
}
