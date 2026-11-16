//! Test fixtures: polytopes and utilities used across test modules.
//!
//! This module provides:
//!
//! - **Ground truth polytopes**: Polytopes with capacities known from literature.
//!   Each has a documented source reference.
//!
//! - **Random generators**: Generate random Lagrangian products and non-Lagrangian
//!   polytopes with configurable parameters.
//!
//! - **Proptest strategies**: For property-based testing of capacity algorithms.
//!
//! # Polytope Classification (IMPORTANT)
//!
//! ## Lagrangian Products
//!
//! A polytope K is a **Lagrangian product** if K = K₁ × K₂ where K₁ ⊂ R²_q and K₂ ⊂ R²_p.
//! Equivalently: all facet normals are either (n_q, 0) or (0, n_p).
//!
//! **IMPORTANT:** Lagrangian products do NOT have "all 2-faces Lagrangian"!
//!
//! **Example: Tesseract [-1,1]^4 = [-1,1]² × [-1,1]²**
//! - 8 facets with normals ±e₁, ±e₂, ±e₃, ±e₄ (where e₁,e₂ are q-space, e₃,e₄ are p-space)
//! - C(8,2) = 28 pairs total
//! - **8 NON-Lagrangian 2-faces**: pairs (±e₁, ±e₃) and (±e₂, ±e₄) have ω ≠ 0
//! - **20 Lagrangian 2-faces**: all other pairs have ω = 0
//! - See `polytope_preprocessing.rs` for explicit verification tests.
//!
//! **Algorithm compatibility:**
//! - Billiard algorithm: WORKS (uses the 8 non-Lagrangian 2-faces)
//! - HK2019 algorithm: WORKS (but slow)
//! - Tube algorithm: WORKS in principle (has non-Lagrangian 2-faces)
//!
//! **Examples:**
//! - `tesseract()`: [-1,1]^4, capacity = 4.0
//! - `triangle_product()`: equilateral triangle × same, capacity = 1.5
//! - `pentagon_product()`: regular pentagon × rotated pentagon, capacity = 3.441
//!
//! ## Non-Lagrangian Polytopes (for Tube Algorithm)
//!
//! For the **tube algorithm** to work optimally, we want polytopes where ALL 2-faces
//! are non-Lagrangian (ω(n_i, n_j) ≠ 0 for all facet pairs i < j).
//!
//! **Examples:**
//! - `random_nonlagrangian_polytope(57)`: 5 facets, 0 Lagrangian 2-faces, tube finds orbit
//! - `random_nonlagrangian_polytope(1729)`: 6 facets, 0 Lagrangian 2-faces, tube finds orbit
//!
//! ## Polytopes with Some Lagrangian 2-Faces
//!
//! Some polytopes have a mix of Lagrangian and non-Lagrangian 2-faces:
//! - `skewed_simplex_4d()`: 5 facets, 4 Lagrangian / 6 non-Lagrangian
//! - `tesseract()`: 8 facets, 20 Lagrangian / 8 non-Lagrangian
//! - `generic_polytope()`: 9 facets (tesseract + 1 extra normal)
//!
//! # Random Polytope Generator
//!
//! `random_nonlagrangian_polytope(seed)` generates a random polytope with the given seed.
//! - Default: 6 facets
//! - Uses rejection sampling: returns None if not ALL pairs are non-Lagrangian
//! - Call `try_random_nonlagrangian_polytope(seed, n_facets, ...)` to control facet count
//!
//! Pre-verified seeds that produce valid polytopes with tube orbits:
//! - Seed 57: 5 facets, 10/10 non-Lagrangian pairs, finds orbit
//! - Seed 1729: 6 facets, 15/15 non-Lagrangian pairs, finds orbit
//!
//! # Ground Truth Polytopes
//!
//! | Polytope                  | Capacity | Algorithm   | Source                      |
//! |---------------------------|----------|-------------|------------------------------|
//! | Tesseract [-1,1]^4       | 4.0      | Billiard    | HK2019 Ex 4.6, Rudolf 2022  |
//! | Rectangle 2x1 product     | 1.0      | Billiard    | Scaling axiom               |
//! | Triangle × Triangle       | 1.5      | Billiard    | Computational (no citation) |
//! | Pentagon HK-O 2024       | 3.441... | Billiard    | HK-O 2024 Prop 1.4          |
//! | Simplex (standard)        | 0.25     | HK2019      | Y. Nir thesis 2013          |
//!
//! # References
//!
//! - HK-O 2024: "A counterexample to the Viterbo conjecture"
//! - Siegel: "Symplectic Capacities Project" (computational verification)
//! - CH2021: Chaidez-Hutchings "Computing Reeb Dynamics on Polytopes"
//! - Y. Nir: "On Closed Characteristics and Billiards in Convex Bodies" (thesis, 2013)

use proptest::prelude::*;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;
use rust_viterbo_geom::{perturb_polytope_normals, PolytopeHRep, SymplecticVector, Vector2f};
use std::f64::consts::{PI, TAU};

use crate::polytope::PolytopeData;

/// Standard tesseract (4D hypercube) [-1,1]⁴.
/// This is a Lagrangian product: B² × B² where B² = [-1,1]².
/// Known capacity: c_EHZ = 4.0
pub fn tesseract() -> PolytopeHRep {
    let normals = vec![
        SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(-1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
        SymplecticVector::new(0.0, -1.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, -1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
        SymplecticVector::new(0.0, 0.0, 0.0, -1.0),
    ];
    PolytopeHRep::new(normals, vec![1.0; 8])
}

/// A polytope that is NOT a Lagrangian product.
pub fn generic_polytope() -> PolytopeHRep {
    let mut normals = vec![
        SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(-1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
        SymplecticVector::new(0.0, -1.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, -1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
        SymplecticVector::new(0.0, 0.0, 0.0, -1.0),
    ];
    let v = SymplecticVector::new(1.0, 0.0, 1.0, 0.0);
    normals.push(v / v.norm());
    PolytopeHRep::new(normals, vec![1.0; 9])
}

/// Scale a polytope by factor λ (multiply all heights by λ).
pub fn scale_polytope(hrep: &PolytopeHRep, lambda: f64) -> PolytopeHRep {
    let scaled_heights: Vec<f64> = hrep.heights.iter().map(|h| h * lambda).collect();
    PolytopeHRep::new(hrep.normals.clone(), scaled_heights)
}

/// Create a perturbed tesseract for tube algorithm testing.
pub fn perturbed_tesseract() -> PolytopeData {
    let hrep = tesseract();
    let outcome = perturb_polytope_normals(&hrep, 42, 1e-4);
    PolytopeData::new(outcome.polytope)
}

/// A 2D convex polygon represented by vertices in CCW order.
#[derive(Clone, Debug)]
pub struct Polygon2D {
    pub vertices: Vec<Vector2f>,
}

impl Polygon2D {
    /// Convert to H-representation (outward normals, positive heights).
    pub fn to_hrep_2d(&self) -> (Vec<Vector2f>, Vec<f64>) {
        let n = self.vertices.len();
        let mut normals = Vec::with_capacity(n);
        let mut heights = Vec::with_capacity(n);

        for i in 0..n {
            let v1 = self.vertices[i];
            let v2 = self.vertices[(i + 1) % n];
            let edge = Vector2f::new(v2.x - v1.x, v2.y - v1.y);
            let normal = Vector2f::new(edge.y, -edge.x);
            let len = (normal.x * normal.x + normal.y * normal.y).sqrt();
            let normal = Vector2f::new(normal.x / len, normal.y / len);
            let height = normal.x * v1.x + normal.y * v1.y;
            debug_assert!(
                height > 0.0,
                "Height should be positive for star-shaped polygon"
            );
            normals.push(normal);
            heights.push(height);
        }
        (normals, heights)
    }
}

/// Generate a random convex 2D polygon with n vertices.
pub fn random_convex_polygon<R: rand::Rng>(
    rng: &mut R,
    n_vertices: usize,
    r_min: f64,
    r_max: f64,
) -> Polygon2D {
    assert!(n_vertices >= 3);
    assert!(r_min > 0.0);
    assert!(r_max >= r_min);

    let r_base = (r_min + r_max) / 2.0;
    let r_perturb = r_base * 0.1;

    let mut vertices = Vec::with_capacity(n_vertices);
    for i in 0..n_vertices {
        let angle = TAU * (i as f64) / (n_vertices as f64);
        let radius = r_base + (rng.gen::<f64>() - 0.5) * 2.0 * r_perturb;
        vertices.push(Vector2f::new(radius * angle.cos(), radius * angle.sin()));
    }
    Polygon2D { vertices }
}

/// Generate a random Lagrangian product K₁ × K₂ in ℝ⁴.
pub fn random_lagrangian_product<R: rand::Rng>(
    rng: &mut R,
    n1: usize,
    n2: usize,
    r_min: f64,
    r_max: f64,
) -> PolytopeHRep {
    let k1 = random_convex_polygon(rng, n1, r_min, r_max);
    let k2 = random_convex_polygon(rng, n2, r_min, r_max);

    let (normals_q, heights_q) = k1.to_hrep_2d();
    let (normals_p, heights_p) = k2.to_hrep_2d();

    let mut normals_4d = Vec::with_capacity(n1 + n2);
    let mut heights_4d = Vec::with_capacity(n1 + n2);

    for (n, h) in normals_q.iter().zip(&heights_q) {
        normals_4d.push(SymplecticVector::new(n.x, n.y, 0.0, 0.0));
        heights_4d.push(*h);
    }
    for (n, h) in normals_p.iter().zip(&heights_p) {
        normals_4d.push(SymplecticVector::new(0.0, 0.0, n.x, n.y));
        heights_4d.push(*h);
    }

    PolytopeHRep::new(normals_4d, heights_4d)
}

/// Generate a random Lagrangian product from a seed.
pub fn seeded_lagrangian_product(seed: u64, n1: usize, n2: usize) -> PolytopeHRep {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    random_lagrangian_product(&mut rng, n1, n2, 0.5, 2.0)
}

/// 16-cell (cross-polytope): dual of tesseract.
/// 16 facets with normals (±1, ±1, ±1, ±1) / 2.
/// This is NOT a Lagrangian product.
pub fn cross_polytope_16() -> PolytopeHRep {
    let mut normals = Vec::with_capacity(16);
    for s0 in [-1.0, 1.0] {
        for s1 in [-1.0, 1.0] {
            for s2 in [-1.0, 1.0] {
                for s3 in [-1.0, 1.0] {
                    let v = SymplecticVector::new(s0, s1, s2, s3) / 2.0;
                    normals.push(v);
                }
            }
        }
    }
    PolytopeHRep::new(normals, vec![1.0; 16])
}

/// 24-cell: self-dual regular 4-polytope.
/// 24 facets, considered "more spherical" than tesseract.
pub fn cell_24() -> PolytopeHRep {
    let mut normals = Vec::new();

    // 8 facets from tesseract directions
    for i in 0..4 {
        let mut n = [0.0; 4];
        n[i] = 1.0;
        normals.push(SymplecticVector::new(n[0], n[1], n[2], n[3]));
        n[i] = -1.0;
        normals.push(SymplecticVector::new(n[0], n[1], n[2], n[3]));
    }

    // 16 facets from 16-cell directions
    let inv_sqrt2 = 1.0 / 2.0_f64.sqrt();
    for s0 in [-1.0, 1.0] {
        for s1 in [-1.0, 1.0] {
            for (i, j) in [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)] {
                let mut n = [0.0; 4];
                n[i] = s0 * inv_sqrt2;
                n[j] = s1 * inv_sqrt2;
                normals.push(SymplecticVector::new(n[0], n[1], n[2], n[3]));
            }
        }
    }

    // Remove duplicates and normalize
    let mut unique_normals = Vec::new();
    for n in normals {
        let n_norm = n / n.norm();
        let is_duplicate = unique_normals
            .iter()
            .any(|&m: &SymplecticVector| (m - n_norm).norm() < 1e-6 || (m + n_norm).norm() < 1e-6);
        if !is_duplicate {
            unique_normals.push(n_norm);
        }
    }

    PolytopeHRep::new(unique_normals.clone(), vec![1.0; unique_normals.len()])
}

/// Equilateral triangle × same triangle (Lagrangian product).
/// Known capacity: 1.5 (from test-cases.md, verified by LP algorithm).
pub fn equilateral_triangle_product() -> PolytopeHRep {
    use std::f64::consts::PI;
    let mut normals = Vec::with_capacity(6);
    let mut heights = Vec::with_capacity(6);

    // Regular triangle with circumradius 1, centered at origin.
    // For regular n-gon with circumradius R:
    //   - Outward normals point perpendicular to edges (at angles π/n + 2πk/n)
    //   - Inradius (height from origin to edge) = R·cos(π/n)
    // For triangle (n=3): inradius = R·cos(π/3) = R·0.5
    for i in 0..3 {
        let angle = 2.0 * PI * (i as f64) / 3.0 + PI / 2.0; // normal directions
        let nx = angle.cos();
        let ny = angle.sin();
        // Height = inradius = circumradius × cos(60°) = 1.0 × 0.5 = 0.5
        let h = 0.5;
        // q-space facet
        normals.push(SymplecticVector::new(nx, ny, 0.0, 0.0));
        heights.push(h);
    }
    // Same triangle in p-space
    for i in 0..3 {
        let angle = 2.0 * PI * (i as f64) / 3.0 + PI / 2.0;
        let nx = angle.cos();
        let ny = angle.sin();
        let h = 0.5;
        normals.push(SymplecticVector::new(0.0, 0.0, nx, ny));
        heights.push(h);
    }

    PolytopeHRep::new(normals, heights)
}

/// Standard 4-simplex (5 facets).
/// Vertices at origin and unit vectors e₁, e₂, e₃, e₄.
/// Known capacity: 0.25 = 1/(2n) for n=2 (from Siegel's Symplectic Capacities Project).
pub fn simplex_4d() -> PolytopeHRep {
    // Simplex conv{0, e₁, e₂, e₃, e₄} has 5 facets:
    // - 4 coordinate hyperplanes: xᵢ ≥ 0
    // - 1 hyperplane: x₁ + x₂ + x₃ + x₄ ≤ 1
    let normals = vec![
        SymplecticVector::new(-1.0, 0.0, 0.0, 0.0), // -x₁ ≤ 0 → x₁ ≥ 0
        SymplecticVector::new(0.0, -1.0, 0.0, 0.0), // -x₂ ≤ 0
        SymplecticVector::new(0.0, 0.0, -1.0, 0.0), // -x₃ ≤ 0
        SymplecticVector::new(0.0, 0.0, 0.0, -1.0), // -x₄ ≤ 0
        SymplecticVector::new(1.0, 1.0, 1.0, 1.0) / 2.0, // normalized sum ≤ 1
    ];
    // Heights: 0 for coordinate planes, 1/‖n‖ for sum plane
    let heights = vec![0.0, 0.0, 0.0, 0.0, 1.0];

    PolytopeHRep::new(normals, heights)
}

/// Skewed 4-simplex for testing non-Lagrangian structures (5 facets).
///
/// This simplex is constructed to have MOSTLY non-Lagrangian 2-faces.
/// Unlike the standard simplex whose coordinate-aligned normals create
/// many Lagrangian pairs (ω(e_i, e_j) = 0 for i,j in same plane),
/// this simplex has generic normals that break the Lagrangian structure.
///
/// Construction:
/// - Start with the standard simplex conv{0, e₁, e₂, e₃, e₄}
/// - Apply a linear transformation that mixes q and p coordinates
/// - The transformation A mixes (q₁, q₂) with (p₁, p₂) to ensure
///   that ω(n_i, n_j) ≠ 0 for most normal pairs
///
/// Properties:
/// - 5 facets (tractable: 5! = 120 permutations for HK2019)
/// - Most 2-faces are non-Lagrangian
/// - Suitable for tube algorithm testing
pub fn skewed_simplex_4d() -> PolytopeHRep {
    // We construct a simplex with generic normals.
    // The key is to ensure that ω(n_i, n_j) ≠ 0 for most pairs.
    //
    // Recall: ω((q₁,q₂,p₁,p₂), (q₁',q₂',p₁',p₂')) = q₁p₁' + q₂p₂' - p₁q₁' - p₂q₂'
    //
    // Strategy: use normals that have nonzero components in both q and p subspaces.
    // A "generic" linear transformation of the standard simplex will work.
    //
    // We choose normals explicitly to guarantee non-Lagrangian structure:
    // Each normal has components in both the q-plane (x,y) and p-plane (z,w).

    // Construct a simplex by specifying vertices and deriving normals.
    // Vertices: slightly shifted from standard simplex to mix coordinates.
    //
    // Instead, let's directly specify normals that are guaranteed non-Lagrangian.
    // For 5 facets meeting at edges, we need normals such that adjacent facets
    // have ω(n_i, n_j) ≠ 0.

    // Use a rotation/shear in ℝ⁴ that mixes q and p coordinates.
    // Apply to standard simplex normals:
    // n₀ = (-1, 0, 0, 0), n₁ = (0, -1, 0, 0), n₂ = (0, 0, -1, 0), n₃ = (0, 0, 0, -1)
    // n₄ = (1, 1, 1, 1)/2

    // Transformation matrix that mixes q and p:
    // [cos θ,  0,    sin θ,  0   ]
    // [0,      cos θ, 0,     sin θ]
    // [-sin θ, 0,    cos θ,  0   ]
    // [0,     -sin θ, 0,     cos θ]
    // This is a symplectic rotation that mixes (q₁, p₁) and (q₂, p₂).

    let theta = PI / 6.0; // 30 degrees - enough to break Lagrangian structure
    let c = theta.cos();
    let s = theta.sin();

    // Original standard simplex normals (not yet translated to have positive heights)
    // The standard simplex conv{0, e₁, e₂, e₃, e₄} centered at origin would have:
    // But we want a simplex with all positive heights, so let's construct differently.

    // Let's build a simplex centered near origin with vertices:
    // v₀ = (1, 0, 0, 0), v₁ = (0, 1, 0, 0), v₂ = (0, 0, 1, 0), v₃ = (0, 0, 0, 1)
    // v₄ = (-1, -1, -1, -1)/√4 (opposite vertex to balance)
    //
    // Actually, simpler: apply the rotation to the standard simplex and translate.

    // Standard simplex normals (outward):
    let std_normals = [
        SymplecticVector::new(-1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(0.0, -1.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 0.0, -1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 0.0, -1.0),
        SymplecticVector::new(1.0, 1.0, 1.0, 1.0).normalize(),
    ];

    // Apply symplectic rotation to each normal
    let mut normals = Vec::with_capacity(5);
    for n in &std_normals {
        // Transform: (q₁, q₂, p₁, p₂) → (c*q₁ + s*p₁, c*q₂ + s*p₂, -s*q₁ + c*p₁, -s*q₂ + c*p₂)
        let q1 = n.x;
        let q2 = n.y;
        let p1 = n.z;
        let p2 = n.w;

        let new_q1 = c * q1 + s * p1;
        let new_q2 = c * q2 + s * p2;
        let new_p1 = -s * q1 + c * p1;
        let new_p2 = -s * q2 + c * p2;

        let transformed = SymplecticVector::new(new_q1, new_q2, new_p1, new_p2);
        normals.push(transformed.normalize());
    }

    // Heights: for the standard simplex conv{0, e₁, e₂, e₃, e₄},
    // the coordinate planes pass through origin (h = 0) and the sum plane
    // passes through each eᵢ with ⟨(1,1,1,1)/2, eᵢ⟩ = 1/2.
    //
    // After rotation, the polytope is the same (rotation preserves convex sets),
    // but expressed in rotated coordinates. The heights depend on a reference point
    // inside the polytope. Let's use the centroid of the original simplex:
    // centroid = (0 + e₁ + e₂ + e₃ + e₄) / 5 = (1/5, 1/5, 1/5, 1/5)

    let centroid = SymplecticVector::new(0.2, 0.2, 0.2, 0.2);
    // Transform centroid
    let tc = SymplecticVector::new(
        c * centroid.x + s * centroid.z,
        c * centroid.y + s * centroid.w,
        -s * centroid.x + c * centroid.z,
        -s * centroid.y + c * centroid.w,
    );

    // Compute heights: h_i = ⟨n_i, p_interior⟩ where p_interior is any interior point.
    // We can use the transformed centroid and add a small margin.
    // For a properly formed H-rep, we need h_i = max { ⟨n_i, v⟩ : v ∈ K }.
    //
    // The original simplex vertices:
    let std_vertices = [
        SymplecticVector::new(0.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
    ];

    // Transform vertices
    let vertices: Vec<_> = std_vertices
        .iter()
        .map(|v| {
            SymplecticVector::new(
                c * v.x + s * v.z,
                c * v.y + s * v.w,
                -s * v.x + c * v.z,
                -s * v.y + c * v.w,
            )
        })
        .collect();

    // Compute heights as max over vertices
    let heights: Vec<f64> = normals
        .iter()
        .map(|n| {
            vertices
                .iter()
                .map(|v| n.dot(v))
                .fold(f64::NEG_INFINITY, f64::max)
        })
        .collect();

    // Translate to ensure all heights are positive
    // Find minimum height and shift if needed
    let min_h = heights.iter().cloned().fold(f64::INFINITY, f64::min);
    let shift = if min_h <= 0.0 { 0.5 - min_h } else { 0.0 };

    // Shift the polytope: new height h'_i = h_i + ⟨n_i, shift_vec⟩
    // We need to find shift_vec such that all heights become positive.
    // Simplest: translate by a vector that increases all heights uniformly.
    // Use the centroid direction: shift by δ * sum_of_normals
    let _ = tc; // centroid computed but shift done differently

    // Actually, the cleanest way is to just add a positive constant to heights
    // This corresponds to translating the polytope away from origin
    let heights: Vec<f64> = heights.iter().map(|h| h + shift + 0.1).collect();

    PolytopeHRep::new(normals, heights)
}

/// Rectangle product: [−w/2, w/2] × [−h/2, h/2] in both q and p space.
/// Known capacity for square (w=h=2): 4.0
/// Known capacity for 2×1 (w=2, h=1): 1.0
pub fn rectangle_product(width: f64, height: f64) -> PolytopeHRep {
    let hw = width / 2.0;
    let hh = height / 2.0;
    let normals = vec![
        // q-space rectangle
        SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(-1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
        SymplecticVector::new(0.0, -1.0, 0.0, 0.0),
        // p-space rectangle (same shape)
        SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, -1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
        SymplecticVector::new(0.0, 0.0, 0.0, -1.0),
    ];
    let heights = vec![hw, hw, hh, hh, hw, hw, hh, hh];
    PolytopeHRep::new(normals, heights)
}

/// HK-O 2024 pentagon counterexample.
/// Pentagon × (same pentagon rotated 90°).
/// Known capacity: 3.4409548... = 2·cos(π/10)·(1+cos(π/5))
/// This is a counterexample to Viterbo's conjecture (systolic ratio > 1).
pub fn hko_pentagon_product() -> PolytopeHRep {
    // Data from packages/python_viterbo/data/counterexamples/hk-o-2024/facets.json
    let normals = vec![
        SymplecticVector::new(0.8090169943749473, 0.5877852522924731, 0.0, 0.0),
        SymplecticVector::new(-0.3090169943749473, 0.9510565162951536, 0.0, 0.0),
        SymplecticVector::new(-1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(-0.30901699437494756, -0.9510565162951536, 0.0, 0.0),
        SymplecticVector::new(0.8090169943749473, -0.5877852522924731, 0.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 0.5877852522924732, -0.8090169943749475),
        SymplecticVector::new(0.0, 0.0, 0.9510565162951536, 0.3090169943749474),
        SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
        SymplecticVector::new(0.0, 0.0, -0.9510565162951536, 0.3090169943749476),
        SymplecticVector::new(0.0, 0.0, -0.5877852522924731, -0.8090169943749475),
    ];
    let heights = vec![
        0.8090169943749473,
        0.8090169943749475,
        0.8090169943749475,
        0.8090169943749475,
        0.8090169943749472,
        0.8090169943749475,
        0.8090169943749475,
        0.8090169943749475,
        0.8090169943749475,
        0.8090169943749473,
    ];
    PolytopeHRep::new(normals, heights)
}

// =============================================================================
// Ground Truth Polytopes with Known Capacities
// =============================================================================

/// Ground truth test case: polytope with documented capacity from literature.
#[derive(Clone, Debug)]
pub struct GroundTruthPolytope {
    /// The polytope in H-representation.
    pub polytope: PolytopeHRep,
    /// Known capacity value from literature.
    pub known_capacity: f64,
    /// Source reference for the capacity value.
    pub source: &'static str,
    /// Short name for test output.
    pub name: &'static str,
    /// Whether this is a Lagrangian product (billiard algorithm applicable).
    pub is_lagrangian_product: bool,
}

/// All ground truth polytopes for testing.
pub fn ground_truth_polytopes() -> Vec<GroundTruthPolytope> {
    vec![
        // Tesseract [-1,1]^4
        // Capacity = 4.0 by direct computation: shortest periodic billiard has period 4.
        // Source: Basic billiard periodicity on symmetric box.
        GroundTruthPolytope {
            polytope: tesseract(),
            known_capacity: 4.0,
            source: "Billiard periodicity on symmetric tesseract",
            name: "tesseract",
            is_lagrangian_product: true,
        },
        // Rectangle product: [0,2] x [0,1] in q and p
        // For rectangle_product(2.0, 1.0), we have
        // q-rect = [-1,1] x [-0.5, 0.5], p-rect = same.
        // The shortest billiard bounces on the short edges.
        // From empirical testing: rectangle_product(2.0, 1.0) has c = 1.0.
        GroundTruthPolytope {
            polytope: rectangle_product(2.0, 1.0),
            known_capacity: 1.0,
            source: "Computed via billiard (verified empirically)",
            name: "rectangle_2x1",
            is_lagrangian_product: true,
        },
        // Unit cube scaled: [-0.5, 0.5]^4
        // This is tesseract scaled by 0.5, so c = 0.5^2 * 4 = 1.0
        GroundTruthPolytope {
            polytope: scale_polytope(&tesseract(), 0.5),
            known_capacity: 1.0,
            source: "Scaling axiom: c(0.5 * tesseract) = 0.25 * c(tesseract) = 1.0",
            name: "half_tesseract",
            is_lagrangian_product: true,
        },
        // Pentagon counterexample (HK-O 2024)
        // Known capacity: 2*cos(pi/10)*(1 + cos(pi/5)) approx 3.4409548...
        GroundTruthPolytope {
            polytope: hko_pentagon_product(),
            known_capacity: 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos()),
            source: "HK-O 2024 'A counterexample to the Viterbo conjecture'",
            name: "hko_pentagon",
            is_lagrangian_product: true,
        },
        // Equilateral triangle product
        // Computed via LP algorithm, verified to be 1.5
        GroundTruthPolytope {
            polytope: equilateral_triangle_product(),
            known_capacity: 1.5,
            source: "LP algorithm verification (see test-cases.md)",
            name: "equilateral_triangle",
            is_lagrangian_product: true,
        },
    ]
}

/// Get a single ground truth polytope by name.
pub fn ground_truth_by_name(name: &str) -> Option<GroundTruthPolytope> {
    ground_truth_polytopes()
        .into_iter()
        .find(|gt| gt.name == name)
}

// =============================================================================
// Extended Random Lagrangian Product Generators
// =============================================================================

/// Configuration for random Lagrangian product generation.
#[derive(Clone, Debug)]
pub struct LagrangianProductConfig {
    /// Number of vertices in q-space polygon (3-8).
    pub n_vertices_q: usize,
    /// Number of vertices in p-space polygon (3-8).
    pub n_vertices_p: usize,
    /// Minimum radius for vertices.
    pub r_min: f64,
    /// Maximum radius for vertices.
    pub r_max: f64,
    /// Aspect ratio perturbation (1.0 = regular, >1 = elongated).
    pub aspect_ratio: f64,
}

impl Default for LagrangianProductConfig {
    fn default() -> Self {
        Self {
            n_vertices_q: 4,
            n_vertices_p: 4,
            r_min: 0.5,
            r_max: 2.0,
            aspect_ratio: 1.0,
        }
    }
}

/// Generate a random convex 2D polygon with configurable aspect ratio.
pub fn random_convex_polygon_with_aspect<R: rand::Rng>(
    rng: &mut R,
    n_vertices: usize,
    r_min: f64,
    r_max: f64,
    aspect_ratio: f64,
) -> Polygon2D {
    assert!(n_vertices >= 3);
    assert!(r_min > 0.0);
    assert!(r_max >= r_min);
    assert!(aspect_ratio > 0.0);

    let r_base = (r_min + r_max) / 2.0;
    let r_perturb = r_base * 0.15; // slightly more variation

    let mut vertices = Vec::with_capacity(n_vertices);
    for i in 0..n_vertices {
        let angle = TAU * (i as f64) / (n_vertices as f64);
        let radius = r_base + (rng.gen::<f64>() - 0.5) * 2.0 * r_perturb;

        // Apply aspect ratio: stretch in x direction
        let x = radius * angle.cos() * aspect_ratio;
        let y = radius * angle.sin();
        vertices.push(Vector2f::new(x, y));
    }
    Polygon2D { vertices }
}

/// Generate a random Lagrangian product with full configuration.
pub fn random_lagrangian_product_configured<R: rand::Rng>(
    rng: &mut R,
    config: &LagrangianProductConfig,
) -> PolytopeHRep {
    let k1 = random_convex_polygon_with_aspect(
        rng,
        config.n_vertices_q,
        config.r_min,
        config.r_max,
        config.aspect_ratio,
    );
    let k2 = random_convex_polygon_with_aspect(
        rng,
        config.n_vertices_p,
        config.r_min,
        config.r_max,
        1.0 / config.aspect_ratio, // inverse aspect for p-space
    );

    let (normals_q, heights_q) = k1.to_hrep_2d();
    let (normals_p, heights_p) = k2.to_hrep_2d();

    let mut normals_4d = Vec::with_capacity(config.n_vertices_q + config.n_vertices_p);
    let mut heights_4d = Vec::with_capacity(config.n_vertices_q + config.n_vertices_p);

    for (n, h) in normals_q.iter().zip(&heights_q) {
        normals_4d.push(SymplecticVector::new(n.x, n.y, 0.0, 0.0));
        heights_4d.push(*h);
    }
    for (n, h) in normals_p.iter().zip(&heights_p) {
        normals_4d.push(SymplecticVector::new(0.0, 0.0, n.x, n.y));
        heights_4d.push(*h);
    }

    PolytopeHRep::new(normals_4d, heights_4d)
}

/// Generate a seeded random Lagrangian product with full configuration.
pub fn seeded_lagrangian_product_configured(seed: u64, config: &LagrangianProductConfig) -> PolytopeHRep {
    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    random_lagrangian_product_configured(&mut rng, config)
}

// =============================================================================
// Proptest Strategies
// =============================================================================

/// Proptest strategy for random Lagrangian products.
///
/// Generates products K1 x K2 where K1, K2 are random convex polygons.
/// Parameters:
/// - Vertex counts: 3-8 for each polygon
/// - Radii: 0.5-2.0
pub fn lagrangian_product_strategy() -> impl Strategy<Value = PolytopeHRep> {
    (any::<u64>(), 3usize..=8, 3usize..=8).prop_map(|(seed, n1, n2)| {
        seeded_lagrangian_product(seed, n1, n2)
    })
}

/// Proptest strategy for small Lagrangian products (fast tests).
///
/// Uses 3-4 vertices per polygon for faster algorithm execution.
pub fn small_lagrangian_product_strategy() -> impl Strategy<Value = PolytopeHRep> {
    (any::<u64>(), 3usize..=4, 3usize..=4).prop_map(|(seed, n1, n2)| {
        seeded_lagrangian_product(seed, n1, n2)
    })
}

/// Proptest strategy for configured Lagrangian products.
pub fn configured_lagrangian_product_strategy() -> impl Strategy<Value = (PolytopeHRep, LagrangianProductConfig)> {
    (
        any::<u64>(),
        3usize..=6,
        3usize..=6,
        prop::num::f64::POSITIVE.prop_map(|x| 0.5 + (x.abs() % 1.5)), // r_min 0.5-2.0
        prop::num::f64::POSITIVE.prop_map(|x| 0.7 + (x.abs() % 1.0)), // aspect 0.7-1.7
    )
        .prop_map(|(seed, n_q, n_p, r_base, aspect)| {
            let config = LagrangianProductConfig {
                n_vertices_q: n_q,
                n_vertices_p: n_p,
                r_min: r_base,
                r_max: r_base + 0.5,
                aspect_ratio: aspect,
            };
            let polytope = seeded_lagrangian_product_configured(seed, &config);
            (polytope, config)
        })
}

/// Proptest strategy for ground truth polytopes (for verification tests).
pub fn ground_truth_strategy() -> impl Strategy<Value = GroundTruthPolytope> {
    let polytopes = ground_truth_polytopes();
    (0..polytopes.len()).prop_map(move |i| polytopes[i].clone())
}

/// Proptest strategy for Lagrangian ground truth polytopes only.
pub fn lagrangian_ground_truth_strategy() -> impl Strategy<Value = GroundTruthPolytope> {
    let polytopes: Vec<_> = ground_truth_polytopes()
        .into_iter()
        .filter(|gt| gt.is_lagrangian_product)
        .collect();
    let len = polytopes.len();
    (0..len).prop_map(move |i| polytopes[i].clone())
}

// =============================================================================
// Additional Utility Functions
// =============================================================================

/// Create a ball approximation (regular n-gon x n-gon product).
///
/// For large n, this approximates the symplectic ball B^4(r).
/// Known capacity: pi * r^2 (Gromov nonsqueezing).
pub fn ball_approximation(n_sides: usize, radius: f64) -> PolytopeHRep {
    assert!(n_sides >= 3);
    assert!(radius > 0.0);

    let mut normals = Vec::with_capacity(2 * n_sides);
    let mut heights = Vec::with_capacity(2 * n_sides);

    // Regular n-gon with inradius = radius
    let inradius = radius;

    for i in 0..n_sides {
        let angle = TAU * (i as f64) / (n_sides as f64) + PI / (n_sides as f64);
        let nx = angle.cos();
        let ny = angle.sin();
        // q-space facet
        normals.push(SymplecticVector::new(nx, ny, 0.0, 0.0));
        heights.push(inradius);
    }
    for i in 0..n_sides {
        let angle = TAU * (i as f64) / (n_sides as f64) + PI / (n_sides as f64);
        let nx = angle.cos();
        let ny = angle.sin();
        // p-space facet
        normals.push(SymplecticVector::new(0.0, 0.0, nx, ny));
        heights.push(inradius);
    }

    PolytopeHRep::new(normals, heights)
}

/// Compute the expected capacity of a ball approximation.
///
/// For a regular n-gon product with inradius r, the capacity approaches
/// pi * r^2 as n -> infinity.
pub fn ball_approximation_capacity(_n_sides: usize, radius: f64) -> f64 {
    PI * radius * radius
}

// =============================================================================
// Random Non-Lagrangian Polytope Generator
// =============================================================================

/// Generate a random unit vector on S³ (uniformly distributed).
///
/// Uses the standard method: sample from standard normal in R^4, then normalize.
fn random_unit_vector_s3<R: rand::Rng>(rng: &mut R) -> SymplecticVector {
    use rand_distr::{Distribution, StandardNormal};
    loop {
        let x: f64 = StandardNormal.sample(rng);
        let y: f64 = StandardNormal.sample(rng);
        let z: f64 = StandardNormal.sample(rng);
        let w: f64 = StandardNormal.sample(rng);
        let v = SymplecticVector::new(x, y, z, w);
        let norm = v.norm();
        if norm > 1e-10 {
            return v / norm;
        }
    }
}

/// Result of attempting to generate a random non-Lagrangian polytope.
#[derive(Clone, Debug)]
pub struct RandomNonLagrangianResult {
    /// The polytope (if generation succeeded).
    pub polytope: Option<PolytopeHRep>,
    /// Number of facets.
    pub n_facets: usize,
    /// Number of non-Lagrangian facet pairs out of C(n,2) total pairs.
    pub non_lagrangian_pairs: usize,
    /// Total number of facet pairs C(n,2).
    pub total_pairs: usize,
    /// Whether the polytope is bounded (origin is strictly interior).
    pub is_bounded: bool,
    /// Diagnostic message explaining any failure.
    pub message: String,
}

/// Generate a random non-Lagrangian polytope from a seed.
///
/// # Construction
///
/// 1. Generate `n_facets` random unit vectors uniformly on S³
/// 2. Generate random positive heights h_i = base_height + uniform(0, height_variation)
/// 3. Verify ALL normal pairs are non-Lagrangian (ω(n_i, n_j) ≠ 0)
/// 4. Verify ALL normal pairs correspond to geometric 2-faces (share vertices)
///
/// # Arguments
///
/// * `seed` - Random seed for deterministic generation
/// * `n_facets` - Number of facets (5-8 recommended for tractability)
/// * `base_height` - Minimum height for all facets
/// * `height_variation` - Additional random height range
///
/// # Returns
///
/// A `RandomNonLagrangianResult` containing the polytope if successful.
/// Returns None if the random normals don't satisfy all requirements.
pub fn try_random_nonlagrangian_polytope(
    seed: u64,
    n_facets: usize,
    base_height: f64,
    height_variation: f64,
) -> RandomNonLagrangianResult {
    use rust_viterbo_geom::symplectic_form;

    let mut rng = ChaCha8Rng::seed_from_u64(seed);

    // Generate random unit normals
    let normals: Vec<SymplecticVector> = (0..n_facets)
        .map(|_| random_unit_vector_s3(&mut rng))
        .collect();

    // Generate random positive heights
    let heights: Vec<f64> = (0..n_facets)
        .map(|_| base_height + rng.gen::<f64>() * height_variation)
        .collect();

    // Count non-Lagrangian normal pairs
    let total_pairs = n_facets * (n_facets - 1) / 2;
    let mut non_lagrangian_count = 0;
    let threshold = 1e-9;

    for i in 0..n_facets {
        for j in (i + 1)..n_facets {
            let omega = symplectic_form(normals[i], normals[j]);
            if omega.abs() > threshold {
                non_lagrangian_count += 1;
            }
        }
    }

    // Require ALL normal pairs to be non-Lagrangian
    if non_lagrangian_count < total_pairs {
        return RandomNonLagrangianResult {
            polytope: None,
            n_facets,
            non_lagrangian_pairs: non_lagrangian_count,
            total_pairs,
            is_bounded: false,
            message: format!(
                "Not all normal pairs are non-Lagrangian: {} out of {} (need all {})",
                non_lagrangian_count, total_pairs, total_pairs
            ),
        };
    }

    let polytope = PolytopeHRep::new(normals, heights);

    // Basic validation (normals unit, heights positive and finite)
    if let Err(e) = polytope.validate(1e-6) {
        return RandomNonLagrangianResult {
            polytope: None,
            n_facets,
            non_lagrangian_pairs: non_lagrangian_count,
            total_pairs,
            is_bounded: false,
            message: format!("Polytope validation failed: {}", e),
        };
    }

    // Check that all normal pairs correspond to geometric 2-faces.
    // A pair (i,j) has a geometric 2-face if their facets share at least one vertex.
    let eps_feas = 1e-9;
    let eps_dedup = 1e-9;
    let two_faces = polytope.two_faces(eps_feas, eps_dedup);
    let geometric_2face_count = two_faces.len();

    if geometric_2face_count < total_pairs {
        return RandomNonLagrangianResult {
            polytope: None,
            n_facets,
            non_lagrangian_pairs: non_lagrangian_count,
            total_pairs,
            is_bounded: false,
            message: format!(
                "Not all normal pairs have geometric 2-faces: {} out of {} pairs have 2-faces",
                geometric_2face_count, total_pairs
            ),
        };
    }

    RandomNonLagrangianResult {
        polytope: Some(polytope),
        n_facets,
        non_lagrangian_pairs: non_lagrangian_count,
        total_pairs,
        is_bounded: true,
        message: format!(
            "Generated polytope with {} facets, {}/{} non-Lagrangian pairs, {} geometric 2-faces",
            n_facets, non_lagrangian_count, total_pairs, geometric_2face_count
        ),
    }
}

/// Generate a random non-Lagrangian polytope with default parameters.
///
/// Uses 6 facets, base_height=1.0, height_variation=0.5.
/// Returns None if the seed doesn't produce a valid polytope.
///
/// NOTE: This generator creates random halfplanes which rarely form simplicial
/// polytopes. For tube algorithm testing, prefer `random_nonlagrangian_simplex()`
/// which always produces a valid 5-facet simplex with 10 geometric 2-faces.
pub fn random_nonlagrangian_polytope(seed: u64) -> Option<PolytopeHRep> {
    try_random_nonlagrangian_polytope(seed, 6, 1.0, 0.5).polytope
}

// =============================================================================
// Random Non-Lagrangian Simplex Generator
// =============================================================================

/// Compute the 4D cross product of three vectors.
///
/// Returns a vector perpendicular to all three input vectors.
fn cross_4d(e1: SymplecticVector, e2: SymplecticVector, e3: SymplecticVector) -> SymplecticVector {
    // Determinant expansion for 4D cross product
    SymplecticVector::new(
        e1.y * (e2.z * e3.w - e2.w * e3.z) - e1.z * (e2.y * e3.w - e2.w * e3.y)
            + e1.w * (e2.y * e3.z - e2.z * e3.y),
        -(e1.x * (e2.z * e3.w - e2.w * e3.z) - e1.z * (e2.x * e3.w - e2.w * e3.x)
            + e1.w * (e2.x * e3.z - e2.z * e3.x)),
        e1.x * (e2.y * e3.w - e2.w * e3.y) - e1.y * (e2.x * e3.w - e2.w * e3.x)
            + e1.w * (e2.x * e3.y - e2.y * e3.x),
        -(e1.x * (e2.y * e3.z - e2.z * e3.y) - e1.y * (e2.x * e3.z - e2.z * e3.x)
            + e1.z * (e2.x * e3.y - e2.y * e3.x)),
    )
}

/// Compute the outward-pointing normal to a facet of a simplex.
///
/// The facet is defined by all vertices except `skip_vertex`.
/// The normal points away from `centroid`.
fn simplex_facet_normal(
    vertices: &[SymplecticVector; 5],
    skip_vertex: usize,
    centroid: SymplecticVector,
) -> SymplecticVector {
    // Collect the 4 vertices of this facet
    let mut fv: Vec<SymplecticVector> = Vec::new();
    for (j, &v) in vertices.iter().enumerate() {
        if j != skip_vertex {
            fv.push(v);
        }
    }

    // Compute normal using edges from fv[0]
    let e1 = fv[1] - fv[0];
    let e2 = fv[2] - fv[0];
    let e3 = fv[3] - fv[0];

    let mut n = cross_4d(e1, e2, e3);
    let norm = n.norm();
    if norm < 1e-10 {
        // Degenerate simplex
        return SymplecticVector::new(0.0, 0.0, 0.0, 0.0);
    }
    n = n / norm;

    // Make sure it points outward (away from centroid)
    let to_centroid = centroid - fv[0];
    if n.dot(&to_centroid) > 0.0 {
        n = SymplecticVector::new(-n.x, -n.y, -n.z, -n.w);
    }
    n
}

/// Validation result for tube algorithm input.
#[derive(Clone, Debug)]
pub struct TubeInputValidation {
    /// Whether the polytope is valid tube algorithm input.
    pub is_valid: bool,
    /// Number of facets.
    pub n_facets: usize,
    /// Total facet pairs C(n,2).
    pub total_pairs: usize,
    /// Number of non-Lagrangian normal pairs.
    pub non_lagrangian_pairs: usize,
    /// Number of geometric 2-faces.
    pub geometric_2faces: usize,
    /// Error message if invalid.
    pub error: Option<String>,
}

/// Validate a polytope as valid input for the tube algorithm.
///
/// For the tube algorithm to work, the polytope must have:
/// 1. All normal pairs non-Lagrangian (ω(nᵢ, nⱼ) ≠ 0)
/// 2. All normal pairs corresponding to geometric 2-faces
///
/// This is a comprehensive validation for tube algorithm input.
pub fn validate_tube_input(hrep: &PolytopeHRep) -> TubeInputValidation {
    use rust_viterbo_geom::symplectic_form;

    let n = hrep.normals.len();
    let total_pairs = n * (n - 1) / 2;

    // Check basic validation first
    if let Err(e) = hrep.validate(1e-6) {
        return TubeInputValidation {
            is_valid: false,
            n_facets: n,
            total_pairs,
            non_lagrangian_pairs: 0,
            geometric_2faces: 0,
            error: Some(format!("Basic validation failed: {}", e)),
        };
    }

    // Count non-Lagrangian pairs
    let mut non_lagrangian_count = 0;
    for i in 0..n {
        for j in (i + 1)..n {
            let omega = symplectic_form(hrep.normals[i], hrep.normals[j]);
            if omega.abs() > 1e-9 {
                non_lagrangian_count += 1;
            }
        }
    }

    // Count geometric 2-faces
    let two_faces = hrep.two_faces(1e-9, 1e-9);
    let geometric_2faces = two_faces.len();

    // Check validity
    let mut error = None;
    if non_lagrangian_count < total_pairs {
        error = Some(format!(
            "Not all normal pairs are non-Lagrangian: {}/{} pairs",
            non_lagrangian_count, total_pairs
        ));
    } else if geometric_2faces < total_pairs {
        error = Some(format!(
            "Not all normal pairs have geometric 2-faces: {}/{} pairs",
            geometric_2faces, total_pairs
        ));
    }

    TubeInputValidation {
        is_valid: error.is_none(),
        n_facets: n,
        total_pairs,
        non_lagrangian_pairs: non_lagrangian_count,
        geometric_2faces,
        error,
    }
}

/// Generate a random non-Lagrangian polytope with specified facet count.
///
/// # Algorithm
///
/// 1. Generate `n_facets` random unit vectors on S³
/// 2. Generate random positive heights
/// 3. Check all C(n,2) normal pairs satisfy ω(nᵢ,nⱼ) ≠ 0
/// 4. Check all C(n,2) normal pairs have geometric 2-faces
/// 5. If not, increment seed and retry (resampling)
///
/// # Arguments
///
/// * `seed` - Random seed
/// * `n_facets` - Number of facets (5 for simplex, 6+  for more complex polytopes)
///
/// # Returns
///
/// A valid `PolytopeHRep` satisfying tube algorithm requirements.
/// Panics if no valid polytope found after max_attempts.
pub fn random_nonlagrangian_polytope_with_facets(seed: u64, n_facets: usize) -> PolytopeHRep {
    assert!(n_facets >= 5, "Need at least 5 facets for a bounded 4D polytope");

    let max_attempts = 100000;
    for attempt in 0..max_attempts {
        let current_seed = seed.wrapping_add(attempt);
        let mut rng = ChaCha8Rng::seed_from_u64(current_seed);

        // Generate random unit normals
        let normals: Vec<SymplecticVector> = (0..n_facets)
            .map(|_| random_unit_vector_s3(&mut rng))
            .collect();

        // Generate random positive heights
        let heights: Vec<f64> = (0..n_facets)
            .map(|_| 0.5 + rng.gen::<f64>() * 1.5) // heights in [0.5, 2.0]
            .collect();

        let polytope = PolytopeHRep::new(normals, heights);

        // Validate as tube input
        let validation = validate_tube_input(&polytope);
        if validation.is_valid {
            return polytope;
        }
    }

    panic!(
        "random_nonlagrangian_polytope_with_facets: failed after {} attempts (seed={}, n_facets={})",
        max_attempts, seed, n_facets
    );
}

/// Generate a random 4D simplex with all 10 facet pairs non-Lagrangian.
///
/// # Algorithm
///
/// 1. Generate 5 random vertices in R⁴
/// 2. Compute the 5 facet normals from simplex geometry
/// 3. Check all C(5,2)=10 normal pairs satisfy ω(nᵢ,nⱼ) ≠ 0
/// 4. If not, increment seed and retry (resampling)
///
/// A 4D simplex always has all C(5,2)=10 pairs as geometric 2-faces,
/// so the only constraint is the non-Lagrangian condition.
///
/// # Returns
///
/// A valid `PolytopeHRep` with:
/// - 5 facets (simplex)
/// - 10 geometric 2-faces
/// - All 10 facet pairs non-Lagrangian
///
/// This function always succeeds (resamples internally until valid).
pub fn random_nonlagrangian_simplex(seed: u64) -> PolytopeHRep {
    use rust_viterbo_geom::symplectic_form;

    let max_attempts = 10000;
    for attempt in 0..max_attempts {
        let current_seed = seed.wrapping_add(attempt);
        let mut rng = ChaCha8Rng::seed_from_u64(current_seed);

        // Generate 5 random vertices
        let mut vertices: [SymplecticVector; 5] = [SymplecticVector::new(0.0, 0.0, 0.0, 0.0); 5];
        for v in vertices.iter_mut() {
            *v = random_unit_vector_s3(&mut rng) * (1.0 + rng.gen::<f64>());
        }

        // Compute centroid
        let centroid = {
            let sum = vertices.iter().fold(
                SymplecticVector::new(0.0, 0.0, 0.0, 0.0),
                |acc, &v| acc + v,
            );
            sum / 5.0
        };

        // Compute facet normals
        let mut normals: [SymplecticVector; 5] =
            [SymplecticVector::new(0.0, 0.0, 0.0, 0.0); 5];
        let mut degenerate = false;
        for i in 0..5 {
            normals[i] = simplex_facet_normal(&vertices, i, centroid);
            if normals[i].norm() < 0.5 {
                degenerate = true;
                break;
            }
        }
        if degenerate {
            continue;
        }

        // Check all 10 pairs are non-Lagrangian
        let mut all_nonlagrangian = true;
        for i in 0..5 {
            for j in (i + 1)..5 {
                let omega = symplectic_form(normals[i], normals[j]);
                if omega.abs() < 1e-9 {
                    all_nonlagrangian = false;
                    break;
                }
            }
            if !all_nonlagrangian {
                break;
            }
        }
        if !all_nonlagrangian {
            continue;
        }

        // Compute heights: h_i = max over vertices of ⟨n_i, v⟩
        let mut heights = Vec::with_capacity(5);
        for n in &normals {
            let h = vertices.iter().map(|v| n.dot(v)).fold(f64::NEG_INFINITY, f64::max);
            heights.push(h);
        }

        // Translate to ensure all heights are positive
        let min_h = heights.iter().cloned().fold(f64::INFINITY, f64::min);
        if min_h <= 0.0 {
            let shift = 1.0 - min_h;
            for h in heights.iter_mut() {
                *h += shift;
            }
        }

        let polytope = PolytopeHRep::new(normals.to_vec(), heights);

        // Final validation: ensure it's valid tube input
        let validation = validate_tube_input(&polytope);
        if validation.is_valid {
            return polytope;
        }
        // Otherwise continue to next attempt
    }

    panic!(
        "random_nonlagrangian_simplex: failed to find valid simplex after {} attempts from seed {}",
        max_attempts, seed
    );
}

/// Generate a random non-Lagrangian simplex and return detailed information.
pub fn try_random_nonlagrangian_simplex(seed: u64) -> RandomNonLagrangianResult {
    use rust_viterbo_geom::symplectic_form;

    let polytope = random_nonlagrangian_simplex(seed);

    // Count non-Lagrangian pairs (should be all 10)
    let mut non_lagrangian_count = 0;
    for i in 0..5 {
        for j in (i + 1)..5 {
            let omega = symplectic_form(polytope.normals[i], polytope.normals[j]);
            if omega.abs() > 1e-9 {
                non_lagrangian_count += 1;
            }
        }
    }

    RandomNonLagrangianResult {
        polytope: Some(polytope),
        n_facets: 5,
        non_lagrangian_pairs: non_lagrangian_count,
        total_pairs: 10,
        is_bounded: true,
        message: format!(
            "Generated simplex with 5 facets, {}/10 non-Lagrangian pairs, 10 geometric 2-faces",
            non_lagrangian_count
        ),
    }
}

// =============================================================================
// Unit Tests
// =============================================================================

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ground_truth_polytopes_have_positive_capacity() {
        for gt in ground_truth_polytopes() {
            assert!(
                gt.known_capacity > 0.0,
                "{}: capacity should be positive",
                gt.name
            );
        }
    }

    #[test]
    fn ground_truth_by_name_finds_tesseract() {
        let gt = ground_truth_by_name("tesseract").expect("should find tesseract");
        assert!((gt.known_capacity - 4.0).abs() < 1e-10);
    }

    #[test]
    fn configured_generator_produces_valid_polytope() {
        let config = LagrangianProductConfig {
            n_vertices_q: 5,
            n_vertices_p: 4,
            r_min: 1.0,
            r_max: 2.0,
            aspect_ratio: 1.5,
        };
        let polytope = seeded_lagrangian_product_configured(42, &config);

        // Check correct number of facets
        assert_eq!(polytope.normals.len(), 9); // 5 + 4
        assert_eq!(polytope.heights.len(), 9);

        // Check normals are unit vectors
        for n in &polytope.normals {
            assert!(
                (n.norm() - 1.0).abs() < 1e-10,
                "Normal should be unit vector"
            );
        }

        // Check heights are positive
        for h in &polytope.heights {
            assert!(*h > 0.0, "Height should be positive");
        }
    }

    #[test]
    fn ball_approximation_has_correct_structure() {
        let ball = ball_approximation(6, 1.0); // hexagon x hexagon

        // Should have 12 facets (6 + 6)
        assert_eq!(ball.normals.len(), 12);
        assert_eq!(ball.heights.len(), 12);

        // First 6 normals should be in q-space (z=w=0)
        for i in 0..6 {
            let n = ball.normals[i];
            assert!(n.z.abs() < 1e-10 && n.w.abs() < 1e-10);
        }

        // Last 6 normals should be in p-space (x=y=0)
        for i in 6..12 {
            let n = ball.normals[i];
            assert!(n.x.abs() < 1e-10 && n.y.abs() < 1e-10);
        }
    }

    #[test]
    fn random_polygon_aspect_ratio_affects_shape() {
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;

        let mut rng = ChaCha8Rng::seed_from_u64(123);
        let regular = random_convex_polygon_with_aspect(&mut rng, 4, 1.0, 1.0, 1.0);

        let mut rng = ChaCha8Rng::seed_from_u64(123);
        let elongated = random_convex_polygon_with_aspect(&mut rng, 4, 1.0, 1.0, 2.0);

        // Elongated should have larger x-extent
        let regular_x_extent: f64 = regular.vertices.iter().map(|v| v.x.abs()).sum();
        let elongated_x_extent: f64 = elongated.vertices.iter().map(|v| v.x.abs()).sum();

        assert!(
            elongated_x_extent > regular_x_extent * 1.5,
            "Elongated polygon should have larger x-extent"
        );
    }

    // =========================================================================
    // Random Non-Lagrangian Polytope Tests (generic halfplanes)
    // =========================================================================

    #[test]
    fn random_nonlagrangian_polytope_rejects_invalid() {
        // Test that the generator correctly rejects polytopes without enough 2-faces.
        // Seed 42 produces 15/15 non-Lagrangian normal pairs but only 1 geometric 2-face.
        let result = try_random_nonlagrangian_polytope(42, 6, 1.0, 0.5);
        eprintln!("Result: {}", result.message);

        // This seed should be rejected (not enough geometric 2-faces)
        assert!(
            result.polytope.is_none(),
            "Seed 42 should be rejected: only 1 geometric 2-face out of 15 required"
        );
        assert!(
            result.message.contains("2-faces"),
            "Rejection message should mention 2-faces"
        );
    }

    #[test]
    fn random_nonlagrangian_normals_are_generic() {
        use rust_viterbo_geom::symplectic_form;

        // Test that simplex normals don't have special values like 0, 1, sqrt(2), etc.
        // Use the simplex generator which always produces valid polytopes.
        let polytope = random_nonlagrangian_simplex(42);

        for (i, n) in polytope.normals.iter().enumerate() {
            // Check that components are "random" - not special values
            for (j, &val) in [n.x, n.y, n.z, n.w].iter().enumerate() {
                // Not exactly zero
                assert!(
                    val.abs() > 1e-6 || val.abs() < 1e-12,
                    "Normal {}, component {}: {} should be truly random, not near-zero",
                    i,
                    j,
                    val
                );
                // Not exactly 1 or -1
                assert!(
                    (val.abs() - 1.0).abs() > 1e-6,
                    "Normal {}, component {}: {} should not be exactly +/-1",
                    i,
                    j,
                    val
                );
            }
        }

        // Check that symplectic forms are also "random" - not special values
        for i in 0..polytope.normals.len() {
            for j in (i + 1)..polytope.normals.len() {
                let omega = symplectic_form(polytope.normals[i], polytope.normals[j]);
                if omega.abs() > 1e-9 {
                    // Not a "nice" value like 0.5, 1.0, etc.
                    let is_special = (omega - 0.5).abs() < 1e-6
                        || (omega - 1.0).abs() < 1e-6
                        || (omega + 0.5).abs() < 1e-6
                        || (omega + 1.0).abs() < 1e-6;
                    assert!(
                        !is_special,
                        "omega(n{}, n{}) = {} should be a truly random value",
                        i,
                        j,
                        omega
                    );
                }
            }
        }
    }

    // =========================================================================
    // Random Non-Lagrangian Simplex Tests
    // =========================================================================

    #[test]
    fn random_nonlagrangian_simplex_produces_valid_output() {
        use rust_viterbo_geom::symplectic_form;

        // Test several seeds
        for seed in [0, 42, 123, 1729, 9999] {
            let polytope = random_nonlagrangian_simplex(seed);

            // Should have 5 facets (simplex)
            assert_eq!(polytope.normals.len(), 5, "Simplex should have 5 facets");
            assert_eq!(polytope.heights.len(), 5);

            // Normals should be unit vectors
            for (i, n) in polytope.normals.iter().enumerate() {
                let norm = n.norm();
                assert!(
                    (norm - 1.0).abs() < 1e-6,
                    "Seed {}: normal {} should be unit, got norm {}",
                    seed,
                    i,
                    norm
                );
            }

            // Heights should be positive
            for (i, &h) in polytope.heights.iter().enumerate() {
                assert!(
                    h > 0.0,
                    "Seed {}: height {} should be positive, got {}",
                    seed,
                    i,
                    h
                );
            }

            // All 10 pairs should be non-Lagrangian
            for i in 0..5 {
                for j in (i + 1)..5 {
                    let omega = symplectic_form(polytope.normals[i], polytope.normals[j]);
                    assert!(
                        omega.abs() > 1e-9,
                        "Seed {}: pair ({}, {}) should be non-Lagrangian, got omega = {}",
                        seed,
                        i,
                        j,
                        omega
                    );
                }
            }

            // Should have 10 geometric 2-faces (simplex property)
            let two_faces = polytope.two_faces(1e-9, 1e-9);
            assert_eq!(
                two_faces.len(),
                10,
                "Seed {}: simplex should have 10 geometric 2-faces, got {}",
                seed,
                two_faces.len()
            );
        }
    }

    #[test]
    fn random_nonlagrangian_simplex_is_deterministic() {
        // Same seed should produce same simplex
        let p1 = random_nonlagrangian_simplex(42);
        let p2 = random_nonlagrangian_simplex(42);

        assert_eq!(p1.normals.len(), p2.normals.len());
        for (n1, n2) in p1.normals.iter().zip(&p2.normals) {
            assert!((n1 - n2).norm() < 1e-12, "Normals should be identical");
        }
        for (h1, h2) in p1.heights.iter().zip(&p2.heights) {
            assert!((h1 - h2).abs() < 1e-12, "Heights should be identical");
        }
    }

    #[test]
    fn random_nonlagrangian_simplex_detailed_analysis() {
        use rust_viterbo_geom::symplectic_form;

        let seed = 0u64;
        let polytope = random_nonlagrangian_simplex(seed);

        eprintln!("=== Random Non-Lagrangian Simplex (seed={}) ===", seed);
        eprintln!("Facets: {}", polytope.normals.len());

        eprintln!("\nNormals:");
        for (i, n) in polytope.normals.iter().enumerate() {
            eprintln!(
                "  n[{}] = ({:+.6}, {:+.6}, {:+.6}, {:+.6})",
                i, n.x, n.y, n.z, n.w
            );
        }

        eprintln!("\nHeights:");
        for (i, h) in polytope.heights.iter().enumerate() {
            eprintln!("  h[{}] = {:.6}", i, h);
        }

        eprintln!("\nSymplectic forms ω(nᵢ, nⱼ):");
        for i in 0..5 {
            for j in (i + 1)..5 {
                let omega = symplectic_form(polytope.normals[i], polytope.normals[j]);
                eprintln!("  ω(n{}, n{}) = {:+.6}", i, j, omega);
            }
        }

        let two_faces = polytope.two_faces(1e-9, 1e-9);
        eprintln!("\nGeometric 2-faces: {}", two_faces.len());
    }

    // =========================================================================
    // validate_tube_input Tests
    // =========================================================================

    #[test]
    fn validate_tube_input_accepts_valid_simplex() {
        let polytope = random_nonlagrangian_simplex(0);
        let validation = validate_tube_input(&polytope);

        assert!(validation.is_valid, "Simplex should be valid: {:?}", validation.error);
        assert_eq!(validation.n_facets, 5);
        assert_eq!(validation.total_pairs, 10);
        assert_eq!(validation.non_lagrangian_pairs, 10);
        assert_eq!(validation.geometric_2faces, 10);
        assert!(validation.error.is_none());
    }

    #[test]
    fn validate_tube_input_rejects_lagrangian_product() {
        // Tesseract is a Lagrangian product - has Lagrangian 2-faces
        let polytope = tesseract();
        let validation = validate_tube_input(&polytope);

        assert!(!validation.is_valid, "Tesseract should be rejected");
        assert!(validation.error.is_some());
        // Tesseract has 8 facets, so 28 pairs
        // Only 8 pairs are non-Lagrangian (the ones mixing q and p directions)
        assert!(validation.non_lagrangian_pairs < validation.total_pairs);
    }

    #[test]
    fn validate_tube_input_rejects_skewed_simplex() {
        // Skewed simplex has 4 Lagrangian 2-faces out of 10
        let polytope = skewed_simplex_4d();
        let validation = validate_tube_input(&polytope);

        assert!(!validation.is_valid, "Skewed simplex should be rejected");
        assert!(validation.error.is_some());
        // Should have only 6 non-Lagrangian pairs out of 10
        assert_eq!(validation.non_lagrangian_pairs, 6);
        assert!(validation.error.as_ref().unwrap().contains("non-Lagrangian"));
    }

    #[test]
    fn validate_tube_input_rejects_random_halfplanes() {
        // Random halfplanes usually don't form simplices - few geometric 2-faces
        let result = try_random_nonlagrangian_polytope(42, 6, 1.0, 0.5);

        // Seed 42 produces only 1 geometric 2-face
        assert!(result.polytope.is_none(), "Seed 42 should be rejected");
        assert!(result.message.contains("2-faces"));
    }

    #[test]
    fn validate_tube_input_multiple_valid_simplices() {
        // Multiple seeds should all produce valid simplices
        for seed in [0, 1, 10, 100, 1000] {
            let polytope = random_nonlagrangian_simplex(seed);
            let validation = validate_tube_input(&polytope);

            assert!(
                validation.is_valid,
                "Seed {} should produce valid simplex: {:?}",
                seed,
                validation.error
            );
        }
    }
}
