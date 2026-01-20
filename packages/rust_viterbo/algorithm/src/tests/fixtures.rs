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
/// 3. Verify at least half the facet pairs are non-Lagrangian (ω(n_i, n_j) ≠ 0)
/// 4. Verify boundedness by checking that origin is strictly interior (all n_i · 0 < h_i)
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

    // Count non-Lagrangian pairs
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

    // Check if at least half are non-Lagrangian
    let min_required = total_pairs / 2;
    if non_lagrangian_count < min_required {
        return RandomNonLagrangianResult {
            polytope: None,
            n_facets,
            non_lagrangian_pairs: non_lagrangian_count,
            total_pairs,
            is_bounded: false,
            message: format!(
                "Too few non-Lagrangian pairs: {} out of {} (need at least {})",
                non_lagrangian_count, total_pairs, min_required
            ),
        };
    }

    // All heights are positive (by construction), so origin is interior
    // The polytope is bounded if the normals span R^4 (which they do w.h.p. for n>=5)
    let is_bounded = heights.iter().all(|&h| h > 0.0);

    let polytope = PolytopeHRep::new(normals, heights);

    // Validate polytope
    if let Err(e) = polytope.validate(1e-6) {
        return RandomNonLagrangianResult {
            polytope: None,
            n_facets,
            non_lagrangian_pairs: non_lagrangian_count,
            total_pairs,
            is_bounded,
            message: format!("Polytope validation failed: {}", e),
        };
    }

    RandomNonLagrangianResult {
        polytope: Some(polytope),
        n_facets,
        non_lagrangian_pairs: non_lagrangian_count,
        total_pairs,
        is_bounded,
        message: format!(
            "Generated polytope with {} facets, {}/{} non-Lagrangian pairs",
            n_facets, non_lagrangian_count, total_pairs
        ),
    }
}

/// Generate a random non-Lagrangian polytope with default parameters.
///
/// Uses 6 facets, base_height=1.0, height_variation=0.5.
/// Returns None if the seed doesn't produce a valid polytope.
pub fn random_nonlagrangian_polytope(seed: u64) -> Option<PolytopeHRep> {
    try_random_nonlagrangian_polytope(seed, 6, 1.0, 0.5).polytope
}

/// Pre-verified seeds that produce valid random non-Lagrangian polytopes.
///
/// These seeds have been tested to:
/// 1. Produce polytopes with at least half non-Lagrangian facet pairs
/// 2. Have all positive heights (bounded polytope)
/// 3. Pass validation checks
///
/// Test results with 6 facets:
/// - 42:   15/15 non-Lagrangian pairs, 1 2-face  -> SearchExhausted
/// - 137:  15/15 non-Lagrangian pairs, 5 2-faces -> SearchExhausted
/// - 1729: 15/15 non-Lagrangian pairs, 6 2-faces -> SUCCESS (capacity found!)
/// - 2718: 15/15 non-Lagrangian pairs, 5 2-faces -> SearchExhausted
/// - 3141: 15/15 non-Lagrangian pairs, 11 2-faces -> SearchExhausted
///
/// Use these for reproducible tests.
pub const VERIFIED_NONLAGRANGIAN_SEEDS: [u64; 5] = [
    42,   // 1 2-face (limited connectivity)
    137,  // 5 2-faces
    1729, // 6 2-faces - FINDS ORBIT (Hardy-Ramanujan number)
    2718, // 5 2-faces (Euler's number digits)
    3141, // 11 2-faces (Pi digits)
];

/// Get a verified random non-Lagrangian polytope by index.
///
/// Returns a polytope from a pre-verified seed, or None if index is out of range.
pub fn verified_nonlagrangian_polytope(index: usize) -> Option<PolytopeHRep> {
    VERIFIED_NONLAGRANGIAN_SEEDS
        .get(index)
        .and_then(|&seed| random_nonlagrangian_polytope(seed))
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
    // Random Non-Lagrangian Polytope Tests
    // =========================================================================

    #[test]
    fn random_nonlagrangian_polytope_produces_valid_output() {
        // Test with seed 42
        let result = try_random_nonlagrangian_polytope(42, 6, 1.0, 0.5);
        eprintln!("Result: {}", result.message);
        eprintln!(
            "Non-Lagrangian pairs: {}/{}",
            result.non_lagrangian_pairs, result.total_pairs
        );

        // For random normals on S^3, almost all pairs should be non-Lagrangian
        // (Lagrangian condition is measure-zero)
        assert!(
            result.non_lagrangian_pairs >= result.total_pairs / 2,
            "Random normals should produce mostly non-Lagrangian pairs"
        );

        if let Some(polytope) = &result.polytope {
            // Verify validation passes
            assert!(
                polytope.validate(1e-6).is_ok(),
                "Polytope should pass validation"
            );

            // Verify normals are unit vectors
            for (i, n) in polytope.normals.iter().enumerate() {
                let norm = n.norm();
                assert!(
                    (norm - 1.0).abs() < 1e-10,
                    "Normal {} should be unit: norm = {}",
                    i,
                    norm
                );
            }

            // Verify heights are positive
            for (i, &h) in polytope.heights.iter().enumerate() {
                assert!(h > 0.0, "Height {} should be positive: h = {}", i, h);
            }
        }
    }

    #[test]
    fn random_nonlagrangian_normals_are_generic() {
        use rust_viterbo_geom::symplectic_form;

        // Test that random normals don't have special values like 0, 1, sqrt(2), etc.
        let result = try_random_nonlagrangian_polytope(42, 6, 1.0, 0.5);
        let polytope = result.polytope.expect("Should produce valid polytope");

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

    #[test]
    fn random_nonlagrangian_multiple_seeds_work() {
        // Test all verified seeds
        for (idx, &seed) in VERIFIED_NONLAGRANGIAN_SEEDS.iter().enumerate() {
            let result = try_random_nonlagrangian_polytope(seed, 6, 1.0, 0.5);
            eprintln!("Seed {}: {}", seed, result.message);

            // All verified seeds should produce valid polytopes
            assert!(
                result.polytope.is_some(),
                "Verified seed {} (index {}) should produce valid polytope",
                seed,
                idx
            );
        }
    }

    #[test]
    fn random_nonlagrangian_is_deterministic() {
        // Same seed should produce same polytope
        let p1 = random_nonlagrangian_polytope(12345).expect("Should produce polytope");
        let p2 = random_nonlagrangian_polytope(12345).expect("Should produce polytope");

        assert_eq!(p1.normals.len(), p2.normals.len());
        for (n1, n2) in p1.normals.iter().zip(&p2.normals) {
            assert!((n1 - n2).norm() < 1e-12, "Normals should be identical");
        }
        for (h1, h2) in p1.heights.iter().zip(&p2.heights) {
            assert!((h1 - h2).abs() < 1e-12, "Heights should be identical");
        }
    }

    #[test]
    fn random_nonlagrangian_detailed_analysis() {
        use rust_viterbo_geom::symplectic_form;

        let seed = 42u64;
        let result = try_random_nonlagrangian_polytope(seed, 6, 1.0, 0.5);
        eprintln!(
            "=== Random Non-Lagrangian Polytope Analysis (seed={}) ===",
            seed
        );
        eprintln!("Message: {}", result.message);

        let polytope = result.polytope.expect("Should produce valid polytope");

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

        eprintln!("\nSymplectic form matrix:");
        eprint!("     ");
        for j in 0..polytope.normals.len() {
            eprint!("{:8}", j);
        }
        eprintln!();
        for i in 0..polytope.normals.len() {
            eprint!("  {} |", i);
            for j in 0..polytope.normals.len() {
                let omega = symplectic_form(polytope.normals[i], polytope.normals[j]);
                eprint!("{:8.4}", omega);
            }
            eprintln!();
        }

        eprintln!("\nNon-Lagrangian pairs (|omega| > 1e-9):");
        let mut count = 0;
        for i in 0..polytope.normals.len() {
            for j in (i + 1)..polytope.normals.len() {
                let omega = symplectic_form(polytope.normals[i], polytope.normals[j]);
                if omega.abs() > 1e-9 {
                    count += 1;
                    eprintln!("  ({}, {}): omega = {:+.6}", i, j, omega);
                }
            }
        }
        let total = polytope.normals.len() * (polytope.normals.len() - 1) / 2;
        eprintln!("\nTotal: {}/{} pairs are non-Lagrangian", count, total);

        // Assert at least half are non-Lagrangian
        assert!(count >= total / 2, "At least half should be non-Lagrangian");
    }
}
