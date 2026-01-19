//! Test fixtures: polytopes and utilities used across test modules.

use rand::SeedableRng;
use rand_chacha::ChaCha8Rng;
use rust_viterbo_geom::{perturb_polytope_normals, PolytopeHRep, SymplecticVector, Vector2f};
use std::f64::consts::TAU;

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
            debug_assert!(height > 0.0, "Height should be positive for star-shaped polygon");
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
