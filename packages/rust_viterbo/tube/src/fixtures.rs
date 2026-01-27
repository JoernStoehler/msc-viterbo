//! Test fixtures for the tube algorithm.
//!
//! Provides standard polytopes for testing:
//! - `unit_cross_polytope()`: 16-cell, suitable for tube algorithm (no Lagrangian 2-faces)
//! - `unit_tesseract()`: Hypercube, rejected by tube algorithm (all 2-faces Lagrangian)
//! - `four_simplex()`: 5-cell, rejected by tube algorithm (has Lagrangian 2-faces)

use nalgebra::Vector4;

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
}
