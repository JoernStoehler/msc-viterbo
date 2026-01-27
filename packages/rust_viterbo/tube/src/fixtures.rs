//! Test fixtures for the tube algorithm.
//!
//! Provides standard polytopes for testing:
//! - `unit_cross_polytope()`: 16-cell, conv{±e₁, ±e₂, ±e₃, ±e₄}
//! - `unit_tesseract()`: Hypercube [-1,1]⁴

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
}
