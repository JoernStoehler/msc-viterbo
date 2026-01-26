//! Test fixtures for the tube algorithm.
//!
//! This module provides standard polytopes for testing:
//! - Unit cross-polytope (16 facets, NO Lagrangian 2-faces - suitable for tube algorithm)
//! - Unit tesseract (8 facets, all 2-faces Lagrangian - REJECTED by tube algorithm)

use nalgebra::Vector4;

use crate::polytope::PolytopeHRep;

/// Create a unit cross-polytope conv{±e₁, ±e₂, ±e₃, ±e₄}.
///
/// The cross-polytope (also called 16-cell or hyperoctahedron) is the dual of the tesseract.
/// It has 16 facets with normals proportional to (±1, ±1, ±1, ±1).
///
/// **Note on Lagrangian 2-faces:** The cross-polytope has NO Lagrangian 2-faces
/// when using proper vertex-based adjacency (two facets form a 2-face iff they
/// share ≥3 vertices). Adjacent facets have normals differing in exactly one sign,
/// and for such pairs ω(n_i, n_j) ≠ 0 always.
///
/// **Capacity:** Not independently known (see spec §4.4.2). The tube algorithm
/// can compute it; use this fixture to validate the algorithm's output.
pub fn unit_cross_polytope() -> PolytopeHRep {
    let mut normals = Vec::new();

    // Generate all 16 normals: (±1, ±1, ±1, ±1) / 2
    for &s1 in &[-1.0, 1.0] {
        for &s2 in &[-1.0, 1.0] {
            for &s3 in &[-1.0, 1.0] {
                for &s4 in &[-1.0, 1.0] {
                    normals.push(Vector4::new(s1, s2, s3, s4) / 2.0);
                }
            }
        }
    }

    // With normals (±1, ±1, ±1, ±1)/2 and heights = 0.5,
    // vertices are at ±eᵢ where eᵢ are standard basis vectors.
    // Check: ⟨(1,1,1,1)/2, (1,0,0,0)⟩ = 1/2 = 0.5, so e₁ is on the boundary.
    // Normals are unit: ||(1,1,1,1)/2|| = √(4·1/4)/2 = 1.

    PolytopeHRep::new(normals, vec![0.5; 16])
}

/// Create a scaled cross-polytope.
///
/// c(λK) = λ² c(K)
pub fn scaled_cross_polytope(lambda: f64) -> PolytopeHRep {
    let base = unit_cross_polytope();
    PolytopeHRep::new(base.normals, base.heights.iter().map(|&h| h * lambda).collect())
}

/// Create a unit tesseract [-1, 1]⁴.
///
/// **Note:** The tesseract is a Lagrangian product, so the tube algorithm
/// will reject it. Use for testing that the algorithm correctly detects
/// Lagrangian 2-faces.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polytope::PolytopeData;
    use crate::symplectic::symplectic_form;
    use crate::consts::EPS_LAGRANGIAN;

    #[test]
    fn test_cross_polytope_valid() {
        let cross = unit_cross_polytope();
        assert!(cross.validate().is_ok());
        assert_eq!(cross.num_facets(), 16);
    }

    #[test]
    fn test_cross_polytope_normals_are_unit() {
        let cross = unit_cross_polytope();
        for n in &cross.normals {
            let norm = n.norm();
            assert!((norm - 1.0).abs() < 1e-10, "Normal not unit: ||n|| = {}", norm);
        }
    }

    #[test]
    fn test_cross_polytope_has_no_lagrangian_2faces() {
        // The cross-polytope has NO Lagrangian 2-faces when using proper adjacency.
        // Two facets are adjacent (share a 2-face) iff their normals differ in exactly
        // one sign position. For such pairs, ω(n_i, n_j) ≠ 0 always.
        let cross = unit_cross_polytope();

        // Count adjacent pairs (differ in exactly one sign)
        fn differs_in_one_sign(n1: &Vector4<f64>, n2: &Vector4<f64>) -> bool {
            let diffs = (0..4)
                .filter(|&i| (n1[i].signum() - n2[i].signum()).abs() > 0.5)
                .count();
            diffs == 1
        }

        let mut lagrangian_count = 0;
        let mut non_lagrangian_count = 0;

        for i in 0..cross.normals.len() {
            for j in (i + 1)..cross.normals.len() {
                if differs_in_one_sign(&cross.normals[i], &cross.normals[j]) {
                    let omega = symplectic_form(&cross.normals[i], &cross.normals[j]);
                    if omega.abs() < EPS_LAGRANGIAN {
                        lagrangian_count += 1;
                    } else {
                        non_lagrangian_count += 1;
                    }
                }
            }
        }

        // With proper adjacency, cross-polytope has NO Lagrangian 2-faces
        assert_eq!(lagrangian_count, 0, "Expected 0 Lagrangian 2-faces, found {}", lagrangian_count);
        assert_eq!(non_lagrangian_count, 32, "Expected 32 non-Lagrangian 2-faces, found {}", non_lagrangian_count);
    }

    #[test]
    fn test_cross_polytope_preprocesses() {
        let cross = unit_cross_polytope();
        let data = PolytopeData::from_hrep(&cross).unwrap();

        // Cross-polytope has NO Lagrangian 2-faces (suitable for tube algorithm)
        assert!(!data.has_lagrangian_two_faces(),
            "Cross-polytope should have NO Lagrangian 2-faces");

        // All 32 true 2-faces should be enriched (non-Lagrangian)
        assert_eq!(data.two_faces.len(), 32, "Expected 32 2-faces");
        assert_eq!(data.two_faces_enriched.len(), 32, "Expected 32 enriched 2-faces");

        // Verify vertices were enumerated
        assert_eq!(data.vertices.len(), 8, "Cross-polytope should have 8 vertices");
    }

    #[test]
    fn test_tesseract_valid() {
        let tesseract = unit_tesseract();
        assert!(tesseract.validate().is_ok());
        assert_eq!(tesseract.num_facets(), 8);
    }

    #[test]
    fn test_tesseract_has_lagrangian_2faces() {
        let tesseract = unit_tesseract();
        let data = PolytopeData::from_hrep(&tesseract).unwrap();

        assert!(data.has_lagrangian_two_faces(),
            "Tesseract should have Lagrangian 2-faces");
    }

    #[test]
    fn test_scaling_preserves_normals() {
        let base = unit_cross_polytope();
        let scaled = scaled_cross_polytope(2.0);

        // Normals should be the same
        for (n1, n2) in base.normals.iter().zip(&scaled.normals) {
            assert!((n1 - n2).norm() < 1e-14);
        }

        // Heights should be scaled
        for (h1, h2) in base.heights.iter().zip(&scaled.heights) {
            assert!((h2 - h1 * 2.0).abs() < 1e-14);
        }
    }
}
