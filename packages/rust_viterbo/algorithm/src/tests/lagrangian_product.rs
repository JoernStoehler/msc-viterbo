//! Tests for Lagrangian product detection and structure.
//!
//! A Lagrangian product K₁ × K₂ ⊂ ℝ² × ℝ² has facets aligned with q-space
//! (first two coordinates) or p-space (last two coordinates).

use super::fixtures::{seeded_lagrangian_product, tesseract};
use crate::billiard::{extract_lagrangian_factors, Polygon2DSimple};
use rust_viterbo_geom::{PolytopeHRep, SymplecticVector};
use proptest::prelude::*;

// ============================================================================
// Proptest Strategies
// ============================================================================

fn lagrangian_product_strategy() -> impl Strategy<Value = rust_viterbo_geom::PolytopeHRep> {
    (any::<u64>(), 3usize..=5, 3usize..=5).prop_map(|(seed, n1, n2)| {
        seeded_lagrangian_product(seed, n1, n2)
    })
}

// ============================================================================
// Detection Tests
// ============================================================================

/// Tesseract is detected as a Lagrangian product.
#[test]
fn tesseract_is_lagrangian_product() {
    let hrep = tesseract();
    assert!(
        extract_lagrangian_factors(&hrep).is_some(),
        "Tesseract should be a Lagrangian product"
    );
}

/// Rotated tesseract is NOT a Lagrangian product in standard coordinates.
///
/// A symplectomorphism mixing (q₁, p₁) breaks the product structure K₁ × K₂.
#[test]
fn rotated_tesseract_is_not_lagrangian_product() {
    let hrep = tesseract();

    // Apply a symplectic rotation that mixes q₁ with p₁:
    // R(π/4) in the (q₁, p₁) plane
    let c = std::f64::consts::FRAC_1_SQRT_2;
    let s = std::f64::consts::FRAC_1_SQRT_2;

    let rotated_normals: Vec<SymplecticVector> = hrep.normals.iter().map(|n| {
        SymplecticVector::new(
            c * n[0] - s * n[2],
            n[1],
            s * n[0] + c * n[2],
            n[3],
        )
    }).collect();

    let rotated = PolytopeHRep::new(rotated_normals, hrep.heights.clone());

    assert!(
        extract_lagrangian_factors(&rotated).is_none(),
        "Rotated tesseract should NOT be a Lagrangian product in standard coordinates"
    );
}

// ============================================================================
// Facet Index Mapping Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    /// 2D to 4D facet index mapping is consistent.
    #[test]
    fn facet_index_mapping_consistent(polytope in lagrangian_product_strategy()) {
        let factors = extract_lagrangian_factors(&polytope)
            .expect("Should be a Lagrangian product");

        let tol = 1e-10;

        // Check K1 mapping: local normal should match global normal's q-components
        for (local_idx, &global_idx) in factors.q_facet_indices.iter().enumerate() {
            let local_n = factors.k1.normals[local_idx];
            let local_h = factors.k1.heights[local_idx];

            let global_n = polytope.normals[global_idx];
            let global_h = polytope.heights[global_idx];

            prop_assert!(
                (local_n.x - global_n.x).abs() < tol && (local_n.y - global_n.y).abs() < tol,
                "K1 facet {} normal mismatch: local=({:.4},{:.4}), global=({:.4},{:.4},{:.4},{:.4})",
                local_idx, local_n.x, local_n.y, global_n.x, global_n.y, global_n.z, global_n.w
            );

            prop_assert!(
                (local_h - global_h).abs() < tol,
                "K1 facet {} height mismatch: local={:.6}, global={:.6}",
                local_idx, local_h, global_h
            );
        }

        // Check K2 mapping: local normal should match global normal's p-components
        for (local_idx, &global_idx) in factors.p_facet_indices.iter().enumerate() {
            let local_n = factors.k2.normals[local_idx];
            let local_h = factors.k2.heights[local_idx];

            let global_n = polytope.normals[global_idx];
            let global_h = polytope.heights[global_idx];

            prop_assert!(
                (local_n.x - global_n.z).abs() < tol && (local_n.y - global_n.w).abs() < tol,
                "K2 facet {} normal mismatch: local=({:.4},{:.4}), global=({:.4},{:.4},{:.4},{:.4})",
                local_idx, local_n.x, local_n.y, global_n.x, global_n.y, global_n.z, global_n.w
            );

            prop_assert!(
                (local_h - global_h).abs() < tol,
                "K2 facet {} height mismatch: local={:.6}, global={:.6}",
                local_idx, local_h, global_h
            );
        }
    }
}

// ============================================================================
// Polygon Vertex Constraint Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    /// 2D polygon vertices satisfy their H-representation constraints.
    #[test]
    fn polygon_vertices_satisfy_constraints(polytope in lagrangian_product_strategy()) {
        let factors = extract_lagrangian_factors(&polytope)
            .expect("Should be a Lagrangian product");

        let tol = 1e-10;

        // Check K1 (q-space polygon)
        for (v_idx, vertex) in factors.k1.vertices.iter().enumerate() {
            let n = factors.k1.normals.len();
            let edge_a = v_idx;
            let edge_b = (v_idx + 1) % n;

            let error_a = (factors.k1.normals[edge_a].dot(vertex) - factors.k1.heights[edge_a]).abs();
            let error_b = (factors.k1.normals[edge_b].dot(vertex) - factors.k1.heights[edge_b]).abs();

            prop_assert!(
                error_a < tol,
                "K1 vertex {} should satisfy edge {} constraint. error={:.2e}",
                v_idx, edge_a, error_a
            );
            prop_assert!(
                error_b < tol,
                "K1 vertex {} should satisfy edge {} constraint. error={:.2e}",
                v_idx, edge_b, error_b
            );

            for e in 0..n {
                if e != edge_a && e != edge_b {
                    let val = factors.k1.normals[e].dot(vertex);
                    prop_assert!(
                        val <= factors.k1.heights[e] + tol,
                        "K1 vertex {} should satisfy edge {} inequality. val={:.6}, h={:.6}",
                        v_idx, e, val, factors.k1.heights[e]
                    );
                }
            }
        }

        // Check K2 (p-space polygon)
        for (v_idx, vertex) in factors.k2.vertices.iter().enumerate() {
            let n = factors.k2.normals.len();
            let edge_a = v_idx;
            let edge_b = (v_idx + 1) % n;

            let error_a = (factors.k2.normals[edge_a].dot(vertex) - factors.k2.heights[edge_a]).abs();
            let error_b = (factors.k2.normals[edge_b].dot(vertex) - factors.k2.heights[edge_b]).abs();

            prop_assert!(
                error_a < tol,
                "K2 vertex {} should satisfy edge {} constraint. error={:.2e}",
                v_idx, edge_a, error_a
            );
            prop_assert!(
                error_b < tol,
                "K2 vertex {} should satisfy edge {} constraint. error={:.2e}",
                v_idx, edge_b, error_b
            );
        }
    }
}

// ============================================================================
// From H-rep Reconstruction Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(10))]

    /// from_hrep correctly reconstructs the original polygon.
    #[test]
    fn from_hrep_reconstructs_polygon(seed in any::<u64>(), n in 3usize..=6) {
        use super::fixtures::random_convex_polygon;
        use rand::SeedableRng;
        use rand_chacha::ChaCha8Rng;

        let mut rng = ChaCha8Rng::seed_from_u64(seed);
        let original = random_convex_polygon(&mut rng, n, 0.5, 2.0);

        let (normals, heights) = original.to_hrep_2d();
        let reconstructed = Polygon2DSimple::from_hrep(normals.clone(), heights.clone());

        prop_assert_eq!(
            reconstructed.vertices.len(),
            original.vertices.len(),
            "Vertex count should match"
        );

        let tol = 1e-6;
        let mut offset = None;
        for (i, orig_v) in original.vertices.iter().enumerate() {
            if (orig_v.x - reconstructed.vertices[0].x).abs() < tol
                && (orig_v.y - reconstructed.vertices[0].y).abs() < tol
            {
                offset = Some(i);
                break;
            }
        }

        let offset = offset.expect(&format!(
            "Should find matching vertex. reconstructed[0] = ({:.4}, {:.4}), original = {:?}",
            reconstructed.vertices[0].x, reconstructed.vertices[0].y, original.vertices
        ));

        for (i, recon_v) in reconstructed.vertices.iter().enumerate() {
            let orig_idx = (i + offset) % n;
            let orig_v = original.vertices[orig_idx];
            let error = ((recon_v.x - orig_v.x).powi(2) + (recon_v.y - orig_v.y).powi(2)).sqrt();
            prop_assert!(
                error < tol,
                "Vertex {} mismatch: reconstructed=({:.4},{:.4}), original[{}]=({:.4},{:.4}), error={:.2e}",
                i, recon_v.x, recon_v.y, orig_idx, orig_v.x, orig_v.y, error
            );
        }
    }
}
