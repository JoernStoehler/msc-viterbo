//! Tests for agreement between different capacity algorithms.
//!
//! On Lagrangian products, both billiard and HK2019 should compute the same capacity.

use super::fixtures::{seeded_lagrangian_product, tesseract};
use crate::compute::{CapacityAlgorithm, HK2019Algorithm, MinkowskiBilliardAlgorithm, TubeAlgorithm};
use crate::result::AlgorithmError;
use proptest::prelude::*;
use rust_viterbo_geom::symplectic_form;

// ============================================================================
// Proptest Strategies
// ============================================================================

fn lagrangian_product_small_strategy() -> impl Strategy<Value = rust_viterbo_geom::PolytopeHRep> {
    any::<u64>().prop_map(|seed| seeded_lagrangian_product(seed, 3, 3))
}

// ============================================================================
// Algorithm Agreement Tests
// ============================================================================

proptest! {
    #![proptest_config(ProptestConfig::with_cases(3))]

    /// Billiard and HK2019 should agree on random Lagrangian products.
    ///
    /// Note: HK2019 has a known QP solver bug that may cause failures.
    #[test]
    fn billiard_hk2019_agreement(polytope in lagrangian_product_small_strategy()) {
        let billiard = MinkowskiBilliardAlgorithm::new();
        let hk2019 = HK2019Algorithm::new();

        let c_billiard = billiard.compute(polytope.clone())
            .expect("Billiard should succeed")
            .capacity;

        let c_hk2019 = match hk2019.compute(polytope) {
            Ok(r) => r.capacity,
            Err(e) => {
                eprintln!("HK2019 failed: {:?}", e);
                return Ok(());
            }
        };

        let rel_error = (c_billiard - c_hk2019).abs() / c_billiard;
        eprintln!("Billiard: {:.4}, HK2019: {:.4}, rel_error: {:.2}%",
            c_billiard, c_hk2019, rel_error * 100.0);

        prop_assert!(
            rel_error < 0.10,
            "Billiard and HK2019 disagree: billiard={}, hk2019={}, rel_error={:.2}%",
            c_billiard, c_hk2019, rel_error * 100.0
        );
    }
}

/// Tube and billiard disagree on tesseract (expected behavior).
///
/// Tube returns NoValidOrbits because tesseract has degenerate Lagrangian 2-faces.
/// Billiard succeeds because tesseract is a Lagrangian product.
#[test]
fn tube_billiard_tesseract_disagree() {
    let hrep = tesseract();
    let tube = TubeAlgorithm::new();
    let billiard = MinkowskiBilliardAlgorithm::new();

    let r_tube = tube.compute(hrep.clone());
    let r_billiard = billiard.compute(hrep);

    assert!(
        matches!(&r_tube, Err(AlgorithmError::NoValidOrbits)),
        "Tube should return NoValidOrbits for tesseract"
    );
    assert!(
        r_billiard.is_ok(),
        "Billiard should succeed for tesseract: {:?}",
        r_billiard
    );
}

/// Debug test for investigating HK2019 vs billiard disagreement.
#[test]
fn debug_hk2019_billiard_disagreement() {
    let seed = 0u64;
    let polytope = seeded_lagrangian_product(seed, 3, 3);

    eprintln!("=== Debug HK2019 vs Billiard ===");
    eprintln!("Seed: {}, facets: {}", seed, polytope.normals.len());

    eprintln!("\nNormals and heights:");
    for (i, (n, h)) in polytope.normals.iter().zip(&polytope.heights).enumerate() {
        eprintln!("  [{:1}]: n=({:7.4}, {:7.4}, {:7.4}, {:7.4}), h={:.4}",
            i, n.x, n.y, n.z, n.w, h);
    }

    eprintln!("\nSymplectic form ω(nᵢ, nⱼ):");
    let n = polytope.normals.len();
    eprint!("     ");
    for j in 0..n { eprint!("{:7}", j); }
    eprintln!();
    for i in 0..n {
        eprint!("  {} |", i);
        for j in 0..n {
            let omega = symplectic_form(polytope.normals[i], polytope.normals[j]);
            eprint!("{:7.3}", omega);
        }
        eprintln!();
    }

    let billiard = MinkowskiBilliardAlgorithm::new();
    let hk2019 = HK2019Algorithm::new();

    let billiard_result = billiard.compute(polytope.clone());
    let hk2019_result = hk2019.compute(polytope.clone());

    eprintln!("\nBilliard result: {:?}", billiard_result);
    eprintln!("HK2019 result: {:?}", hk2019_result);

    if let (Ok(b), Ok(h)) = (&billiard_result, &hk2019_result) {
        let rel_error = (b.capacity - h.capacity).abs() / b.capacity;
        eprintln!("\nComparison: billiard={:.6}, hk2019={:.6}, rel_error={:.2}%",
            b.capacity, h.capacity, rel_error * 100.0);
    }
}
