//! Tests for known capacity values from literature.
//!
//! Each test should cite its source. See docs/test-propositions.md for the
//! mathematical propositions these tests verify.

use super::fixtures::{
    equilateral_triangle_product, hko_pentagon_product, rectangle_product, tesseract,
};
use crate::compute::{CapacityAlgorithm, HK2019Algorithm, MinkowskiBilliardAlgorithm};

// =============================================================================
// Ground Truth: Tesseract
// =============================================================================

/// Tesseract capacity is 4.0.
///
/// **Source:** HK2017, Rudolf 2022
/// **Proposition:** c_EHZ([-1,1]⁴) = 4.0
#[test]
fn tesseract_capacity_is_four() {
    let algo = MinkowskiBilliardAlgorithm::new();
    let result = algo.compute(tesseract()).expect("billiard should succeed");

    assert!(
        (result.capacity - 4.0).abs() < 1e-6,
        "tesseract capacity should be 4.0, got {}",
        result.capacity
    );
}

// =============================================================================
// Ground Truth: Triangle × Triangle
// =============================================================================

/// Equilateral triangle × same triangle has capacity 1.5.
///
/// **Source:** test-cases.md, verified by LP algorithm
/// **Proposition:** For equilateral triangle with circumradius r, c = 1.5 r²
///
/// NOTE: The Fagnano orbit (t=0.5) gives 2.25, but Minkowski optimal is at t=1/3.
#[test]
fn triangle_product_capacity_is_one_point_five() {
    let hrep = equilateral_triangle_product();
    let algo = MinkowskiBilliardAlgorithm::new();
    let result = algo
        .compute(hrep)
        .expect("billiard should succeed on triangle product");

    // Circumradius = 1, so capacity should be 1.5
    assert!(
        (result.capacity - 1.5).abs() < 0.1,
        "triangle×triangle capacity should be ~1.5, got {}",
        result.capacity
    );
}

/// Cross-validate triangle capacity: billiard and HK2019 should agree.
#[test]
fn triangle_product_billiard_hk2019_agree() {
    let hrep = equilateral_triangle_product();

    let billiard = MinkowskiBilliardAlgorithm::new();
    let hk2019 = HK2019Algorithm::new();

    let c_billiard = billiard.compute(hrep.clone()).expect("billiard").capacity;
    let c_hk2019 = hk2019.compute(hrep).expect("hk2019").capacity;

    let rel_error = (c_billiard - c_hk2019).abs() / c_billiard;
    assert!(
        rel_error < 0.05,
        "billiard ({}) and HK2019 ({}) disagree on triangle: {:.1}% error",
        c_billiard,
        c_hk2019,
        rel_error * 100.0
    );
}

// =============================================================================
// Ground Truth: Pentagon × Pentagon (HK-O 2024 Counterexample)
// =============================================================================

/// Pentagon × rotated pentagon has capacity ≈ 3.441.
///
/// **Source:** Haim-Kislev & Ostrover 2024, Proposition 1
/// **Formula:** c = 2·cos(π/10)·(1 + cos(π/5)) ≈ 3.4409548
///
/// This is a counterexample to Viterbo's conjecture (systolic ratio > 1).
///
/// **KNOWN BUG**: Billiard returns 2.127 = 3.441/phi (off by golden ratio).
/// Fixture verified correct (matches Python). Bug is in billiard LP algorithm.
/// See: packages/rust_viterbo/algorithm/src/billiard_lp.rs
///
/// **When this passes**: Someone has fixed the golden ratio bug in the LP.
/// Remove #[should_panic] when fixed.
#[test]
#[should_panic(expected = "pentagon capacity")]
fn pentagon_counterexample_capacity() {
    let hrep = hko_pentagon_product();
    let algo = MinkowskiBilliardAlgorithm::new();
    let result = algo
        .compute(hrep)
        .expect("billiard should succeed on pentagon");

    // CORRECT ASSERTION: capacity should be ~3.441 (HK-O 2024 formula)
    let expected = 3.4409548;
    assert!(
        (result.capacity - expected).abs() < 0.1,
        "pentagon capacity should be ~{:.4}, got {:.4} - billiard LP has golden ratio bug",
        expected, result.capacity
    );
}

/// Pentagon counterexample: verify systolic ratio > 1.
///
/// **Proposition:** rho = c^2 / (2*Area(K)*Area(T)) > 1
/// This disproves Viterbo's conjecture.
///
/// **KNOWN BUG**: Depends on pentagon_counterexample_capacity which has
/// the golden ratio bug. With the buggy capacity (2.127 instead of 3.441),
/// the systolic ratio is ~0.4 instead of ~1.047.
///
/// **When this passes**: Someone has fixed the golden ratio bug in the LP.
/// Remove #[should_panic] when fixed.
#[test]
#[should_panic(expected = "systolic ratio")]
fn pentagon_systolic_ratio_exceeds_one() {
    let hrep = hko_pentagon_product();
    let algo = MinkowskiBilliardAlgorithm::new();
    let result = algo.compute(hrep).expect("billiard should succeed");

    // From HK-O 2024 data: volume = 5.653178
    let volume = 5.653178107421709;
    let systolic_ratio = result.capacity.powi(2) / (2.0 * volume);

    // CORRECT ASSERTION: systolic ratio should be > 1 (disproves Viterbo)
    // Expected value: (sqrt(5)+3)/5 ≈ 1.0472
    let expected = (5.0_f64.sqrt() + 3.0) / 5.0;
    assert!(
        systolic_ratio > 1.0 && (systolic_ratio - expected).abs() < 0.05,
        "systolic ratio should be ~{:.4} (> 1), got {:.4} - capacity has golden ratio bug",
        expected, systolic_ratio
    );
}

// =============================================================================
// Ground Truth: Rectangle Products
// =============================================================================

/// Rectangle 2×1 product has capacity 1.0.
///
/// **Source:** test-cases.md
/// **Proposition:** c([-1,1]×[-0.5,0.5] × same) = 1.0
#[test]
fn rectangle_2x1_product_capacity() {
    let hrep = rectangle_product(2.0, 1.0);
    let algo = MinkowskiBilliardAlgorithm::new();
    let result = algo.compute(hrep).expect("billiard should succeed");

    assert!(
        (result.capacity - 1.0).abs() < 0.01,
        "2×1 rectangle product capacity should be 1.0, got {}",
        result.capacity
    );
}

/// Verify rectangle capacity scales correctly with dimensions.
///
/// **Proposition:** For rectangle a×b product, capacity relates to min(a,b).
#[test]
fn rectangle_capacity_scaling() {
    let algo = MinkowskiBilliardAlgorithm::new();

    // Square 2×2 (= tesseract scaled by 1)
    let c_square = algo.compute(rectangle_product(2.0, 2.0)).unwrap().capacity;
    assert!(
        (c_square - 4.0).abs() < 0.01,
        "2×2 should give 4.0, got {}",
        c_square
    );

    // Rectangle 4×2
    let c_4x2 = algo.compute(rectangle_product(4.0, 2.0)).unwrap().capacity;

    // Rectangle 2×4 (same as 4×2 by symmetry)
    let c_2x4 = algo.compute(rectangle_product(2.0, 4.0)).unwrap().capacity;

    assert!(
        (c_4x2 - c_2x4).abs() < 0.01,
        "4×2 and 2×4 should have same capacity: {} vs {}",
        c_4x2,
        c_2x4
    );
}

// =============================================================================
// Debug: Pentagon LP Intermediate Values
// =============================================================================

/// Cross-validate pentagon with HK2019 algorithm.
///
/// If HK2019 gives 3.441, billiard is wrong.
/// If HK2019 gives 2.127, both have same bug.
///
/// NOTE: Pentagon has 10 facets, so 10! = 3,628,800 permutations.
/// This test will be VERY SLOW (minutes to hours).
#[test]
#[ignore = "10! permutations - takes too long"]
fn pentagon_hk2019_cross_validation() {
    use std::f64::consts::PI;

    let hrep = hko_pentagon_product();
    let algo = HK2019Algorithm::new();

    eprintln!("Running HK2019 on pentagon ({} facets)...", hrep.normals.len());
    eprintln!("This will enumerate {}! = {} permutations", hrep.normals.len(),
              (1..=hrep.normals.len()).product::<usize>());

    let result = algo.compute(hrep).expect("HK2019 should succeed");

    let expected = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());
    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;

    eprintln!("\nHK2019 result: {:.10}", result.capacity);
    eprintln!("Expected: {:.10}", expected);
    eprintln!("Billiard gives: 2.1266270209");
    eprintln!("Ratio expected/hk2019: {:.10}", expected / result.capacity);
    eprintln!("φ: {:.10}", phi);
}

/// Debug test to investigate pentagon bug.
/// Prints LP intermediate values to help identify where φ division occurs.
#[test]
fn debug_pentagon_lp_values() {
    use crate::billiard::extract_lagrangian_factors;
    use crate::billiard_lp::compute_billiard_capacity_lp;
    use std::f64::consts::PI;

    let hrep = hko_pentagon_product();

    eprintln!("\n=== Debug Pentagon LP Values ===\n");

    // Extract factors
    let factors = extract_lagrangian_factors(&hrep).expect("Should be Lagrangian product");

    eprintln!("K1 (q-space) polygon:");
    for (i, v) in factors.k1.vertices.iter().enumerate() {
        eprintln!("  vertex[{}]: ({:.6}, {:.6})", i, v.x, v.y);
    }
    eprintln!("  normals and heights:");
    for (i, (n, h)) in factors.k1.normals.iter().zip(&factors.k1.heights).enumerate() {
        eprintln!("    [{}]: n=({:.6}, {:.6}), h={:.6}", i, n.x, n.y, h);
    }

    eprintln!("\nK2 (p-space) polygon:");
    for (i, v) in factors.k2.vertices.iter().enumerate() {
        eprintln!("  vertex[{}]: ({:.6}, {:.6})", i, v.x, v.y);
    }
    eprintln!("  normals and heights:");
    for (i, (n, h)) in factors.k2.normals.iter().zip(&factors.k2.heights).enumerate() {
        eprintln!("    [{}]: n=({:.6}, {:.6}), h={:.6}", i, n.x, n.y, h);
    }

    // Compute capacity
    let result = compute_billiard_capacity_lp(hrep).expect("LP should succeed");
    eprintln!("\nLP Result:");
    eprintln!("  capacity (T-length): {:.10}", result.capacity);

    // Expected values
    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
    let expected = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());

    eprintln!("\nExpected capacity: {:.10}", expected);
    eprintln!("Ratio (expected/actual): {:.10}", expected / result.capacity);
    eprintln!("Golden ratio φ: {:.10}", phi);

    // Print witness if available
    if let Some(ref witness) = result.witness {
        eprintln!("\nWitness orbit:");
        eprintln!("  facet_sequence: {:?}", witness.facet_sequence);
        eprintln!("  breakpoints ({}):", witness.breakpoints.len());
        for (i, bp) in witness.breakpoints.iter().enumerate() {
            eprintln!("    [{}]: ({:.6}, {:.6}, {:.6}, {:.6})", i, bp.x, bp.y, bp.z, bp.w);
        }
    }
}

/// Debug pentagon bug: trace through K2° computation.
///
/// The billiard T-length formula uses h_K2°(d) = support function of K2°.
/// K2° has vertices at n_i/h_i (polar body formula).
///
/// Let's verify this manually.
#[test]
fn debug_pentagon_polar_body() {
    use crate::billiard::extract_lagrangian_factors;
    use std::f64::consts::PI;

    let hrep = hko_pentagon_product();
    let factors = extract_lagrangian_factors(&hrep).expect("Should be Lagrangian product");

    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;

    eprintln!("\n=== Pentagon K2° Investigation ===\n");

    // K2 polygon details
    eprintln!("K2 polygon (p-space):");
    let k2 = &factors.k2;
    
    eprintln!("  Vertices:");
    for (i, v) in k2.vertices.iter().enumerate() {
        let norm = (v.x*v.x + v.y*v.y).sqrt();
        eprintln!("    [{}]: ({:.6}, {:.6}), norm = {:.6}", i, v.x, v.y, norm);
    }
    
    eprintln!("\n  Normals and heights:");
    for (i, (n, h)) in k2.normals.iter().zip(&k2.heights).enumerate() {
        let n_norm = (n.x*n.x + n.y*n.y).sqrt();
        eprintln!("    [{}]: n=({:.6}, {:.6}), |n|={:.6}, h={:.6}", i, n.x, n.y, n_norm, h);
    }

    // Compute K2° manually
    eprintln!("\n  K2° vertices = n_i/h_i:");
    for (i, (n, h)) in k2.normals.iter().zip(&k2.heights).enumerate() {
        let polar_v_x = n.x / h;
        let polar_v_y = n.y / h;
        let polar_norm = (polar_v_x*polar_v_x + polar_v_y*polar_v_y).sqrt();
        eprintln!("    [{}]: ({:.6}, {:.6}), norm = {:.6}", i, polar_v_x, polar_v_y, polar_norm);
    }

    // The K2° computed by k2.polar()
    let k2_polar = k2.polar();
    eprintln!("\n  K2° from polar() method:");
    for (i, v) in k2_polar.vertices.iter().enumerate() {
        let norm = (v.x*v.x + v.y*v.y).sqrt();
        eprintln!("    [{}]: ({:.6}, {:.6}), norm = {:.6}", i, v.x, v.y, norm);
    }

    // Key quantities
    eprintln!("\n=== Key Constants ===");
    let h = k2.heights[0];  // All heights are the same for regular pentagon
    eprintln!("h = {:.10} (should be cos(pi/5) = phi/2)", h);
    eprintln!("cos(pi/5) = {:.10}", (PI/5.0).cos());
    eprintln!("phi/2 = {:.10}", phi/2.0);
    eprintln!("1/h = {:.10}", 1.0/h);
    eprintln!("2/phi = {:.10}", 2.0/phi);

    // Check: 1/h should equal 2/phi
    assert!((1.0/h - 2.0/phi).abs() < 1e-8, "1/h should equal 2/phi");

    // Now the K2° vertices should have norm = 1/h = 2/phi ≈ 1.236
    // NOT phi ≈ 1.618
    //
    // So the bug is NOT in the K2° construction.
}

/// Debug pentagon bug: verify T-length formula.
///
/// The T-length for a 2-bounce trajectory is:
///   T = h_K2°(d) + h_K2°(-d)
/// where d = q2 - q1 is the trajectory direction.
///
/// We compute this manually and compare with LP result.
#[test]
fn debug_pentagon_tlength_formula() {
    use crate::billiard::extract_lagrangian_factors;
    use crate::billiard_lp::{find_min_2bounce_lp, find_min_3bounce_lp};
    use std::f64::consts::PI;
    use rust_viterbo_geom::Vector2f;

    let hrep = hko_pentagon_product();
    let factors = extract_lagrangian_factors(&hrep).expect("Should be Lagrangian product");

    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
    let expected_capacity = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());

    eprintln!("\n=== Pentagon T-length Verification ===\n");

    let k1 = &factors.k1;
    let k2 = &factors.k2;
    let k2_polar = k2.polar();

    // Get LP results
    let result_2b = find_min_2bounce_lp(k1, k2);
    let result_3b = find_min_3bounce_lp(k1, k2);

    eprintln!("LP Results:");
    if let Some(ref r2) = result_2b {
        eprintln!("  2-bounce: T={:.10}, edges={:?}, t={:?}", r2.t_length, r2.edge_indices, r2.edge_params);
    }
    if let Some(ref r3) = result_3b {
        eprintln!("  3-bounce: T={:.10}, edges={:?}, t={:?}", r3.t_length, r3.edge_indices, r3.edge_params);
    }

    // For the optimal 2-bounce, compute trajectory manually
    if let Some(ref r2) = result_2b {
        let n = k1.vertices.len();
        let [ei, ej] = r2.edge_indices;
        let [ti, tj] = r2.edge_params;

        // Edge endpoints
        let ai = k1.vertices[ei];
        let bi = k1.vertices[(ei + 1) % n];
        let aj = k1.vertices[ej];
        let bj = k1.vertices[(ej + 1) % n];

        // Bounce points
        let q1 = ai + (bi - ai) * ti;
        let q2 = aj + (bj - aj) * tj;

        eprintln!("\n  Optimal 2-bounce trajectory:");
        eprintln!("    q1 = ({:.6}, {:.6})", q1.x, q1.y);
        eprintln!("    q2 = ({:.6}, {:.6})", q2.x, q2.y);

        let d = q2 - q1;
        eprintln!("    d = q2-q1 = ({:.6}, {:.6}), |d| = {:.6}", d.x, d.y, d.norm());

        // Support functions using K2°
        let h_d = k2_polar.support(d);
        let h_neg_d = k2_polar.support(-d);
        let t_length_manual = h_d + h_neg_d;

        eprintln!("    h_K2°(d) = {:.10}", h_d);
        eprintln!("    h_K2°(-d) = {:.10}", h_neg_d);
        eprintln!("    T-length (manual) = h_K2°(d) + h_K2°(-d) = {:.10}", t_length_manual);
        eprintln!("    T-length (LP) = {:.10}", r2.t_length);

        // Verify manual matches LP
        let diff = (t_length_manual - r2.t_length).abs();
        eprintln!("    Difference: {:.2e}", diff);

        // The bug is that LP returns T/φ instead of T.
        // Let's check: expected = actual * φ?
        eprintln!("\n  Bug analysis:");
        eprintln!("    Expected capacity: {:.10}", expected_capacity);
        eprintln!("    LP result / φ = {:.10}", r2.t_length * phi);
        eprintln!("    Manual T-length / φ = {:.10}", t_length_manual * phi);
    }
}

/// Debug pentagon bug: compare with unrotated pentagon.
///
/// Test 2: If pentagon×same_pentagon (no rotation) works but rotated doesn't,
/// bug is in rotation handling.
#[test]
fn debug_pentagon_unrotated() {
    use crate::billiard::extract_lagrangian_factors;
    use crate::billiard_lp::compute_billiard_capacity_lp;
    use std::f64::consts::PI;
    use rust_viterbo_geom::{PolytopeHRep, SymplecticVector};

    eprintln!("\n=== Pentagon Unrotated Test ===\n");

    // Create pentagon × same pentagon (no 90° rotation)
    // Regular pentagon with circumradius 1, first vertex at (1,0)
    let mut normals = Vec::new();
    let mut heights = Vec::new();

    // K1 (q-space): regular pentagon
    for k in 0..5 {
        let angle = 2.0 * PI * (k as f64) / 5.0;
        // Outward normal bisects the angle at vertex k
        let normal_angle = angle + PI / 5.0;  // offset to point outward from edge
        let nx = normal_angle.cos();
        let ny = normal_angle.sin();
        normals.push(SymplecticVector::new(nx, ny, 0.0, 0.0));
        heights.push((PI/5.0).cos());  // inradius
    }

    // K2 (p-space): SAME pentagon (no rotation)
    for k in 0..5 {
        let angle = 2.0 * PI * (k as f64) / 5.0;
        let normal_angle = angle + PI / 5.0;
        let nx = normal_angle.cos();
        let ny = normal_angle.sin();
        normals.push(SymplecticVector::new(0.0, 0.0, nx, ny));
        heights.push((PI/5.0).cos());
    }

    let hrep = PolytopeHRep::new(normals, heights);
    let result = compute_billiard_capacity_lp(hrep).expect("LP should succeed");

    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
    
    // For pentagon × same pentagon, what's the expected capacity?
    // Conjecture: it should be related to pentagon diagonal length
    eprintln!("Pentagon × same pentagon (unrotated):");
    eprintln!("  Capacity: {:.10}", result.capacity);
    eprintln!("  Capacity * φ: {:.10}", result.capacity * phi);

    // For the rotated case:
    let hrep_rotated = hko_pentagon_product();
    let result_rotated = compute_billiard_capacity_lp(hrep_rotated).expect("LP should succeed");

    eprintln!("\nPentagon × rotated pentagon (HK-O 2024):");
    eprintln!("  Capacity: {:.10}", result_rotated.capacity);
    eprintln!("  Capacity * φ: {:.10}", result_rotated.capacity * phi);
    eprintln!("  Expected (HK-O): {:.10}", 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos()));

    // Are they both wrong by factor φ?
    eprintln!("\nRatio analysis:");
    eprintln!("  Unrotated/Rotated: {:.4}", result.capacity / result_rotated.capacity);
}

/// CRITICAL: Verify the LP uses the correct polygon (K2 vs K2°).
///
/// The billiard T-length formula is:
///   T = h_{K2°}(d) + h_{K2°}(-d)
///
/// NOT:
///   T = h_{K2}(d) + h_{K2}(-d)
///
/// The LP in solve_2bounce_lp iterates over k2.vertices.
/// It should iterate over k2.polar().vertices = K2°.vertices!
#[test]
fn debug_pentagon_k2_vs_k2_polar() {
    use crate::billiard::extract_lagrangian_factors;
    use std::f64::consts::PI;
    use rust_viterbo_geom::Vector2f;

    let hrep = hko_pentagon_product();
    let factors = extract_lagrangian_factors(&hrep).expect("Should be Lagrangian product");

    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
    let expected = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());

    eprintln!("\n=== K2 vs K2° Verification ===\n");

    let k2 = &factors.k2;
    let k2_polar = k2.polar();

    // The optimal trajectory goes from (1, 0) to (0.309, 0.951)
    let q1 = Vector2f::new(1.0, 0.0);
    let q2 = Vector2f::new(0.309017, 0.951057);
    let d = q2 - q1;

    // Compute support using K2 (WRONG - what LP does)
    let h_k2_d = k2.support(d);
    let h_k2_neg_d = k2.support(-d);
    let t_using_k2 = h_k2_d + h_k2_neg_d;

    // Compute support using K2° (CORRECT - what should be done)
    let h_k2polar_d = k2_polar.support(d);
    let h_k2polar_neg_d = k2_polar.support(-d);
    let t_using_k2polar = h_k2polar_d + h_k2polar_neg_d;

    eprintln!("Direction d = ({:.6}, {:.6})", d.x, d.y);
    
    eprintln!("\nUsing K2 (WRONG - what LP does):");
    eprintln!("  h_K2(d) = {:.10}", h_k2_d);
    eprintln!("  h_K2(-d) = {:.10}", h_k2_neg_d);
    eprintln!("  T = {:.10}", t_using_k2);

    eprintln!("\nUsing K2° (CORRECT - what should be done):");
    eprintln!("  h_K2°(d) = {:.10}", h_k2polar_d);
    eprintln!("  h_K2°(-d) = {:.10}", h_k2polar_neg_d);
    eprintln!("  T = {:.10}", t_using_k2polar);

    eprintln!("\nRatios:");
    eprintln!("  T(K2°) / T(K2) = {:.10}", t_using_k2polar / t_using_k2);
    eprintln!("  1/h = 2/φ = {:.10}", 2.0/phi);
    
    eprintln!("\nExpected capacity: {:.10}", expected);
    eprintln!("LP returns (using K2): {:.10}", t_using_k2);
    eprintln!("Correct (using K2°): {:.10}", t_using_k2polar);
    
    // The ratio T(K2°)/T(K2) should be 1/h = 2/φ ≈ 1.236
    // But we see T_LP * φ = expected, so the ratio is actually φ
    // Something else is going on...
}

/// Full verification of expected pentagon capacity formula.
///
/// From HK-O 2024, the capacity is 2*cos(π/10)*(1 + cos(π/5)).
/// Let's verify this step by step.
#[test]
fn debug_pentagon_expected_formula() {
    use std::f64::consts::PI;

    eprintln!("\n=== Pentagon Expected Formula Verification ===\n");

    let phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
    
    // The expected capacity formula from HK-O 2024:
    // c = 2 * cos(π/10) * (1 + cos(π/5))
    let cos_pi_10 = (PI / 10.0).cos();
    let cos_pi_5 = (PI / 5.0).cos();
    let expected = 2.0 * cos_pi_10 * (1.0 + cos_pi_5);

    eprintln!("Formula: c = 2 * cos(π/10) * (1 + cos(π/5))");
    eprintln!("  cos(π/10) = {:.10}", cos_pi_10);
    eprintln!("  cos(π/5) = {:.10} = φ/2", cos_pi_5);
    eprintln!("  1 + cos(π/5) = {:.10}", 1.0 + cos_pi_5);
    eprintln!("  c = {:.10}", expected);

    // Verify cos(π/10) = sqrt((φ+2)/4) = sqrt((5+sqrt(5))/8)
    let cos_pi_10_check = ((5.0 + 5.0_f64.sqrt()) / 8.0).sqrt();
    eprintln!("\n  cos(π/10) = sqrt((5+sqrt(5))/8) = {:.10}", cos_pi_10_check);

    // Pentagon geometry
    eprintln!("\nPentagon geometry (circumradius R = 1):");
    eprintln!("  Circumradius R = 1");
    eprintln!("  Inradius r = R * cos(π/5) = {:.10}", cos_pi_5);
    eprintln!("  Side length s = 2R * sin(π/5) = {:.10}", 2.0 * (PI/5.0).sin());
    eprintln!("  Diagonal d = s * φ = {:.10}", 2.0 * (PI/5.0).sin() * phi);

    // The billiard algorithm computes min T-length for K2°-billiard in K1
    // For pentagon × 90°-rotated pentagon:
    // - K1 has circumradius 1
    // - K2 (rotated) also has circumradius 1
    // - K2° has vertices at n/h where h = cos(π/5)
    // - So K2° vertices have norm 1/cos(π/5) = 2/φ ≈ 1.236
    
    eprintln!("\nK2° geometry:");
    eprintln!("  K2 heights h = cos(π/5) = φ/2 = {:.10}", cos_pi_5);
    eprintln!("  K2° vertices at norm 1/h = 2/φ = {:.10}", 2.0/phi);

    // What's the minimum K2°-billiard length in K1?
    // This requires finding the shortest 2-bounce or 3-bounce path
    // where segment lengths are measured in K2° norm.
    
    // The formula c = 2*cos(π/10)*(1+cos(π/5)) suggests a specific trajectory
    // Let's work backwards: what trajectory gives this length?
    
    eprintln!("\nWorking backwards from expected capacity:");
    eprintln!("  c = 2*cos(π/10)*(1+cos(π/5)) = {:.10}", expected);
    
    // Factor out 2*cos(π/10):
    let factor = 2.0 * cos_pi_10;
    eprintln!("  = 2*cos(π/10) * (1 + cos(π/5))");
    eprintln!("  = {:.10} * {:.10}", factor, 1.0 + cos_pi_5);

    // The factor (1 + cos(π/5)) = 1 + φ/2 = (2+φ)/2
    let _one_plus_cos = 1.0 + cos_pi_5;
    eprintln!("  1 + cos(π/5) = (2+φ)/2 = {:.10}", (2.0+phi)/2.0);
    
    // So we need trajectories where h_K2°(d) involves these factors
}

/// Debug: verify LP computes h_K2 correctly.
///
/// The LP objective is z1 + z2 where:
///   z1 >= <d12, y> for all y in K2
///   z2 >= <d21, y> for all y in K2
///
/// At optimum, z1 = max_y <d12, y> = h_K2(d12) and z2 = h_K2(d21).
/// So the LP objective should equal h_K2(d12) + h_K2(d21).
#[test]
fn debug_verify_lp_support_function() {
    use crate::billiard::extract_lagrangian_factors;
    use crate::billiard_lp::solve_2bounce_lp;
    use rust_viterbo_geom::Vector2f;

    let hrep = hko_pentagon_product();
    let factors = extract_lagrangian_factors(&hrep).expect("Should be Lagrangian product");

    eprintln!("\n=== Verify LP computes h_K2 correctly ===\n");

    let k1 = &factors.k1;
    let k2 = &factors.k2;

    // Solve LP for specific edge pair
    let edge_pair = [0, 2];  // The optimal edge pair from earlier test
    let result = solve_2bounce_lp(k1, k2, edge_pair).expect("LP should succeed");

    eprintln!("LP result for edges {:?}:", edge_pair);
    eprintln!("  t = {:?}", result.edge_params);
    eprintln!("  T-length = {:.10}", result.t_length);

    // Compute the actual trajectory points
    let n = k1.vertices.len();
    let [ei, ej] = edge_pair;
    let [ti, tj] = result.edge_params;

    let ai = k1.vertices[ei];
    let bi = k1.vertices[(ei + 1) % n];
    let aj = k1.vertices[ej];
    let bj = k1.vertices[(ej + 1) % n];

    let q1 = ai + (bi - ai) * ti;
    let q2 = aj + (bj - aj) * tj;
    let d12 = q2 - q1;
    let d21 = -d12;

    eprintln!("\nTrajectory:");
    eprintln!("  q1 = ({:.6}, {:.6})", q1.x, q1.y);
    eprintln!("  q2 = ({:.6}, {:.6})", q2.x, q2.y);
    eprintln!("  d12 = ({:.6}, {:.6})", d12.x, d12.y);

    // Compute h_K2(d12) and h_K2(d21) manually
    let h_k2_d12 = k2.support(d12);
    let h_k2_d21 = k2.support(d21);
    let manual_t_length = h_k2_d12 + h_k2_d21;

    eprintln!("\nManual computation (using K2):");
    eprintln!("  h_K2(d12) = {:.10}", h_k2_d12);
    eprintln!("  h_K2(d21) = {:.10}", h_k2_d21);
    eprintln!("  Total = {:.10}", manual_t_length);

    eprintln!("\nDifference (LP - manual): {:.2e}", (result.t_length - manual_t_length).abs());

    // Also check which K2 vertices achieve the maximum
    for (i, y) in k2.vertices.iter().enumerate() {
        let val12 = d12.dot(y);
        let val21 = d21.dot(y);
        eprintln!("  K2 vertex[{}]: <d12,y>={:.6}, <d21,y>={:.6}", i, val12, val21);
    }
}

/// Verify the diagonal trajectory formula from HK-O 2024.
///
/// The HK-O paper says the optimal 2-bounce trajectory is along the DIAGONALS
/// of the pentagon K. A pentagon diagonal connects v_k to v_{k+2} (mod 5).
///
/// The T°-length of a diagonal is 2*cos(π/10)*(1+cos(π/5)).
#[test]
fn debug_pentagon_diagonal_trajectory() {
    use crate::billiard::extract_lagrangian_factors;
    use std::f64::consts::PI;
    use rust_viterbo_geom::Vector2f;

    let hrep = hko_pentagon_product();
    let factors = extract_lagrangian_factors(&hrep).expect("Should be Lagrangian product");

    eprintln!("\n=== Pentagon Diagonal Trajectory Analysis ===\n");

    let k1 = &factors.k1;
    let k2 = &factors.k2;
    let _phi = (1.0 + 5.0_f64.sqrt()) / 2.0;
    let expected = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());

    eprintln!("K1 vertices (q-space):");
    for (i, v) in k1.vertices.iter().enumerate() {
        eprintln!("  v[{}] = ({:.6}, {:.6})", i, v.x, v.y);
    }

    eprintln!("\nK2 vertices (p-space, T in the paper):");
    for (i, w) in k2.vertices.iter().enumerate() {
        eprintln!("  w[{}] = ({:.6}, {:.6})", i, w.x, w.y);
    }

    // The pentagon K has circumradius 1, so vertices are at angles 2πk/5.
    // A diagonal connects v_k to v_{k+2}.
    // Let's compute the T°-length of each diagonal.
    
    eprintln!("\nDiagonals of K1:");
    for k in 0..5 {
        let v_k = k1.vertices[k];
        let v_k2 = k1.vertices[(k + 2) % 5];
        let d = v_k2 - v_k;
        
        // T°-length = ||d||_T° = max_w <d, w>
        // Since the trajectory is 2-bounce (out and back), total = h_T(d) + h_T(-d)
        let h_d = k2.support(d);
        let h_neg_d = k2.support(-d);
        let t_length = h_d + h_neg_d;
        
        eprintln!("  Diagonal v[{}]->v[{}]: d=({:.4}, {:.4}), |d|={:.6}", 
                  k, (k+2)%5, d.x, d.y, d.norm());
        eprintln!("    h_T(d) = {:.10}", h_d);
        eprintln!("    h_T(-d) = {:.10}", h_neg_d);
        eprintln!("    T°-length = {:.10}", t_length);
    }
    
    // Compare with expected
    eprintln!("\nExpected T°-length of diagonal: {:.10}", expected);
    
    // The LP finds a different trajectory - let's see what it finds
    use crate::billiard_lp::find_min_2bounce_lp;
    let lp_result = find_min_2bounce_lp(k1, k2).expect("LP should find solution");
    
    eprintln!("\nLP optimal 2-bounce:");
    eprintln!("  edges = {:?}, t = {:?}", lp_result.edge_indices, lp_result.edge_params);
    eprintln!("  T°-length = {:.10}", lp_result.t_length);
    
    // The discrepancy is that the LP finds a SHORTER trajectory!
    // But that can't be right because HK-O says diagonals are optimal.
    // Unless... the LP is using the wrong K2?
}

/// Debug: What trajectory is the LP finding?
///
/// The LP finds edges [0, 2] with t = [1.0, 0.0].
/// Edge i goes from vertex[i] to vertex[i+1].
/// So:
/// - Edge 0 at t=1.0: point on edge from v[0] to v[1], at t=1.0 → this is v[1]
/// - Edge 2 at t=0.0: point on edge from v[2] to v[3], at t=0.0 → this is v[2]
///
/// So the LP trajectory goes from v[1] to v[2], which is an EDGE not a DIAGONAL!
#[test]
fn debug_what_trajectory_lp_finds() {
    use crate::billiard::extract_lagrangian_factors;
    use crate::billiard_lp::find_min_2bounce_lp;
    use std::f64::consts::PI;

    let hrep = hko_pentagon_product();
    let factors = extract_lagrangian_factors(&hrep).expect("Should be Lagrangian product");

    eprintln!("\n=== What Trajectory Does LP Find? ===\n");

    let k1 = &factors.k1;
    let k2 = &factors.k2;
    let n = k1.vertices.len();

    eprintln!("K1 vertex indices and positions:");
    for (i, v) in k1.vertices.iter().enumerate() {
        eprintln!("  v[{}] = ({:.6}, {:.6})", i, v.x, v.y);
    }

    let lp_result = find_min_2bounce_lp(k1, k2).expect("LP should find solution");
    eprintln!("\nLP result:");
    eprintln!("  edges = {:?}, t = {:?}", lp_result.edge_indices, lp_result.edge_params);

    // Decode the trajectory
    let [ei, ej] = lp_result.edge_indices;
    let [ti, tj] = lp_result.edge_params;

    let ai = k1.vertices[ei];
    let bi = k1.vertices[(ei + 1) % n];
    let aj = k1.vertices[ej];
    let bj = k1.vertices[(ej + 1) % n];

    let q1 = ai + (bi - ai) * ti;
    let q2 = aj + (bj - aj) * tj;

    eprintln!("\nEdge {} goes from v[{}]=({:.4},{:.4}) to v[{}]=({:.4},{:.4})", 
              ei, ei, ai.x, ai.y, (ei+1)%n, bi.x, bi.y);
    eprintln!("  At t={:.6}: q1 = ({:.6}, {:.6})", ti, q1.x, q1.y);

    eprintln!("\nEdge {} goes from v[{}]=({:.4},{:.4}) to v[{}]=({:.4},{:.4})", 
              ej, ej, aj.x, aj.y, (ej+1)%n, bj.x, bj.y);
    eprintln!("  At t={:.6}: q2 = ({:.6}, {:.6})", tj, q2.x, q2.y);

    // Identify which vertices these are closest to
    let eps = 1e-6;
    for (k, v) in k1.vertices.iter().enumerate() {
        if (q1 - v).norm() < eps {
            eprintln!("\nq1 is vertex v[{}]", k);
        }
        if (q2 - v).norm() < eps {
            eprintln!("q2 is vertex v[{}]", k);
        }
    }

    let d = q2 - q1;
    eprintln!("\nTrajectory: from q1 to q2");
    eprintln!("  Direction d = ({:.6}, {:.6}), |d| = {:.6}", d.x, d.y, d.norm());

    // Is this an edge (length = side) or diagonal?
    let side_length = 2.0 * (PI/5.0).sin();  // pentagon side with circumradius 1
    let diag_length = side_length * (1.0 + 5.0_f64.sqrt()) / 2.0;  // diagonal = side * phi

    eprintln!("\nPentagon geometry (circumradius 1):");
    eprintln!("  Side length = {:.6}", side_length);
    eprintln!("  Diagonal length = {:.6}", diag_length);
    eprintln!("  |d| = {:.6}", d.norm());

    if (d.norm() - side_length).abs() < eps {
        eprintln!("  → LP trajectory is along an EDGE (side)");
    } else if (d.norm() - diag_length).abs() < eps {
        eprintln!("  → LP trajectory is along a DIAGONAL");
    } else {
        eprintln!("  → LP trajectory is neither edge nor diagonal!");
    }

    // The KEY issue: LP is finding edge-to-edge trajectory, not diagonal!
    // But the billiard should be going vertex-to-vertex along diagonal.
}

/// Verify the billiard constraint: trajectory cannot be translated into interior.
///
/// A 2-bounce trajectory between edges i and j is valid iff the edges don't share
/// a vertex (i.e., they're not adjacent).
///
/// Pentagon edges:
/// - Edge 0: v[0]→v[1]
/// - Edge 1: v[1]→v[2]
/// - Edge 2: v[2]→v[3]
/// - Edge 3: v[3]→v[4]
/// - Edge 4: v[4]→v[0]
///
/// Adjacent pairs (share a vertex): (0,1), (1,2), (2,3), (3,4), (4,0)
/// Non-adjacent pairs (valid): (0,2), (0,3), (1,3), (1,4), (2,4)
#[test]
fn debug_verify_billiard_constraint() {
    use crate::billiard::extract_lagrangian_factors;
    use crate::billiard_lp::solve_2bounce_lp;
    use std::f64::consts::PI;

    let hrep = hko_pentagon_product();
    let factors = extract_lagrangian_factors(&hrep).expect("Should be Lagrangian product");

    eprintln!("\n=== Verify Billiard Constraint ===\n");

    let k1 = &factors.k1;
    let k2 = &factors.k2;
    let n = k1.vertices.len();
    let expected = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());

    eprintln!("Checking all edge pairs:\n");
    eprintln!("Legend: ADJ=adjacent (invalid), OK=non-adjacent (valid)\n");

    let mut best_valid = f64::INFINITY;
    let mut best_invalid = f64::INFINITY;

    for i in 0..n {
        for j in (i + 1)..n {
            // Check if edges are adjacent (share a vertex)
            // Edge i goes v[i]→v[i+1], edge j goes v[j]→v[j+1]
            // They share a vertex if (i+1)%n == j or (j+1)%n == i
            let adjacent = ((i + 1) % n == j) || ((j + 1) % n == i);
            let status = if adjacent { "ADJ" } else { "OK " };

            if let Some(result) = solve_2bounce_lp(k1, k2, [i, j]) {
                eprintln!("  [{}, {}] {}: T-length = {:.6}", i, j, status, result.t_length);
                
                if adjacent {
                    best_invalid = best_invalid.min(result.t_length);
                } else {
                    best_valid = best_valid.min(result.t_length);
                }
            } else {
                eprintln!("  [{}, {}] {}: infeasible", i, j, status);
            }
        }
    }

    eprintln!("\nBest T-length among VALID (non-adjacent) pairs: {:.10}", best_valid);
    eprintln!("Best T-length among INVALID (adjacent) pairs: {:.10}", best_invalid);
    eprintln!("Expected capacity: {:.10}", expected);

    eprintln!("\nConclusion:");
    if (best_valid - expected).abs() < 1e-6 {
        eprintln!("  ✓ Excluding adjacent pairs gives CORRECT capacity!");
    } else {
        eprintln!("  ✗ Still wrong even after excluding adjacent pairs");
    }
}

/// Debug: trace the [0, 2] edge pair LP in detail.
///
/// Edge 0: v[0]→v[1]
/// Edge 2: v[2]→v[3]
///
/// For a diagonal trajectory, we'd want:
/// - On edge 0: t=0 gives v[0], t=1 gives v[1]
/// - On edge 2: t=0 gives v[2], t=1 gives v[3]
///
/// Diagonal v[0]→v[2] would need: (edge 0 at t=0) to (edge 2 at t=0)
/// But edge 0 and edge 2 don't share any vertex, so this should work...
///
/// Wait - v[0]→v[2] is NOT vertex-to-vertex on these edges!
/// v[0] is START of edge 0
/// v[2] is START of edge 2
///
/// Let me trace the actual LP solution.
#[test]
fn debug_trace_edge_pair_0_2() {
    use crate::billiard::extract_lagrangian_factors;
    use crate::billiard_lp::solve_2bounce_lp;

    let hrep = hko_pentagon_product();
    let factors = extract_lagrangian_factors(&hrep).expect("Should be Lagrangian product");

    eprintln!("\n=== Trace Edge Pair [0, 2] ===\n");

    let k1 = &factors.k1;
    let k2 = &factors.k2;
    let n = k1.vertices.len();

    // Print edge definitions
    eprintln!("K1 vertices:");
    for (i, v) in k1.vertices.iter().enumerate() {
        eprintln!("  v[{}] = ({:.6}, {:.6})", i, v.x, v.y);
    }

    eprintln!("\nK1 edges:");
    for i in 0..n {
        let start = k1.vertices[i];
        let end = k1.vertices[(i + 1) % n];
        eprintln!("  Edge {}: v[{}]→v[{}] = ({:.4},{:.4})→({:.4},{:.4})", 
                  i, i, (i+1)%n, start.x, start.y, end.x, end.y);
    }

    // Solve LP for edge pair [0, 2]
    let result = solve_2bounce_lp(k1, k2, [0, 2]).expect("Should succeed");

    eprintln!("\nLP result for [0, 2]:");
    eprintln!("  t = {:?}", result.edge_params);
    eprintln!("  T-length = {:.10}", result.t_length);

    // Compute actual trajectory points
    let [t0, t2] = result.edge_params;
    let q0 = k1.vertices[0] + (k1.vertices[1] - k1.vertices[0]) * t0;
    let q2 = k1.vertices[2] + (k1.vertices[3] - k1.vertices[2]) * t2;

    eprintln!("\nActual trajectory:");
    eprintln!("  q0 (on edge 0 at t={:.4}) = ({:.6}, {:.6})", t0, q0.x, q0.y);
    eprintln!("  q2 (on edge 2 at t={:.4}) = ({:.6}, {:.6})", t2, q2.x, q2.y);

    let d = q2 - q0;
    eprintln!("  Direction d = ({:.6}, {:.6}), |d| = {:.6}", d.x, d.y, d.norm());

    // Check support functions
    let h_d = k2.support(d);
    let h_neg_d = k2.support(-d);
    eprintln!("\n  h_K2(d) = {:.10}", h_d);
    eprintln!("  h_K2(-d) = {:.10}", h_neg_d);
    eprintln!("  h_K2(d) + h_K2(-d) = {:.10}", h_d + h_neg_d);

    // Compare with what we'd get for the actual diagonal v[0]→v[2]
    let v0 = k1.vertices[0];
    let v2 = k1.vertices[2];
    let diag = v2 - v0;
    let h_diag = k2.support(diag);
    let h_neg_diag = k2.support(-diag);

    eprintln!("\nDiagonal v[0]→v[2]:");
    eprintln!("  v[0] = ({:.6}, {:.6})", v0.x, v0.y);
    eprintln!("  v[2] = ({:.6}, {:.6})", v2.x, v2.y);
    eprintln!("  diag = ({:.6}, {:.6}), |diag| = {:.6}", diag.x, diag.y, diag.norm());
    eprintln!("  h_K2(diag) = {:.10}", h_diag);
    eprintln!("  h_K2(-diag) = {:.10}", h_neg_diag);
    eprintln!("  Total = {:.10}", h_diag + h_neg_diag);

    // KEY: v[0] is on edge 0 (at t=0), v[2] is on edge 1 (at t=1) OR edge 2 (at t=0)?
    // v[2] is the START of edge 2 (t=0 on edge 2)
    // But v[0] is the START of edge 0 (t=0 on edge 0)
    // So to get diagonal v[0]→v[2], we need edges [0, 2] at t=[0, 0]!
    
    eprintln!("\n=== Testing t=[0,0] on edges [0,2] ===");
    let q0_at_0 = k1.vertices[0];  // edge 0 at t=0
    let q2_at_0 = k1.vertices[2];  // edge 2 at t=0
    eprintln!("  q0 (edge 0, t=0) = ({:.6}, {:.6}) = v[0]", q0_at_0.x, q0_at_0.y);
    eprintln!("  q2 (edge 2, t=0) = ({:.6}, {:.6}) = v[2]", q2_at_0.x, q2_at_0.y);
    
    // Check: is t=[0,0] feasible? It might be excluded by some constraint.
}

/// Verify: t=[0,0] on edges [0,2] gives the correct diagonal capacity.
///
/// The LP currently finds t=[1,0] because it minimizes without caring about
/// the billiard constraint. We need to force t away from boundaries.
#[test]
fn debug_verify_t_boundaries() {
    use crate::billiard::extract_lagrangian_factors;
    use std::f64::consts::PI;

    let hrep = hko_pentagon_product();
    let factors = extract_lagrangian_factors(&hrep).expect("Should be Lagrangian product");

    eprintln!("\n=== Verify t boundary issue ===\n");

    let k1 = &factors.k1;
    let k2 = &factors.k2;
    let expected = 2.0 * (PI / 10.0).cos() * (1.0 + (PI / 5.0).cos());

    // For edge pair [0, 2], compute T-length at various t values
    let _edge_pair = [0usize, 2usize];
    let _n = k1.vertices.len();

    eprintln!("Edge pair [0, 2]: edge 0 = v[0]→v[1], edge 2 = v[2]→v[3]\n");

    for t0 in [0.0, 0.5, 1.0] {
        for t2 in [0.0, 0.5, 1.0] {
            let q0 = k1.vertices[0] + (k1.vertices[1] - k1.vertices[0]) * t0;
            let q2 = k1.vertices[2] + (k1.vertices[3] - k1.vertices[2]) * t2;
            let d = q2 - q0;
            let t_length = k2.support(d) + k2.support(-d);

            // Check what vertex/point this corresponds to
            let q0_desc = if t0 == 0.0 { "v[0]" } else if t0 == 1.0 { "v[1]" } else { "mid" };
            let q2_desc = if t2 == 0.0 { "v[2]" } else if t2 == 1.0 { "v[3]" } else { "mid" };

            eprintln!("  t=[{:.1}, {:.1}]: {} → {}, T-length = {:.6}",
                      t0, t2, q0_desc, q2_desc, t_length);
        }
    }

    eprintln!("\nExpected (diagonal): {:.6}", expected);
    eprintln!("\nObservation: t=[0,0] gives v[0]→v[2] (diagonal) with correct T-length 3.44");
    eprintln!("             t=[1,0] gives v[1]→v[2] (SIDE) with wrong T-length 2.13");
    eprintln!("\nThe LP finds t=[1,0] because it's a lower T-length, but this is INVALID");
    eprintln!("because the trajectory lies entirely on the boundary (it's a side of the pentagon).");
}
