//! Diagnostic: categorize tube/HK2017 failures for random polytopes.
//!
//! Run with: cargo test --package tube --test failure_diagnostic -- --ignored --nocapture

use hk2017::{
    hk2017_capacity, Hk2017Config, Hk2017Error, PolytopeHRep as Hk2017Hrep, RejectionHistogram,
};
use tube::{fixtures, tube_capacity, PolytopeHRep as TubeHrep, TubeError};

fn tube_to_hk2017(hrep: &TubeHrep) -> Hk2017Hrep {
    Hk2017Hrep::new(hrep.normals.clone(), hrep.heights.clone())
}

#[test]
#[ignore] // Diagnostic test: run manually, not in CI
fn diagnose_failures() {
    let min_omega = 0.05;

    let mut gen_failed = 0;
    let mut tube_ok = 0;
    let mut tube_lagrangian = 0;
    let mut tube_numerical = 0;
    let mut tube_singular = 0;
    let mut tube_no_orbits = 0;
    let mut tube_invalid = 0;
    let mut hk_ok = 0;
    let mut hk_no_interior = 0;
    let mut hk_invalid = 0;
    let mut hk_other = 0;
    let mut hk_rejection_totals = RejectionHistogram::default();

    // Sample numerical instability messages
    let mut numerical_samples: Vec<String> = Vec::new();

    for seed in 0..2 {
        let polytope = match fixtures::random_hrep(8, min_omega, seed) {
            Some(p) => p,
            None => {
                gen_failed += 1;
                continue;
            }
        };

        // Tube
        match tube_capacity(&polytope) {
            Ok(_) => tube_ok += 1,
            Err(TubeError::HasLagrangianTwoFaces) => tube_lagrangian += 1,
            Err(TubeError::NumericalInstability(msg)) => {
                tube_numerical += 1;
                if numerical_samples.len() < 5 {
                    numerical_samples.push(format!("seed {}: {}", seed, msg));
                }
            }
            Err(TubeError::NearSingularFlowMap { det }) => {
                tube_singular += 1;
                if numerical_samples.len() < 5 {
                    numerical_samples.push(format!("seed {}: NearSingular det={:.2e}", seed, det));
                }
            }
            Err(TubeError::NoClosedOrbits) => tube_no_orbits += 1,
            Err(TubeError::InvalidPolytope(msg)) => {
                tube_invalid += 1;
                if numerical_samples.len() < 5 {
                    numerical_samples.push(format!("seed {}: Invalid: {}", seed, msg));
                }
            }
        }

        // HK2017
        let hk_polytope = tube_to_hk2017(&polytope);
        match hk2017_capacity(&hk_polytope, &Hk2017Config::naive()) {
            Ok(_) => hk_ok += 1,
            Err(Hk2017Error::NoFeasibleInteriorPoint {
                rejection_reasons, ..
            }) => {
                hk_no_interior += 1;
                // Accumulate rejection reasons
                hk_rejection_totals.negative_beta += rejection_reasons.negative_beta;
                hk_rejection_totals.singular_kkt += rejection_reasons.singular_kkt;
                hk_rejection_totals.non_positive_q += rejection_reasons.non_positive_q;
                hk_rejection_totals.constraint_violation += rejection_reasons.constraint_violation;
                hk_rejection_totals.other += rejection_reasons.other;
            }
            Err(Hk2017Error::InvalidPolytope(_)) => hk_invalid += 1,
            Err(e) => {
                hk_other += 1;
                // Other errors (NoPositiveQ, SingularKkt, NumericalInstability, etc.)
                if numerical_samples.len() < 10 {
                    numerical_samples.push(format!("seed {} HK2017: {}", seed, e));
                }
            }
        }
    }

    let total_gen = 2 - gen_failed;

    println!("\n=== Failure Diagnostic (min_omega={}) ===", min_omega);
    println!("Seeds tried: 2");
    println!("Generation failed: {}", gen_failed);
    println!("Polytopes generated: {}", total_gen);
    println!();
    println!("TUBE RESULTS:");
    println!(
        "  OK:                 {} ({:.1}%)",
        tube_ok,
        100.0 * tube_ok as f64 / total_gen as f64
    );
    println!("  HasLagrangianTwoFaces: {}", tube_lagrangian);
    println!("  NumericalInstability:  {}", tube_numerical);
    println!("  NearSingularFlowMap:   {}", tube_singular);
    println!("  NoClosedOrbits:        {}", tube_no_orbits);
    println!("  InvalidPolytope:       {}", tube_invalid);
    println!();
    println!("HK2017 RESULTS:");
    println!(
        "  OK:                 {} ({:.1}%)",
        hk_ok,
        100.0 * hk_ok as f64 / total_gen as f64
    );
    println!("  NoFeasibleInterior: {}", hk_no_interior);
    println!("  InvalidPolytope:    {}", hk_invalid);
    println!("  Other:              {}", hk_other);
    println!();
    println!("HK2017 REJECTION REASONS (summed across all NoFeasibleInterior failures):");
    println!(
        "  negative_beta:        {}",
        hk_rejection_totals.negative_beta
    );
    println!(
        "  singular_kkt:         {}",
        hk_rejection_totals.singular_kkt
    );
    println!(
        "  non_positive_q:       {}",
        hk_rejection_totals.non_positive_q
    );
    println!(
        "  constraint_violation: {}",
        hk_rejection_totals.constraint_violation
    );
    println!("  other:                {}", hk_rejection_totals.other);
    println!();
    println!("Sample error messages:");
    for msg in &numerical_samples {
        println!("  {}", msg);
    }
    println!();
}
