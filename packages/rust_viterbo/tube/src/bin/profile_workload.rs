//! Profiling workload for flamegraph analysis.
//!
//! This binary provides representative workloads for profiling with cargo-flamegraph.
//!
//! Usage:
//!   cargo build --release -p tube --bin profile_workload
//!   cargo flamegraph --bin profile_workload -o flamegraph.svg
//!
//! Or run directly:
//!   cargo run --release -p tube --bin profile_workload -- [workload]
//!
//! Available workloads:
//!   - tube_cross: Tube algorithm on cross-polytope (default)
//!   - tube_24cell: Tube algorithm on 24-cell
//!   - tube_random: Tube algorithm on random polytopes
//!   - all: Run all workloads

use tube::fixtures::{random_hrep, unit_24_cell, unit_cross_polytope};
use tube::tube_capacity;

const ITERATIONS: usize = 100;

fn profile_tube_cross_polytope() {
    println!(
        "Profiling: Tube on cross-polytope ({} iterations)",
        ITERATIONS
    );
    let polytope = unit_cross_polytope();

    for i in 0..ITERATIONS {
        let result = tube_capacity(&polytope).expect("Tube capacity failed");
        if i == 0 {
            println!("  Capacity: {:.6}", result.capacity);
            println!("  Tubes explored: {}", result.tubes_explored);
        }
    }
    println!("  Done.");
}

fn profile_tube_24_cell() {
    println!("Profiling: Tube on 24-cell ({} iterations)", ITERATIONS);
    let polytope = unit_24_cell();

    for i in 0..ITERATIONS {
        let result = tube_capacity(&polytope).expect("Tube capacity failed");
        if i == 0 {
            println!("  Capacity: {:.6}", result.capacity);
            println!("  Tubes explored: {}", result.tubes_explored);
        }
    }
    println!("  Done.");
}

fn profile_tube_random() {
    println!("Profiling: Tube on random polytopes");
    let min_omega = 0.01;
    let mut successful = 0;

    for seed in 0..1000u64 {
        if let Some(polytope) = random_hrep(12, min_omega, seed) {
            match tube_capacity(&polytope) {
                Ok(result) => {
                    if successful == 0 {
                        println!("  First polytope capacity: {:.6}", result.capacity);
                    }
                    successful += 1;
                    if successful >= 50 {
                        break;
                    }
                }
                Err(_) => continue,
            }
        }
    }
    println!("  Processed {} random polytopes.", successful);
    println!("  Done.");
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let workload = args.get(1).map(|s| s.as_str()).unwrap_or("all");

    println!("=== Profile Workload ===\n");

    match workload {
        "tube_cross" => profile_tube_cross_polytope(),
        "tube_24cell" => profile_tube_24_cell(),
        "tube_random" => profile_tube_random(),
        _ => {
            profile_tube_cross_polytope();
            println!();
            profile_tube_24_cell();
            println!();
            profile_tube_random();
        }
    }

    println!("\n=== Profiling Complete ===");
}
