//! Detailed diagnostic for random polytope failures.
//!
//! Run with: cargo test --package tube --test detailed_diagnostic -- --ignored --nocapture

use hk2017::{hk2017_capacity, Hk2017Config, Hk2017Error, PolytopeHRep as Hk2017Hrep};
use tube::{fixtures, tube_capacity, PolytopeHRep as TubeHrep, TubeError};

fn tube_to_hk2017(hrep: &TubeHrep) -> Hk2017Hrep {
    Hk2017Hrep::new(hrep.normals.clone(), hrep.heights.clone())
}

/// Detailed diagnostic for one polytope.
#[test]
#[ignore]
fn diagnose_single_polytope() {
    // Find a valid random 8-facet polytope
    let min_omega = 0.001; // Same as comparison test
    let mut polytope = None;
    let mut found_seed = 0;

    for seed in 0..5000 {
        if let Some(p) = fixtures::random_hrep(8, min_omega, seed) {
            polytope = Some(p);
            found_seed = seed;
            break;
        }
    }

    let polytope = polytope.expect("Should find at least one valid polytope");
    println!(
        "\n=== Single Polytope Diagnostic (seed={}) ===\n",
        found_seed
    );

    // Print polytope data
    println!("Polytope H-rep:");
    for (i, (n, h)) in polytope.normals.iter().zip(&polytope.heights).enumerate() {
        println!(
            "  Facet {}: n=({:.4}, {:.4}, {:.4}, {:.4}), h={:.4}",
            i, n[0], n[1], n[2], n[3], h
        );
    }

    // Compute symplectic forms
    println!("\nSymplectic form matrix (omega(n_i, n_j)):");
    for i in 0..8 {
        print!("  ");
        for j in 0..8 {
            let ni = &polytope.normals[i];
            let nj = &polytope.normals[j];
            // Standard symplectic form: omega(a, b) = a1*b3 - a3*b1 + a2*b4 - a4*b2
            let omega = ni[0] * nj[2] - ni[2] * nj[0] + ni[1] * nj[3] - ni[3] * nj[1];
            print!("{:7.3} ", omega);
        }
        println!();
    }

    // Try Tube
    println!("\n--- Tube Algorithm ---");
    match tube_capacity(&polytope) {
        Ok(result) => {
            println!("SUCCESS: capacity = {:.6}", result.capacity);
            println!("  Tubes explored: {}", result.tubes_explored);
        }
        Err(TubeError::NoClosedOrbits) => {
            println!("FAILED: NoClosedOrbits");
            // Could add more debugging here about tube exploration
        }
        Err(e) => {
            println!("FAILED: {:?}", e);
        }
    }

    // Try HK2017
    println!("\n--- HK2017 Algorithm ---");
    let hk_polytope = tube_to_hk2017(&polytope);
    match hk2017_capacity(&hk_polytope, &Hk2017Config::naive()) {
        Ok(result) => {
            println!("SUCCESS: capacity = {:.6}", result.capacity);
            println!(
                "  Permutations evaluated: {}",
                result.permutations_evaluated
            );
        }
        Err(Hk2017Error::NoFeasibleInteriorPoint {
            checked,
            rejected,
            rejection_reasons,
        }) => {
            println!("FAILED: NoFeasibleInteriorPoint");
            println!("  Checked: {}", checked);
            println!("  Rejected: {}", rejected);
            println!("  Reasons: negative_beta={}, singular_kkt={}, constraint_violation={}, non_positive_q={}",
                rejection_reasons.negative_beta,
                rejection_reasons.singular_kkt,
                rejection_reasons.constraint_violation,
                rejection_reasons.non_positive_q);
        }
        Err(e) => {
            println!("FAILED: {:?}", e);
        }
    }
}

/// Compare random polytope vs cross-polytope on algorithm internals.
#[test]
#[ignore]
fn compare_random_vs_fixture() {
    use hk2017::FacetData;

    println!("\n=== Random vs Cross-Polytope Comparison ===\n");

    // Cross-polytope (known to work)
    let cross = fixtures::unit_cross_polytope();
    println!("Cross-polytope ({} facets):", cross.num_facets());

    let cross_fd = FacetData::from_polytope(&tube_to_hk2017(&cross)).unwrap();

    // Check omega matrix properties
    let mut cross_omega_max = 0.0f64;
    let mut cross_omega_min = f64::MAX;
    for i in 0..cross.num_facets() {
        for j in (i + 1)..cross.num_facets() {
            let omega = cross_fd.omega_matrix[(i, j)].abs();
            if omega > 1e-10 {
                cross_omega_max = cross_omega_max.max(omega);
                cross_omega_min = cross_omega_min.min(omega);
            }
        }
    }
    println!(
        "  |omega| range (non-zero): [{:.4}, {:.4}]",
        cross_omega_min, cross_omega_max
    );

    // Height statistics
    let cross_h_min = cross.heights.iter().cloned().fold(f64::MAX, f64::min);
    let cross_h_max = cross.heights.iter().cloned().fold(0.0, f64::max);
    println!("  Height range: [{:.4}, {:.4}]", cross_h_min, cross_h_max);

    // Find a valid random polytope
    let min_omega = 0.001;
    let mut random_poly = None;
    for seed in 0..5000 {
        if let Some(p) = fixtures::random_hrep(8, min_omega, seed) {
            random_poly = Some((seed, p));
            break;
        }
    }

    let (seed, random) = random_poly.expect("Should find random polytope");
    println!(
        "\nRandom polytope (seed={}, {} facets):",
        seed,
        random.num_facets()
    );

    let random_fd = FacetData::from_polytope(&tube_to_hk2017(&random)).unwrap();

    // Check omega matrix properties
    let mut random_omega_max = 0.0f64;
    let mut random_omega_min = f64::MAX;
    for i in 0..random.num_facets() {
        for j in (i + 1)..random.num_facets() {
            let omega = random_fd.omega_matrix[(i, j)].abs();
            if omega > 1e-10 {
                random_omega_max = random_omega_max.max(omega);
                random_omega_min = random_omega_min.min(omega);
            }
        }
    }
    println!(
        "  |omega| range (non-zero): [{:.4}, {:.4}]",
        random_omega_min, random_omega_max
    );

    // Height statistics
    let random_h_min = random.heights.iter().cloned().fold(f64::MAX, f64::min);
    let random_h_max = random.heights.iter().cloned().fold(0.0, f64::max);
    println!("  Height range: [{:.4}, {:.4}]", random_h_min, random_h_max);

    // Now test both algorithms
    println!("\nAlgorithm results:");

    match tube_capacity(&cross) {
        Ok(r) => println!("  Cross-polytope Tube: capacity={:.4}", r.capacity),
        Err(e) => println!("  Cross-polytope Tube: FAILED {:?}", e),
    }

    // NOTE: HK2017 on cross-polytope is skipped because it has 16 facets,
    // meaning 16! = 20 trillion permutations - completely intractable.
    println!("  Cross-polytope HK2017: SKIPPED (16 facets = 16! permutations)");

    match tube_capacity(&random) {
        Ok(r) => println!("  Random Tube: capacity={:.4}", r.capacity),
        Err(e) => println!("  Random Tube: FAILED {:?}", e),
    }

    match hk2017_capacity(&tube_to_hk2017(&random), &Hk2017Config::naive()) {
        Ok(r) => println!("  Random HK2017: capacity={:.4}", r.capacity),
        Err(e) => println!("  Random HK2017: FAILED {:?}", e),
    }
}

/// Test HK2017 with relaxed tolerances.
#[test]
#[ignore]
fn test_hk2017_relaxed_tolerances() {
    println!("\n=== HK2017 Tolerance Sensitivity ===\n");

    // Find a random polytope that fails with default tolerances
    let min_omega = 0.001;
    let mut failing_poly = None;

    for seed in 0..5000 {
        if let Some(p) = fixtures::random_hrep(8, min_omega, seed) {
            let hk = tube_to_hk2017(&p);
            if hk2017_capacity(&hk, &Hk2017Config::naive()).is_err() {
                failing_poly = Some((seed, p));
                break;
            }
        }
    }

    let (seed, polytope) = match failing_poly {
        Some(p) => p,
        None => {
            println!("No failing polytopes found - unexpected!");
            return;
        }
    };

    println!("Testing seed {} with various tolerances:\n", seed);

    let hk_polytope = tube_to_hk2017(&polytope);

    // Try different positive_tol values
    for positive_tol in [1e-10, 1e-8, 1e-6, 1e-4, 1e-2] {
        let config = Hk2017Config {
            strategy: hk2017::EnumerationStrategy::Naive,
            constraint_tol: 1e-10,
            positive_tol,
        };

        match hk2017_capacity(&hk_polytope, &config) {
            Ok(r) => println!(
                "  positive_tol={:.0e}: SUCCESS capacity={:.4}",
                positive_tol, r.capacity
            ),
            Err(Hk2017Error::NoFeasibleInteriorPoint {
                rejection_reasons, ..
            }) => {
                println!(
                    "  positive_tol={:.0e}: FAILED (negative_beta={})",
                    positive_tol, rejection_reasons.negative_beta
                );
            }
            Err(e) => println!("  positive_tol={:.0e}: FAILED {:?}", positive_tol, e),
        }
    }
}

/// Diagnostic: inspect the actual KKT solutions for a failing polytope.
#[test]
#[ignore]
fn diagnose_kkt_solutions() {
    use hk2017::{solve::solve_for_permutation, solve::SolveResult, FacetData};

    println!("\n=== KKT Solution Diagnostic ===\n");

    // Find a random polytope that fails
    let min_omega = 0.001;
    let mut failing_poly = None;

    for seed in 0..5000 {
        if let Some(p) = fixtures::random_hrep(8, min_omega, seed) {
            let hk = tube_to_hk2017(&p);
            if hk2017_capacity(&hk, &Hk2017Config::naive()).is_err() {
                failing_poly = Some((seed, p));
                break;
            }
        }
    }

    let (seed, polytope) = match failing_poly {
        Some(p) => p,
        None => {
            println!("No failing polytopes found");
            return;
        }
    };

    println!("Analyzing seed {} KKT solutions\n", seed);

    let hk_polytope = tube_to_hk2017(&polytope);
    let facet_data = FacetData::from_polytope(&hk_polytope).unwrap();
    let config = Hk2017Config::naive();

    // Try a few simple permutations and inspect the beta values
    let permutations: Vec<Vec<usize>> = vec![
        vec![0, 1],
        vec![0, 1, 2],
        vec![0, 1, 2, 3],
        vec![0, 1, 2, 3, 4],
        vec![0, 1, 2, 3, 4, 5],
        vec![0, 1, 2, 3, 4, 5, 6],
        vec![0, 1, 2, 3, 4, 5, 6, 7],
    ];

    for sigma in permutations {
        match solve_for_permutation(&sigma, &facet_data, &config) {
            SolveResult::Feasible {
                q_value,
                beta_local,
            } => {
                println!("Permutation {:?}: FEASIBLE", sigma);
                println!("  Q = {:.6}", q_value);
                println!("  beta = {:?}", beta_local);
            }
            SolveResult::Infeasible(reason) => {
                // Compute the actual solution to see the beta values
                println!("Permutation {:?}: {:?}", sigma, reason);
            }
        }
    }
}

/// Test if larger min_omega improves algorithm success rate.
#[test]
#[ignore]
fn test_min_omega_effect() {
    println!("\n=== Min Omega Effect on Algorithm Success ===\n");

    for min_omega in [0.001, 0.01, 0.05, 0.1, 0.2, 0.3] {
        let mut tube_ok = 0;
        let mut hk_ok = 0;
        let mut generated = 0;

        for seed in 0..500 {
            if let Some(p) = fixtures::random_hrep(8, min_omega, seed) {
                generated += 1;

                if tube_capacity(&p).is_ok() {
                    tube_ok += 1;
                }

                let hk = tube_to_hk2017(&p);
                if hk2017_capacity(&hk, &Hk2017Config::naive()).is_ok() {
                    hk_ok += 1;
                }

                // Stop early if we have enough samples
                if generated >= 50 {
                    break;
                }
            }
        }

        if generated > 0 {
            println!(
                "min_omega={:.3}: generated={}, tube_ok={} ({:.0}%), hk_ok={} ({:.0}%)",
                min_omega,
                generated,
                tube_ok,
                100.0 * tube_ok as f64 / generated as f64,
                hk_ok,
                100.0 * hk_ok as f64 / generated as f64
            );
        } else {
            println!(
                "min_omega={:.3}: no polytopes generated in 500 seeds",
                min_omega
            );
        }
    }
}

/// Trace tube exploration to understand NoClosedOrbits failures.
#[test]
#[ignore]
fn trace_tube_exploration() {
    use tube::preprocess::preprocess;

    println!("\n=== Tube Exploration Trace ===\n");

    // Find a polytope that fails with NoClosedOrbits
    let min_omega = 0.001;
    let mut polytope = None;

    for seed in 0..100 {
        if let Some(p) = fixtures::random_hrep(8, min_omega, seed) {
            if matches!(tube_capacity(&p), Err(TubeError::NoClosedOrbits)) {
                polytope = Some((seed, p));
                break;
            }
        }
    }

    let (seed, polytope) = match polytope {
        Some(p) => p,
        None => {
            println!("No failing polytope found - unexpected!");
            return;
        }
    };

    println!("Analyzing seed={}\n", seed);

    // Get preprocessed data
    let data = preprocess(&polytope).unwrap();

    println!("Polytope structure:");
    println!("  Num facets: {}", data.num_facets);
    println!("  Num 2-faces: {}", data.two_face_data.len());
    println!("  Num transitions: {}", data.transitions.len());

    // Analyze 2-faces
    println!("\n2-face omega values:");
    let mut min_omega_actual = f64::MAX;
    let mut max_omega_actual = 0.0f64;
    for tf in &data.two_face_data {
        min_omega_actual = min_omega_actual.min(tf.omega);
        max_omega_actual = max_omega_actual.max(tf.omega);
    }
    println!(
        "  Range: [{:.6}, {:.6}]",
        min_omega_actual, max_omega_actual
    );

    // Analyze rotation values
    println!("\n2-face rotation values:");
    let rotations: Vec<f64> = data.two_face_data.iter().map(|tf| tf.rotation).collect();
    let min_rot = rotations.iter().cloned().fold(f64::MAX, f64::min);
    let max_rot = rotations.iter().cloned().fold(f64::MIN, f64::max);
    println!(
        "  Range: [{:.4}, {:.4}] (need sum ≈ 2π for closure)",
        min_rot, max_rot
    );

    // Check if rotations can sum to 2π
    let total_positive: f64 = rotations.iter().filter(|&&r| r > 0.0).sum();
    let total_negative: f64 = rotations.iter().filter(|&&r| r < 0.0).sum();
    println!("  Sum of positive rotations: {:.4}", total_positive);
    println!("  Sum of negative rotations: {:.4}", total_negative);
    println!(
        "  Target for closure: 2π = {:.4}",
        2.0 * std::f64::consts::PI
    );

    // Analyze polygon areas
    println!("\n2-face polygon areas:");
    let areas: Vec<f64> = data
        .two_face_data
        .iter()
        .map(|tf| tf.polygon.area())
        .collect();
    let min_area = areas.iter().cloned().fold(f64::MAX, f64::min);
    let max_area = areas.iter().cloned().fold(0.0, f64::max);
    println!("  Range: [{:.6}, {:.6}]", min_area, max_area);
}

/// Compare rotation structure between cross-polytope and random.
#[test]
#[ignore]
fn compare_rotation_structure() {
    use tube::preprocess::preprocess;

    println!("\n=== Rotation Structure Comparison ===\n");

    // Cross-polytope
    let cross = fixtures::unit_cross_polytope();
    let cross_data = preprocess(&cross).unwrap();

    println!("Cross-polytope:");
    println!("  Num 2-faces: {}", cross_data.two_face_data.len());

    let cross_rotations: Vec<f64> = cross_data
        .two_face_data
        .iter()
        .map(|tf| tf.rotation)
        .collect();
    let cross_min = cross_rotations.iter().cloned().fold(f64::MAX, f64::min);
    let cross_max = cross_rotations.iter().cloned().fold(f64::MIN, f64::max);
    let cross_pos_sum: f64 = cross_rotations.iter().filter(|&&r| r > 0.0).sum();
    let cross_neg_sum: f64 = cross_rotations.iter().filter(|&&r| r < 0.0).sum();

    println!("  Rotation range: [{:.4}, {:.4}]", cross_min, cross_max);
    println!("  Sum positive: {:.4}", cross_pos_sum);
    println!("  Sum negative: {:.4}", cross_neg_sum);
    println!("  2π = {:.4}", 2.0 * std::f64::consts::PI);

    // Random polytope (seed=0)
    let random = fixtures::random_hrep(8, 0.001, 0).unwrap();
    let random_data = preprocess(&random).unwrap();

    println!("\nRandom polytope (seed=0):");
    println!("  Num 2-faces: {}", random_data.two_face_data.len());

    let random_rotations: Vec<f64> = random_data
        .two_face_data
        .iter()
        .map(|tf| tf.rotation)
        .collect();
    let random_min = random_rotations.iter().cloned().fold(f64::MAX, f64::min);
    let random_max = random_rotations.iter().cloned().fold(f64::MIN, f64::max);
    let random_pos_sum: f64 = random_rotations.iter().filter(|&&r| r > 0.0).sum();
    let random_neg_sum: f64 = random_rotations.iter().filter(|&&r| r < 0.0).sum();

    println!("  Rotation range: [{:.4}, {:.4}]", random_min, random_max);
    println!("  Sum positive: {:.4}", random_pos_sum);
    println!("  Sum negative: {:.4}", random_neg_sum);

    // Check if closure is possible
    let cross_can_close = cross_pos_sum >= 2.0 * std::f64::consts::PI
        || cross_neg_sum.abs() >= 2.0 * std::f64::consts::PI;
    let random_can_close = random_pos_sum >= 2.0 * std::f64::consts::PI
        || random_neg_sum.abs() >= 2.0 * std::f64::consts::PI;

    println!("\nClosure feasibility:");
    println!("  Cross-polytope can close: {}", cross_can_close);
    println!("  Random polytope can close: {}", random_can_close);
}

/// Analyze transition graph connectivity.
#[test]
#[ignore]
fn analyze_transition_graph() {
    use std::collections::{HashSet, VecDeque};
    use tube::preprocess::preprocess;

    println!("\n=== Transition Graph Analysis ===\n");

    // Cross-polytope
    let cross = fixtures::unit_cross_polytope();
    let cross_data = preprocess(&cross).unwrap();

    println!("Cross-polytope:");
    println!("  Num 2-faces: {}", cross_data.two_face_data.len());
    println!("  Num transitions: {}", cross_data.transitions.len());

    // Build adjacency list
    let mut cross_adj: Vec<Vec<usize>> = vec![vec![]; cross_data.two_face_data.len()];
    for trans in &cross_data.transitions {
        cross_adj[trans.two_face_entry].push(trans.two_face_exit);
    }

    // Count self-loops (direct return to same 2-face)
    let cross_self_loops: usize = cross_adj
        .iter()
        .enumerate()
        .map(|(i, neighbors)| neighbors.iter().filter(|&&j| j == i).count())
        .sum();
    println!("  Self-loops: {}", cross_self_loops);

    // Check strongly connected (can reach any 2-face from any other)
    let cross_reachable = bfs_reachable(&cross_adj, 0);
    println!(
        "  Reachable from 2-face 0: {}/{}",
        cross_reachable.len(),
        cross_data.two_face_data.len()
    );

    // Random polytope
    let random = fixtures::random_hrep(8, 0.001, 0).unwrap();
    let random_data = preprocess(&random).unwrap();

    println!("\nRandom polytope (seed=0):");
    println!("  Num 2-faces: {}", random_data.two_face_data.len());
    println!("  Num transitions: {}", random_data.transitions.len());

    // Build adjacency list
    let mut random_adj: Vec<Vec<usize>> = vec![vec![]; random_data.two_face_data.len()];
    for trans in &random_data.transitions {
        random_adj[trans.two_face_entry].push(trans.two_face_exit);
    }

    // Count self-loops
    let random_self_loops: usize = random_adj
        .iter()
        .enumerate()
        .map(|(i, neighbors)| neighbors.iter().filter(|&&j| j == i).count())
        .sum();
    println!("  Self-loops: {}", random_self_loops);

    // Check connectivity
    let random_reachable = bfs_reachable(&random_adj, 0);
    println!(
        "  Reachable from 2-face 0: {}/{}",
        random_reachable.len(),
        random_data.two_face_data.len()
    );

    // Find shortest cycle for each starting 2-face
    println!("\n  Shortest cycles from each 2-face:");
    for start in 0..random_data.two_face_data.len().min(5) {
        match find_shortest_cycle(&random_adj, start) {
            Some(len) => println!("    2-face {}: length {}", start, len),
            None => println!("    2-face {}: NO CYCLE", start),
        }
    }
}

fn bfs_reachable(adj: &[Vec<usize>], start: usize) -> std::collections::HashSet<usize> {
    use std::collections::{HashSet, VecDeque};

    let mut visited = HashSet::new();
    let mut queue = VecDeque::new();

    visited.insert(start);
    queue.push_back(start);

    while let Some(node) = queue.pop_front() {
        for &neighbor in &adj[node] {
            if visited.insert(neighbor) {
                queue.push_back(neighbor);
            }
        }
    }

    visited
}

fn find_shortest_cycle(adj: &[Vec<usize>], start: usize) -> Option<usize> {
    use std::collections::VecDeque;

    // BFS to find shortest path back to start
    let mut visited = vec![false; adj.len()];
    let mut queue: VecDeque<(usize, usize)> = VecDeque::new(); // (node, distance)

    // Don't mark start as visited initially - we want to find a path back to it
    for &neighbor in &adj[start] {
        if neighbor == start {
            return Some(1); // Self-loop
        }
        queue.push_back((neighbor, 1));
        visited[neighbor] = true;
    }

    while let Some((node, dist)) = queue.pop_front() {
        for &neighbor in &adj[node] {
            if neighbor == start {
                return Some(dist + 1);
            }
            if !visited[neighbor] {
                visited[neighbor] = true;
                queue.push_back((neighbor, dist + 1));
            }
        }
    }

    None
}

/// Analyze 2-face adjacency and transition structure in detail.
#[test]
#[ignore]
fn analyze_adjacency_detail() {
    use tube::preprocess::preprocess;

    println!("\n=== Detailed Adjacency Analysis ===\n");

    // Random polytope
    let random = fixtures::random_hrep(8, 0.001, 0).unwrap();
    let data = preprocess(&random).unwrap();

    println!("Random polytope (seed=0, {} facets):\n", data.num_facets);

    // List all 2-faces
    println!("2-faces (entry_facet -> exit_facet):");
    for (k, tf) in data.two_face_data.iter().enumerate() {
        println!(
            "  2-face {}: {} -> {} (omega={:.4}, rot={:.4})",
            k, tf.entry_facet, tf.exit_facet, tf.omega, tf.rotation
        );
    }

    // For each 2-face, show what transitions exist
    println!("\nTransitions (2-face_entry -> 2-face_exit via facet_mid):");
    for trans in &data.transitions {
        let tf_entry = &data.two_face_data[trans.two_face_entry];
        let tf_exit = &data.two_face_data[trans.two_face_exit];
        println!(
            "  2-face {} ({}->{}) -> 2-face {} ({}->{}) via facet {}",
            trans.two_face_entry,
            tf_entry.entry_facet,
            tf_entry.exit_facet,
            trans.two_face_exit,
            tf_exit.entry_facet,
            tf_exit.exit_facet,
            trans.facet_mid
        );
    }

    // Count outgoing transitions per 2-face
    println!("\nOutgoing transitions per 2-face:");
    for k in 0..data.two_face_data.len() {
        let count = data.lookup.transitions_from(k).len();
        let tf = &data.two_face_data[k];
        println!(
            "  2-face {} ({} -> {}): {} outgoing",
            k, tf.entry_facet, tf.exit_facet, count
        );
    }

    // Now analyze why connectivity is low:
    // For each 2-face exit_facet, count how many 2-faces have it as entry_facet
    println!("\nFacet usage as entry vs exit:");
    for facet in 0..data.num_facets {
        let as_entry = data
            .two_face_data
            .iter()
            .filter(|tf| tf.entry_facet == facet)
            .count();
        let as_exit = data
            .two_face_data
            .iter()
            .filter(|tf| tf.exit_facet == facet)
            .count();
        println!("  Facet {}: entry={}, exit={}", facet, as_entry, as_exit);
    }
}

/// Investigate whether Lagrangian 2-faces being filtered causes the sink pattern.
///
/// This test checks the user's hypothesis from issue #155:
/// 1. Does every 2-face have entry & exit facet? (YES by construction)
/// 2. Are some 2-faces Lagrangian and filtered, creating "holes"?
/// 3. Does every facet appear both as entry and exit (balanced)?
#[test]
#[ignore]
fn investigate_lagrangian_filtering() {
    use tube::constants::EPS_LAGRANGIAN;

    println!("\n=== Lagrangian Filtering Investigation ===\n");

    // Use seed=0 which we know fails
    let random = fixtures::random_hrep(8, 0.001, 0).unwrap();
    let n = random.num_facets();

    println!("Analyzing all facet pairs for {} facets:\n", n);

    // Compute omega for ALL pairs and check Lagrangian status
    let mut all_2faces: Vec<(usize, usize, f64, bool, Option<(usize, usize)>)> = Vec::new();

    for i in 0..n {
        for j in (i + 1)..n {
            let ni = &random.normals[i];
            let nj = &random.normals[j];
            // omega(a, b) = a1*b3 - a3*b1 + a2*b4 - a4*b2 = <J*a, b>
            let omega_ij = ni[0] * nj[2] - ni[2] * nj[0] + ni[1] * nj[3] - ni[3] * nj[1];
            let is_lagrangian = omega_ij.abs() < EPS_LAGRANGIAN;

            // Determine flow direction (entry, exit)
            let flow_dir = if is_lagrangian {
                None
            } else if omega_ij > 0.0 {
                Some((i, j)) // flow i -> j
            } else {
                Some((j, i)) // flow j -> i
            };

            all_2faces.push((i, j, omega_ij, is_lagrangian, flow_dir));
        }
    }

    // Note: Not all pairs (i,j) are actual 2-faces - need to check adjacency
    // For now, let's count omega signs per facet to understand the pattern

    println!("Omega sign analysis per facet:");
    println!("(For facet k: count pairs where omega > 0 vs < 0 vs ≈0)");
    println!();

    for facet in 0..n {
        let mut pos = 0;
        let mut neg = 0;
        let mut lagr = 0;

        for &(i, j, omega, is_lagr, _) in &all_2faces {
            if i == facet || j == facet {
                if is_lagr {
                    lagr += 1;
                } else if (i == facet && omega > 0.0) || (j == facet && omega < 0.0) {
                    // Facet is entry (flow goes OUT of facet)
                    pos += 1;
                } else {
                    // Facet is exit (flow goes INTO facet)
                    neg += 1;
                }
            }
        }
        println!(
            "  Facet {}: out={}, in={}, lagrangian={}",
            facet, pos, neg, lagr
        );
    }

    println!("\n--- Checking actual 2-faces (share ≥3 vertices) ---\n");

    // Now check which pairs are actual 2-faces by using preprocess
    use tube::preprocess::preprocess;
    let data = preprocess(&random).unwrap();

    println!("Total 2-faces found: {}", data.two_face_data.len());
    println!(
        "Has Lagrangian 2-faces: {}",
        data.has_lagrangian_two_faces()
    );

    // Count entry/exit usage
    let mut entry_count = vec![0usize; n];
    let mut exit_count = vec![0usize; n];

    for tf in &data.two_face_data {
        entry_count[tf.entry_facet] += 1;
        exit_count[tf.exit_facet] += 1;
    }

    println!("\nFacet entry/exit balance (non-Lagrangian 2-faces only):");
    for facet in 0..n {
        let status = if entry_count[facet] == 0 && exit_count[facet] > 0 {
            "← SINK (in but no out)"
        } else if entry_count[facet] > 0 && exit_count[facet] == 0 {
            "← SOURCE (out but no in)"
        } else if entry_count[facet] == 0 && exit_count[facet] == 0 {
            "← ISOLATED"
        } else {
            ""
        };
        println!(
            "  Facet {}: entry={}, exit={} {}",
            facet, entry_count[facet], exit_count[facet], status
        );
    }

    // Key question: for facets that are sinks, are there Lagrangian 2-faces
    // that would provide the missing "exit" paths?
    println!("\n--- Checking if Lagrangian 2-faces explain sinks ---\n");

    for facet in 0..n {
        if entry_count[facet] == 0 && exit_count[facet] > 0 {
            println!("Facet {} is a SINK. Checking for Lagrangian exits:", facet);

            // Find all potential 2-faces involving this facet
            for other in 0..n {
                if other == facet {
                    continue;
                }
                let (i, j) = if facet < other {
                    (facet, other)
                } else {
                    (other, facet)
                };

                // Find this pair in our list
                for &(pi, pj, omega, is_lagr, flow_dir) in &all_2faces {
                    if pi == i && pj == j {
                        let would_be_entry = match flow_dir {
                            Some((entry, _)) => entry == facet,
                            None => false,
                        };

                        if is_lagr {
                            println!("  ({}, {}): LAGRANGIAN (ω={:.2e}) - filtered!", i, j, omega);
                        } else if would_be_entry {
                            println!(
                                "  ({}, {}): ω={:.4} -> flow {}->{} (facet {} is entry)",
                                i,
                                j,
                                omega,
                                flow_dir.unwrap().0,
                                flow_dir.unwrap().1,
                                facet
                            );
                        }
                    }
                }
            }
            println!();
        }
    }
}

/// Investigate why facets 0 and 6 are isolated in the random polytope.
/// Check vertex sharing between facets.
#[test]
#[ignore]
fn investigate_isolated_facets() {
    use tube::constants::EPS;

    println!("\n=== Investigating Isolated Facets ===\n");

    let random = fixtures::random_hrep(8, 0.001, 0).unwrap();
    let n = random.num_facets();

    // First, enumerate all vertices
    use nalgebra::{Matrix4, Vector4};
    let mut vertices: Vec<Vector4<f64>> = Vec::new();

    for i in 0..n {
        for j in (i + 1)..n {
            for k in (j + 1)..n {
                for l in (k + 1)..n {
                    let m = Matrix4::from_rows(&[
                        random.normals[i].transpose(),
                        random.normals[j].transpose(),
                        random.normals[k].transpose(),
                        random.normals[l].transpose(),
                    ]);

                    if let Some(m_inv) = m.try_inverse() {
                        let h = Vector4::new(
                            random.heights[i],
                            random.heights[j],
                            random.heights[k],
                            random.heights[l],
                        );
                        let candidate = m_inv * h;

                        // Check if candidate satisfies all constraints
                        let is_valid = random
                            .normals
                            .iter()
                            .zip(&random.heights)
                            .all(|(n, &h)| n.dot(&candidate) <= h + EPS);

                        if is_valid {
                            let is_dup = vertices
                                .iter()
                                .any(|v: &Vector4<f64>| (v - candidate).norm() < EPS);
                            if !is_dup {
                                vertices.push(candidate);
                            }
                        }
                    }
                }
            }
        }
    }

    println!("Total vertices found: {}", vertices.len());

    // For each vertex, determine which facets it belongs to
    let mut vertex_facets: Vec<Vec<usize>> = Vec::new();
    for v in &vertices {
        let mut facets = Vec::new();
        for (i, (n, h)) in random.normals.iter().zip(&random.heights).enumerate() {
            if (n.dot(v) - h).abs() < EPS {
                facets.push(i);
            }
        }
        vertex_facets.push(facets);
    }

    println!("\nVertices and their facets:");
    for (idx, facets) in vertex_facets.iter().enumerate() {
        println!("  Vertex {}: on facets {:?}", idx, facets);
    }

    // Now count shared vertices between facet pairs
    println!("\nFacet pair adjacency (# shared vertices):");
    for i in 0..n {
        for j in (i + 1)..n {
            let shared: Vec<usize> = vertex_facets
                .iter()
                .enumerate()
                .filter(|(_, facets)| facets.contains(&i) && facets.contains(&j))
                .map(|(idx, _)| idx)
                .collect();

            let indicator = if shared.len() >= 3 {
                "← 2-FACE"
            } else if shared.len() > 0 {
                ""
            } else {
                "← NO ADJACENCY"
            };

            if shared.len() > 0 || i == 0 || i == 6 || j == 0 || j == 6 {
                println!(
                    "  ({}, {}): {} shared vertices {:?} {}",
                    i,
                    j,
                    shared.len(),
                    shared,
                    indicator
                );
            }
        }
    }

    // Check facets 0 and 6 specifically
    println!("\n--- Facet 0 analysis ---");
    let facet0_vertices: Vec<usize> = vertex_facets
        .iter()
        .enumerate()
        .filter(|(_, f)| f.contains(&0))
        .map(|(i, _)| i)
        .collect();
    println!("Vertices on facet 0: {:?}", facet0_vertices);

    println!("\n--- Facet 6 analysis ---");
    let facet6_vertices: Vec<usize> = vertex_facets
        .iter()
        .enumerate()
        .filter(|(_, f)| f.contains(&6))
        .map(|(i, _)| i)
        .collect();
    println!("Vertices on facet 6: {:?}", facet6_vertices);
}

/// Test that for the cross-polytope, every facet appears as both entry and exit.
/// This is the "balanced" property that random polytopes seem to violate.
#[test]
#[ignore]
fn test_cross_polytope_entry_exit_balance() {
    use tube::preprocess::preprocess;

    println!("\n=== Cross-polytope Entry/Exit Balance ===\n");

    let cross = fixtures::unit_cross_polytope();
    let data = preprocess(&cross).unwrap();

    let n = data.num_facets;
    let mut entry_count = vec![0usize; n];
    let mut exit_count = vec![0usize; n];

    for tf in &data.two_face_data {
        entry_count[tf.entry_facet] += 1;
        exit_count[tf.exit_facet] += 1;
    }

    println!(
        "Cross-polytope ({} facets, {} 2-faces):",
        n,
        data.two_face_data.len()
    );
    println!();

    let mut balanced = true;
    for facet in 0..n {
        let is_balanced = entry_count[facet] > 0 && exit_count[facet] > 0;
        if !is_balanced {
            balanced = false;
        }
        println!(
            "  Facet {:2}: entry={:2}, exit={:2} {}",
            facet,
            entry_count[facet],
            exit_count[facet],
            if is_balanced { "✓" } else { "✗ UNBALANCED" }
        );
    }

    println!();
    if balanced {
        println!("All facets are balanced (appear as both entry and exit)");
    } else {
        println!("WARNING: Some facets are unbalanced!");
    }

    // For symmetric polytopes, we expect equal counts
    let entry_sum: usize = entry_count.iter().sum();
    let exit_sum: usize = exit_count.iter().sum();
    println!("\nTotal: entry_sum={}, exit_sum={}", entry_sum, exit_sum);

    assert!(balanced, "Cross-polytope should have balanced facets");
}

/// Test the user's proposition about transition structure:
///
/// For all non-Lagrangian polytopes K, for all facets F:
/// - Let A = 2-faces where F is entry (trajectories EXIT F through these)
/// - Let B = 2-faces where F is exit (trajectories ENTER F through these)
/// Then:
/// - Any a ∈ A has transitions only to elements of B (not to other 2-faces)
/// - Any b ∈ B has transitions only from elements of A (not from other 2-faces)
///
/// This tests whether the transition structure is consistent with the Reeb flow.
#[test]
#[ignore]
fn test_transition_structure_proposition() {
    use tube::preprocess::preprocess;

    println!("\n=== Transition Structure Proposition Test ===\n");

    // Test on cross-polytope (known to work)
    println!("--- Cross-polytope ---\n");
    let cross = fixtures::unit_cross_polytope();
    test_proposition_on_polytope(&cross, "cross-polytope");

    // Test on random polytope (known to fail)
    println!("\n--- Random polytope (seed=0) ---\n");
    if let Some(random) = fixtures::random_hrep(8, 0.001, 0) {
        test_proposition_on_polytope(&random, "random-seed0");
    }
}

fn test_proposition_on_polytope(hrep: &TubeHrep, name: &str) {
    use tube::preprocess::preprocess;

    let data = match preprocess(hrep) {
        Ok(d) => d,
        Err(e) => {
            println!("{}: preprocessing failed: {}", name, e);
            return;
        }
    };

    let n = data.num_facets;
    let num_2faces = data.two_face_data.len();

    println!(
        "{}: {} facets, {} 2-faces, {} transitions",
        name,
        n,
        num_2faces,
        data.transitions.len()
    );

    // For each facet, compute A (entry 2-faces) and B (exit 2-faces)
    for facet in 0..n {
        let a: Vec<usize> = data
            .two_face_data
            .iter()
            .enumerate()
            .filter(|(_, tf)| tf.entry_facet == facet)
            .map(|(k, _)| k)
            .collect();

        let b: Vec<usize> = data
            .two_face_data
            .iter()
            .enumerate()
            .filter(|(_, tf)| tf.exit_facet == facet)
            .map(|(k, _)| k)
            .collect();

        if a.is_empty() && b.is_empty() {
            println!("  Facet {}: ISOLATED (no 2-faces)", facet);
            continue;
        }

        // Check: transitions from A should go to B
        let mut a_to_b_ok = true;
        let mut violations_a_to_b: Vec<String> = Vec::new();

        for &a_idx in &a {
            let trans_from_a = data.lookup.transitions_from(a_idx);
            for &trans_idx in trans_from_a {
                let trans = &data.transitions[trans_idx];
                let target_2face = trans.two_face_exit;

                // The target 2-face should have entry_facet = our facet
                // (since we're transitioning through facet, the next 2-face
                // should have this facet as entry)
                let target_tf = &data.two_face_data[target_2face];

                // Actually, the proposition says: transitions from a ∈ A go to B
                // B = 2-faces where F is exit
                // After flowing along F, we exit F through some 2-face
                // That 2-face should have F as entry (because we're leaving F)

                // Wait, let me re-read the code...
                // A transition from 2-face k_entry to k_exit means:
                // - We're on 2-face k_entry, which has (entry_facet, exit_facet)
                // - We flow along exit_facet (the "facet_mid")
                // - We end up on 2-face k_exit

                // So if 2-face a has entry_facet = F:
                // - Trajectories are on F, approaching 2-face a
                // - They cross into exit_facet of a
                // - Transitions from a go to 2-faces where the target has
                //   entry_facet = a.exit_facet

                // The proposition seems to be about the structure:
                // If F is entry_facet of a, then transitions from a
                // involve flowing along a.exit_facet, not F.
                // So transitions from A don't directly go to B for the same F.

                // Let me re-interpret: the proposition might be saying
                // that the transition graph through facet F is well-structured.

                // Actually, let me check: for 2-face a with entry=F, exit=G:
                // - Transitions from a involve flowing along G
                // - After flowing along G, we reach some 2-face b
                // - b has entry_facet = G (since we just flowed along G)

                // So transitions from A (where entry=F) go to 2-faces where
                // entry_facet = exit_facet of a = the "other" facet of a.

                // I think the proposition needs clarification.
                // Let me just check what the transitions look like.
            }
        }

        // Actually, let me just print the transition structure for each facet
        if !a.is_empty() || !b.is_empty() {
            println!("  Facet {}: A(entry)={:?}, B(exit)={:?}", facet, a, b);

            // For each a in A, show where transitions go
            for &a_idx in &a {
                let tf_a = &data.two_face_data[a_idx];
                let trans_from_a: Vec<_> = data
                    .lookup
                    .transitions_from(a_idx)
                    .iter()
                    .map(|&t_idx| {
                        let t = &data.transitions[t_idx];
                        let target = &data.two_face_data[t.two_face_exit];
                        (t.two_face_exit, target.entry_facet, target.exit_facet)
                    })
                    .collect();

                println!(
                    "    From 2-face {} ({}->{}) via {}: goes to {:?}",
                    a_idx, tf_a.entry_facet, tf_a.exit_facet, tf_a.exit_facet, trans_from_a
                );
            }

            // For each b in B, show where transitions come from
            for &b_idx in &b {
                let tf_b = &data.two_face_data[b_idx];
                let trans_to_b: Vec<_> = data
                    .transitions
                    .iter()
                    .filter(|t| t.two_face_exit == b_idx)
                    .map(|t| {
                        let source = &data.two_face_data[t.two_face_entry];
                        (t.two_face_entry, source.entry_facet, source.exit_facet)
                    })
                    .collect();

                if trans_to_b.is_empty() {
                    println!(
                        "    To 2-face {} ({}->{}) via {}: NO INCOMING TRANSITIONS",
                        b_idx, tf_b.entry_facet, tf_b.exit_facet, tf_b.entry_facet
                    );
                }
            }
        }
    }
}
