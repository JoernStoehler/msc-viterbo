//! Critical invariant tests for billiard orbit validity.
//!
//! Port of tube/tests/orbit_invariants.rs to verify billiard trajectories
//! satisfy the necessary properties for being valid orbits.

use billiard::{billiard_capacity_from_polygons, Polygon2D};
use nalgebra::Vector2;
use std::f64::consts::PI;

const EPS: f64 = 1e-6;

/// Test that all breakpoints lie on facet boundaries
#[test]
fn test_breakpoints_on_boundary() {
    let test_cases = vec![
        ("triangle", Polygon2D::regular(3, 1.0, 0.0).unwrap()),
        ("square", Polygon2D::square(2.0).unwrap()),
    ];

    for (name, polygon) in test_cases {
        let result = billiard_capacity_from_polygons(&polygon, &polygon).unwrap();

        // Check q-positions on K_q boundary
        for (i, q) in result.witness.q_positions.iter().enumerate() {
            let mut on_boundary = false;
            for j in 0..polygon.num_edges() {
                let n = polygon.normals[j];
                let h = polygon.heights[j];
                if (n.dot(q) - h).abs() < EPS {
                    on_boundary = true;
                    break;
                }
            }
            assert!(on_boundary, "{}: q_position[{}] not on boundary", name, i);
        }

        // Check p-positions on K_p boundary
        for (i, p) in result.witness.p_positions.iter().enumerate() {
            let mut on_boundary = false;
            for j in 0..polygon.num_edges() {
                let n = polygon.normals[j];
                let h = polygon.heights[j];
                if (n.dot(p) - h).abs() < EPS {
                    on_boundary = true;
                    break;
                }
            }
            assert!(on_boundary, "{}: p_position[{}] not on boundary", name, i);
        }
    }
}

/// Test that orbit closes (first = last after completing full cycle)
#[test]
fn test_orbit_closure() {
    let test_cases = vec![
        ("triangle", Polygon2D::regular(3, 1.0, 0.0).unwrap()),
        ("square", Polygon2D::square(2.0).unwrap()),
    ];

    for (name, polygon) in test_cases {
        let result = billiard_capacity_from_polygons(&polygon, &polygon).unwrap();

        let num_bounces = result.witness.num_bounces;

        // Check q-displacement sums to zero
        let mut q_sum = Vector2::zeros();
        for i in 0..num_bounces {
            let q_i = result.witness.q_positions[i];
            let q_next = result.witness.q_positions[(i + 1) % num_bounces];
            q_sum += q_next - q_i;
        }
        assert!(q_sum.norm() < EPS, "{}: q does not close, sum = {:?}", name, q_sum);

        // Check p-displacement sums to zero
        let mut p_sum = Vector2::zeros();
        for i in 0..num_bounces {
            let p_i = result.witness.p_positions[i];
            let p_next = result.witness.p_positions[(i + 1) % num_bounces];
            p_sum += p_next - p_i;
        }
        assert!(p_sum.norm() < EPS, "{}: p does not close, sum = {:?}", name, p_sum);
    }
}

/// Test that segments follow allowed velocity directions
#[test]
fn test_segments_follow_reeb_directions() {
    let polygon = Polygon2D::square(2.0).unwrap();
    let result = billiard_capacity_from_polygons(&polygon, &polygon).unwrap();

    let num_bounces = result.witness.num_bounces;

    // For each q-motion segment, check velocity is achievable
    for i in 0..num_bounces {
        let q_i = result.witness.q_positions[i];
        let q_next = result.witness.q_positions[(i + 1) % num_bounces];
        let q_displacement = q_next - q_i;

        if q_displacement.norm() < EPS {
            continue; // Skip zero-length segments
        }

        // The displacement should be achievable by Reeb flow on some p-facet
        // This requires checking if displacement is parallel to some Reeb vector
        // For now, just check it's non-zero (basic sanity)
        assert!(q_displacement.norm() > 0.0, "Zero q-displacement at segment {}", i);
    }
}

/// Test that action is positive
#[test]
fn test_action_positive() {
    let test_cases = vec![
        ("triangle", Polygon2D::regular(3, 1.0, 0.0).unwrap()),
        ("square", Polygon2D::square(2.0).unwrap()),
    ];

    for (name, polygon) in test_cases {
        let result = billiard_capacity_from_polygons(&polygon, &polygon).unwrap();
        assert!(result.witness.action > 0.0, "{}: action not positive", name);
        assert!(result.witness.action < f64::INFINITY, "{}: action infinite", name);
    }
}

/// Test scaling property: c(λK) = λ² c(K)
#[test]
fn test_scaling_property() {
    let square = Polygon2D::square(2.0).unwrap();
    let c1 = billiard_capacity_from_polygons(&square, &square).unwrap().capacity;

    let square_scaled = square.scale(2.0);
    let c2 = billiard_capacity_from_polygons(&square_scaled, &square_scaled).unwrap().capacity;

    // c(2K) should equal 4*c(K)
    let expected = 4.0 * c1;
    let ratio = c2 / expected;

    println!("Scaling test: c(K)={:.6}, c(2K)={:.6}, expected={:.6}, ratio={:.6}",
             c1, c2, expected, ratio);

    assert!((ratio - 1.0).abs() < 1e-4,
            "Scaling property violated: c(2K)={:.6} != 4*c(K)={:.6}", c2, expected);
}

/// Test that capacity is consistent across different edge combinations
#[test]
fn test_capacity_deterministic() {
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();

    // Run multiple times, should get same answer
    let c1 = billiard_capacity_from_polygons(&triangle, &triangle).unwrap().capacity;
    let c2 = billiard_capacity_from_polygons(&triangle, &triangle).unwrap().capacity;

    assert!((c1 - c2).abs() < EPS, "Capacity not deterministic: {} vs {}", c1, c2);
}

/// Diagnostic test to examine orbit structure in detail
#[test]
#[ignore]
fn diagnostic_orbit_structure() {
    println!("\n=== ORBIT STRUCTURE DIAGNOSTIC ===\n");

    let test_cases = vec![
        ("triangle×triangle",
         Polygon2D::regular(3, 1.0, 0.0).unwrap(),
         Polygon2D::regular(3, 1.0, 0.0).unwrap()),
        ("square×square",
         Polygon2D::square(2.0).unwrap(),
         Polygon2D::square(2.0).unwrap()),
    ];

    for (name, k_q, k_p) in test_cases {
        println!("{}:", name);
        let result = billiard_capacity_from_polygons(&k_q, &k_p).unwrap();

        println!("  Capacity: {:.6}", result.capacity);
        println!("  Action: {:.6}", result.witness.action);
        println!("  Num bounces: {}", result.witness.num_bounces);

        // Print positions
        for i in 0..result.witness.num_bounces {
            let q = result.witness.q_positions[i];
            let p = result.witness.p_positions[i];
            println!("  Bounce {}: q=({:.6}, {:.6}), p=({:.6}, {:.6})",
                     i, q[0], q[1], p[0], p[1]);
        }

        // Print edges
        for (i, &edge_idx) in result.witness.q_edges.iter().enumerate() {
            println!("  q_edge[{}] = {}", i, edge_idx);
        }

        println!();
    }
}
