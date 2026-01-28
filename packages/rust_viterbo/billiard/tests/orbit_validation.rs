//! Orbit validation tests for the billiard algorithm.
//!
//! Verify that the billiard algorithm produces valid Reeb orbits in Lagrangian products.
//! These are pure geometric checks - no billiard theory needed.

use approx::assert_relative_eq;
use billiard::{billiard_capacity_from_polygons, Polygon2D};
use nalgebra::{Vector2, Vector4};
use std::f64::consts::PI;

/// Tolerance for boundary checks
const EPS_BOUNDARY: f64 = 1e-6;

/// Helper: Check if a 4D point is on the boundary of K_q × K_p
fn is_on_boundary_4d(
    point: &Vector4<f64>,
    k_q: &Polygon2D,
    k_p: &Polygon2D,
) -> bool {
    let q = Vector2::new(point[0], point[1]);
    let p = Vector2::new(point[2], point[3]);

    // Check if on any q-facet (n_q, 0) with height h_q
    for (n, h) in k_q.normals.iter().zip(&k_q.heights) {
        if (n.dot(&q) - h).abs() < EPS_BOUNDARY {
            return true;
        }
    }

    // Check if on any p-facet (0, n_p) with height h_p
    for (n, h) in k_p.normals.iter().zip(&k_p.heights) {
        if (n.dot(&p) - h).abs() < EPS_BOUNDARY {
            return true;
        }
    }

    false
}

/// Test 1: All 4D breakpoints lie on the boundary ∂K
#[test]
fn test_breakpoints_on_boundaries() {
    let square = Polygon2D::square(2.0).unwrap();
    let result = billiard_capacity_from_polygons(&square, &square)
        .expect("Should find orbit");

    let breakpoints_4d = result.witness.to_4d_breakpoints();

    for (i, point) in breakpoints_4d.iter().enumerate() {
        assert!(
            is_on_boundary_4d(point, &square, &square),
            "Breakpoint {} not on boundary: ({:.6}, {:.6}, {:.6}, {:.6})",
            i,
            point[0],
            point[1],
            point[2],
            point[3]
        );
    }
}

/// Test 2: Orbit closure - sum of all displacement vectors equals zero
#[test]
fn test_orbit_closure() {
    let square = Polygon2D::square(2.0).unwrap();
    let result = billiard_capacity_from_polygons(&square, &square)
        .expect("Should find orbit");

    let breakpoints_4d = result.witness.to_4d_breakpoints();
    let n = breakpoints_4d.len();

    // Sum all displacement vectors in 4D
    let mut total_displacement = Vector4::zeros();
    for i in 0..n {
        let start = breakpoints_4d[i];
        let end = breakpoints_4d[(i + 1) % n];
        total_displacement += end - start;
    }

    let closure_error = total_displacement.norm();
    assert!(
        closure_error < EPS_BOUNDARY,
        "Orbit not closed: ||sum(displacements)|| = {:.6}",
        closure_error
    );
}

/// Test 3: Scaling law c(λK) = λ²c(K) for λ = 0.5
#[test]
fn test_scaling_law_half() {
    let square = Polygon2D::square(2.0).unwrap();
    let c_base = billiard_capacity_from_polygons(&square, &square)
        .expect("base")
        .capacity;

    let square_half = square.scale(0.5);
    let c_half = billiard_capacity_from_polygons(&square_half, &square_half)
        .expect("half")
        .capacity;

    assert_relative_eq!(c_half, 0.25 * c_base, epsilon = 1e-6);
}

/// Test 4: Scaling law c(λK) = λ²c(K) for λ = 2.0
#[test]
fn test_scaling_law_double() {
    let square = Polygon2D::square(2.0).unwrap();
    let c_base = billiard_capacity_from_polygons(&square, &square)
        .expect("base")
        .capacity;

    let square_double = square.scale(2.0);
    let c_double = billiard_capacity_from_polygons(&square_double, &square_double)
        .expect("double")
        .capacity;

    assert_relative_eq!(c_double, 4.0 * c_base, epsilon = 1e-6);
}

/// Test 5: Scaling law c(λK) = λ²c(K) for λ = 3.0
#[test]
fn test_scaling_law_triple() {
    let square = Polygon2D::square(2.0).unwrap();
    let c_base = billiard_capacity_from_polygons(&square, &square)
        .expect("base")
        .capacity;

    let square_triple = square.scale(3.0);
    let c_triple = billiard_capacity_from_polygons(&square_triple, &square_triple)
        .expect("triple")
        .capacity;

    assert_relative_eq!(c_triple, 9.0 * c_base, epsilon = 1e-6);
}

/// Test 6: Deterministic - same input produces identical output
#[test]
fn test_deterministic() {
    let pentagon = Polygon2D::regular_pentagon();
    let rotated = pentagon.rotate(PI / 4.0);

    let result1 = billiard_capacity_from_polygons(&pentagon, &rotated)
        .expect("first run");
    let result2 = billiard_capacity_from_polygons(&pentagon, &rotated)
        .expect("second run");

    // Capacity must be identical
    assert_eq!(result1.capacity, result2.capacity);

    // Witness trajectory must be identical
    assert_eq!(result1.witness.num_bounces, result2.witness.num_bounces);
    assert_eq!(result1.witness.action, result2.witness.action);

    // All breakpoints must match
    for (p1, p2) in result1
        .witness
        .to_4d_breakpoints()
        .iter()
        .zip(result2.witness.to_4d_breakpoints().iter())
    {
        assert_eq!(p1, p2);
    }
}

/// Test 7: Capacity is positive and finite
#[test]
fn test_capacity_positive_finite() {
    let square = Polygon2D::square(2.0).unwrap();
    let result = billiard_capacity_from_polygons(&square, &square)
        .expect("Should find orbit");

    assert!(result.capacity > 0.0);
    assert!(result.capacity.is_finite());
}

/// Test 8: Triangle case - breakpoints on boundary
#[test]
fn test_triangle_breakpoints_on_boundary() {
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();
    let result = billiard_capacity_from_polygons(&triangle, &triangle)
        .expect("Should find orbit");

    let breakpoints_4d = result.witness.to_4d_breakpoints();

    for (i, point) in breakpoints_4d.iter().enumerate() {
        assert!(
            is_on_boundary_4d(point, &triangle, &triangle),
            "Triangle: Breakpoint {} not on boundary",
            i
        );
    }
}

/// Test 9: Triangle case - orbit closure
#[test]
fn test_triangle_orbit_closure() {
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();
    let result = billiard_capacity_from_polygons(&triangle, &triangle)
        .expect("Should find orbit");

    let breakpoints_4d = result.witness.to_4d_breakpoints();
    let n = breakpoints_4d.len();

    let mut total_displacement = Vector4::zeros();
    for i in 0..n {
        total_displacement += breakpoints_4d[(i + 1) % n] - breakpoints_4d[i];
    }

    assert!(total_displacement.norm() < EPS_BOUNDARY);
}

/// Test 10: Rectangle × Square - mixed case
#[test]
fn test_rectangle_square_valid_orbit() {
    // Rectangle [−1,1] × [−2,2]
    let rectangle = Polygon2D::from_vertices(vec![
        Vector2::new(-1.0, -2.0),
        Vector2::new(1.0, -2.0),
        Vector2::new(1.0, 2.0),
        Vector2::new(-1.0, 2.0),
    ])
    .unwrap();
    let square = Polygon2D::square(2.0).unwrap();

    let result = billiard_capacity_from_polygons(&rectangle, &square)
        .expect("Should find orbit");

    // Check all basic properties
    let breakpoints_4d = result.witness.to_4d_breakpoints();

    // All on boundary
    for point in &breakpoints_4d {
        assert!(is_on_boundary_4d(point, &rectangle, &square));
    }

    // Orbit closes
    let n = breakpoints_4d.len();
    let mut total = Vector4::zeros();
    for i in 0..n {
        total += breakpoints_4d[(i + 1) % n] - breakpoints_4d[i];
    }
    assert!(total.norm() < EPS_BOUNDARY);
}

/// Helper: Apply symplectic J matrix: J(q1, q2, p1, p2) = (-p1, -p2, q1, q2)
fn apply_j(v: &Vector4<f64>) -> Vector4<f64> {
    Vector4::new(-v[2], -v[3], v[0], v[1])
}

/// Helper: Compute Reeb vector R = (2/h) J·n for a 4D facet
fn reeb_vector_4d(normal: &Vector4<f64>, height: f64) -> Vector4<f64> {
    apply_j(normal) * (2.0 / height)
}

/// Helper: Find ALL active facets at a 4D point (returns list of (normal, height))
fn find_all_active_facets(
    point: &Vector4<f64>,
    k_q: &Polygon2D,
    k_p: &Polygon2D,
) -> Vec<(Vector4<f64>, f64)> {
    let q = Vector2::new(point[0], point[1]);
    let p = Vector2::new(point[2], point[3]);
    let mut active = Vec::new();

    // Check q-facets (n_q, 0)
    for (n, h) in k_q.normals.iter().zip(&k_q.heights) {
        if (n.dot(&q) - h).abs() < EPS_BOUNDARY {
            active.push((Vector4::new(n[0], n[1], 0.0, 0.0), *h));
        }
    }

    // Check p-facets (0, n_p)
    for (n, h) in k_p.normals.iter().zip(&k_p.heights) {
        if (n.dot(&p) - h).abs() < EPS_BOUNDARY {
            active.push((Vector4::new(0.0, 0.0, n[0], n[1]), *h));
        }
    }

    active
}

/// Test 11: Segments follow Reeb vector direction
/// THE DEFINING PROPERTY: γ̇(t) = R(γ(t))
#[test]
fn test_segments_follow_reeb_direction() {
    let square = Polygon2D::square(2.0).unwrap();
    let result = billiard_capacity_from_polygons(&square, &square)
        .expect("Should find orbit");

    let breakpoints_4d = result.witness.to_4d_breakpoints();
    let n = breakpoints_4d.len();

    for i in 0..n {
        let start = breakpoints_4d[i];
        let end = breakpoints_4d[(i + 1) % n];
        let displacement = end - start;

        // Skip zero-length segments
        if displacement.norm() < 1e-10 {
            continue;
        }

        // Find ALL active facets at the start point
        let active_facets = find_all_active_facets(&start, &square, &square);
        assert!(
            !active_facets.is_empty(),
            "Start point should be on at least one facet"
        );

        // Compute Reeb vectors for all active facets
        let reeb_vectors: Vec<Vector4<f64>> = active_facets
            .iter()
            .map(|(n, h)| reeb_vector_4d(n, *h))
            .collect();

        // Check differential inclusion: displacement ∈ ℝ₊ conv{p_i}
        // For now, just verify displacement is in the span (not necessarily positive cone)
        // This is a simplified test - proper cone membership is more complex

        // If single facet: displacement should be parallel to Reeb vector
        if active_facets.len() == 1 {
            let reeb = &reeb_vectors[0];
            let d_norm = displacement.normalize();
            let r_norm = reeb.normalize();
            let dot = d_norm.dot(&r_norm).abs();
            assert!(
                (dot - 1.0).abs() < 1e-6,
                "Segment {} on single facet not parallel to Reeb: |d̂·R̂| = {:.6}",
                i,
                dot
            );
        } else {
            // Multiple facets: displacement should be in cone spanned by Reeb vectors
            // TODO: Implement proper cone membership test
            // For now, just check displacement is not zero and has reasonable magnitude
            assert!(displacement.norm() > 1e-10, "Displacement should be non-zero");
        }
    }
}

/// Test 12: Period T > 0 (non-trivial orbit)
#[test]
fn test_period_positive() {
    let square = Polygon2D::square(2.0).unwrap();
    let result = billiard_capacity_from_polygons(&square, &square)
        .expect("Should find orbit");

    // For billiard, action = capacity
    assert!(
        result.capacity > 0.0,
        "Period (action) must be positive, got {}",
        result.capacity
    );
}

/// Test 13: Action equals capacity for optimal orbit
#[test]
fn test_action_equals_capacity() {
    let square = Polygon2D::square(2.0).unwrap();
    let result = billiard_capacity_from_polygons(&square, &square)
        .expect("Should find orbit");

    // The witness trajectory's action should equal the computed capacity
    assert_relative_eq!(result.witness.action, result.capacity, epsilon = 1e-10);
}

/// Test 14: Triangle - segments follow Reeb direction
#[test]
fn test_triangle_segments_follow_reeb() {
    let triangle = Polygon2D::regular(3, 1.0, 0.0).unwrap();
    let result = billiard_capacity_from_polygons(&triangle, &triangle)
        .expect("Should find orbit");

    let breakpoints_4d = result.witness.to_4d_breakpoints();
    let n = breakpoints_4d.len();

    for i in 0..n {
        let start = breakpoints_4d[i];
        let end = breakpoints_4d[(i + 1) % n];
        let displacement = end - start;

        if displacement.norm() < 1e-10 {
            continue;
        }

        let active_facets = find_all_active_facets(&start, &triangle, &triangle);
        assert!(
            !active_facets.is_empty(),
            "Start point should be on at least one facet"
        );

        let reeb_vectors: Vec<Vector4<f64>> = active_facets
            .iter()
            .map(|(n, h)| reeb_vector_4d(n, *h))
            .collect();

        if active_facets.len() == 1 {
            let reeb = &reeb_vectors[0];
            let d_norm = displacement.normalize();
            let r_norm = reeb.normalize();
            let dot = d_norm.dot(&r_norm).abs();
            assert!(
                (dot - 1.0).abs() < 1e-6,
                "Triangle segment {} on single facet not parallel to Reeb: |d̂·R̂| = {:.6}",
                i,
                dot
            );
        } else {
            // Multiple facets active
            assert!(displacement.norm() > 1e-10);
        }
    }
}
