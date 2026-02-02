//! Cross-check algorithm for boundedness: vertex enumeration.
//!
//! Independent algorithm to verify LP-based `is_bounded`. See bounded.rs for proof.

use super::{cross_polytope_normals, simplex_like_normals, tesseract_normals};
use crate::bounded::is_bounded;
use crate::tolerances::EPS;
use minilp::{ComparisonOp, OptimizationDirection, Problem};
use nalgebra::{Matrix4, Vector4};

/// Vertex enumeration cross-check. Returns true IFF bounded AND non-redundant.
fn is_bounded_via_vertex_enumeration(normals: &[Vector4<f64>], heights: &[f64]) -> bool {
    // Step 1: Check for duplicate halfspaces
    for i in 0..normals.len() {
        for j in (i + 1)..normals.len() {
            if are_equivalent_halfspaces(&normals[i], heights[i], &normals[j], heights[j]) {
                return false;
            }
        }
    }

    // Steps 2-4: Compute vertex set V
    let vertices = compute_vertices(normals, heights);

    // Steps 5-6: For each halfspace, check if W = H ∩ V spans dimension 3
    for (n, &h) in normals.iter().zip(heights.iter()) {
        let w: Vec<_> = vertices
            .iter()
            .filter(|v| (n.dot(v) - h).abs() < EPS)
            .copied()
            .collect();

        if !spans_dimension_3(&w) {
            return false;
        }
    }

    true
}

fn are_equivalent_halfspaces(n1: &Vector4<f64>, h1: f64, n2: &Vector4<f64>, h2: f64) -> bool {
    (n1 - n2).norm() < EPS && (h1 - h2).abs() < EPS
}

fn spans_dimension_3(w: &[Vector4<f64>]) -> bool {
    if w.len() < 4 {
        return false;
    }

    let origin = w[0];
    let diffs: Vec<Vector4<f64>> = w[1..].iter().map(|p| p - origin).collect();

    let mat = nalgebra::DMatrix::from_columns(
        &diffs
            .iter()
            .map(|d| nalgebra::DVector::from_column_slice(d.as_slice()))
            .collect::<Vec<_>>(),
    );

    let svd = mat.svd(false, false);
    let rank = svd.singular_values.iter().filter(|&&s| s > EPS).count();

    rank >= 3
}

fn compute_vertices(normals: &[Vector4<f64>], heights: &[f64]) -> Vec<Vector4<f64>> {
    let n = normals.len();
    let mut vertices = Vec::new();

    for i in 0..n {
        for j in (i + 1)..n {
            for k in (j + 1)..n {
                for l in (k + 1)..n {
                    let mat = Matrix4::from_rows(&[
                        normals[i].transpose(),
                        normals[j].transpose(),
                        normals[k].transpose(),
                        normals[l].transpose(),
                    ]);

                    if let Some(inv) = mat.try_inverse() {
                        let rhs = Vector4::new(heights[i], heights[j], heights[k], heights[l]);
                        let x = inv * rhs;

                        let valid = normals
                            .iter()
                            .zip(heights.iter())
                            .all(|(n, &h)| n.dot(&x) <= h + EPS);

                        if valid {
                            vertices.push(x);
                        }
                    }
                }
            }
        }
    }

    deduplicate_vertices(&mut vertices);
    vertices
}

fn deduplicate_vertices(vertices: &mut Vec<Vector4<f64>>) {
    let mut i = 0;
    while i < vertices.len() {
        let mut j = i + 1;
        while j < vertices.len() {
            if (vertices[i] - vertices[j]).norm() < EPS {
                vertices.swap_remove(j);
            } else {
                j += 1;
            }
        }
        i += 1;
    }
}

// ==================== CROSS-CHECK TESTS ====================

#[test]
fn test_cross_check_tesseract() {
    let normals = tesseract_normals();
    let heights = vec![1.0; 8];

    let lp_result = is_bounded(&normals);
    let vertex_result = is_bounded_via_vertex_enumeration(&normals, &heights);

    assert!(lp_result, "LP: tesseract should be bounded");
    assert!(vertex_result, "Vertex enum: tesseract should be bounded");
    assert_eq!(lp_result, vertex_result, "algorithms must agree");

    let vertices = compute_vertices(&normals, &heights);
    assert_eq!(vertices.len(), 16, "tesseract should have 16 vertices");
}

#[test]
fn test_cross_check_cross_polytope() {
    let normals = cross_polytope_normals();
    let heights = vec![1.0; 16];

    let lp_result = is_bounded(&normals);
    let vertex_result = is_bounded_via_vertex_enumeration(&normals, &heights);

    assert!(lp_result, "LP: cross-polytope should be bounded");
    assert!(vertex_result, "Vertex enum: cross-polytope should be bounded");
    assert_eq!(lp_result, vertex_result, "algorithms must agree");

    let vertices = compute_vertices(&normals, &heights);
    assert_eq!(vertices.len(), 8, "cross-polytope should have 8 vertices");
}

#[test]
fn test_cross_check_simplex() {
    let normals = simplex_like_normals();
    let heights = vec![1.0; 5];

    let lp_result = is_bounded(&normals);
    let vertex_result = is_bounded_via_vertex_enumeration(&normals, &heights);

    assert!(lp_result, "LP: simplex should be bounded");
    assert!(vertex_result, "Vertex enum: simplex should be bounded");
    assert_eq!(lp_result, vertex_result, "algorithms must agree");

    let vertices = compute_vertices(&normals, &heights);
    assert_eq!(vertices.len(), 5, "4-simplex should have 5 vertices");
}

#[test]
fn test_cross_check_unbounded_with_vertices() {
    let normals = vec![
        Vector4::new(-1.0, 0.0, 0.0, 0.0),
        Vector4::new(0.0, 1.0, 0.0, 0.0),
        Vector4::new(0.0, -1.0, 0.0, 0.0),
        Vector4::new(0.0, 0.0, 1.0, 0.0),
        Vector4::new(0.0, 0.0, -1.0, 0.0),
        Vector4::new(0.0, 0.0, 0.0, 1.0),
        Vector4::new(0.0, 0.0, 0.0, -1.0),
    ];
    let heights = vec![1.0; 7];

    let lp_result = is_bounded(&normals);
    let vertex_result = is_bounded_via_vertex_enumeration(&normals, &heights);

    assert!(!lp_result, "LP: missing facet → unbounded");
    assert!(!vertex_result, "Vertex enum: missing facet → unbounded");
    assert_eq!(lp_result, vertex_result, "algorithms must agree");

    let vertices = compute_vertices(&normals, &heights);
    assert_eq!(vertices.len(), 8, "8 vertices at x₁ = -1");
}

#[test]
fn test_cross_check_counterexample() {
    let normals = vec![
        Vector4::new(1.0, -1.0, -1.0, -1.0).normalize(),
        Vector4::new(-1.0, 1.0, -1.0, -1.0).normalize(),
        Vector4::new(-1.0, -1.0, 1.0, -1.0).normalize(),
        Vector4::new(-1.0, -1.0, -1.0, 1.0).normalize(),
        Vector4::new(-1.0, -1.0, -1.0, -1.0).normalize(),
    ];
    let heights = vec![1.0; 5];

    let lp_result = is_bounded(&normals);
    let vertex_result = is_bounded_via_vertex_enumeration(&normals, &heights);

    assert!(!lp_result, "LP: counterexample is unbounded");
    assert!(!vertex_result, "Vertex enum: counterexample is unbounded");
    assert_eq!(lp_result, vertex_result, "algorithms must agree");
}

// ==================== VERTEX EXTREMALITY TESTS ====================

#[test]
fn test_vertices_are_extreme_tesseract() {
    let normals = tesseract_normals();
    let heights = vec![1.0; 8];
    let vertices = compute_vertices(&normals, &heights);

    for (i, v) in vertices.iter().enumerate() {
        let others: Vec<_> = vertices
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != i)
            .map(|(_, u)| u)
            .collect();
        assert!(
            !is_convex_combination(v, &others),
            "vertex {} should not be a convex combination of others",
            i
        );
    }
}

#[test]
fn test_vertices_are_extreme_cross_polytope() {
    let normals = cross_polytope_normals();
    let heights = vec![1.0; 16];
    let vertices = compute_vertices(&normals, &heights);

    for (i, v) in vertices.iter().enumerate() {
        let others: Vec<_> = vertices
            .iter()
            .enumerate()
            .filter(|(j, _)| *j != i)
            .map(|(_, u)| u)
            .collect();
        assert!(
            !is_convex_combination(v, &others),
            "vertex {} should not be a convex combination of others",
            i
        );
    }
}

fn is_convex_combination(v: &Vector4<f64>, others: &[&Vector4<f64>]) -> bool {
    if others.is_empty() {
        return false;
    }

    let mut problem = Problem::new(OptimizationDirection::Minimize);

    let lambdas: Vec<_> = others
        .iter()
        .map(|_| problem.add_var(0.0, (0.0, 1.0)))
        .collect();

    let sum_constraint: Vec<_> = lambdas.iter().map(|&l| (l, 1.0)).collect();
    problem.add_constraint(sum_constraint.clone(), ComparisonOp::Ge, 1.0);
    problem.add_constraint(sum_constraint, ComparisonOp::Le, 1.0);

    for j in 0..4 {
        let coord_constraint: Vec<_> = lambdas
            .iter()
            .zip(others.iter())
            .map(|(&l, &u)| (l, u[j]))
            .collect();
        problem.add_constraint(coord_constraint.clone(), ComparisonOp::Ge, v[j] - EPS);
        problem.add_constraint(coord_constraint, ComparisonOp::Le, v[j] + EPS);
    }

    problem.solve().is_ok()
}
