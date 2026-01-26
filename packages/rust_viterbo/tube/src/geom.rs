//! 4D geometric utilities.
//!
//! This module provides:
//! - Action computation for closed polygonal curves
//! - Boundary/interior point tests
//! - Utility functions for 4D geometry

use nalgebra::Vector4;

use crate::consts::EPS;
use crate::symplectic::symplectic_form;

/// Compute the action of a closed polygonal curve.
///
/// For vertices v₀, v₁, ..., v_{n-1} (with v_n = v₀ implicit):
/// A = (1/2) Σ ω(vₖ, v_{k+1})
pub fn action_of_closed_polygon(vertices: &[Vector4<f64>]) -> f64 {
    if vertices.len() < 2 {
        return 0.0;
    }

    let n = vertices.len();
    let mut sum = 0.0;
    for k in 0..n {
        let next = (k + 1) % n;
        sum += symplectic_form(&vertices[k], &vertices[next]);
    }
    0.5 * sum
}

/// Check if a point is on the boundary of a polytope (on at least one facet).
pub fn is_on_boundary(
    p: &Vector4<f64>,
    normals: &[Vector4<f64>],
    heights: &[f64],
) -> bool {
    let on_some_facet = normals
        .iter()
        .zip(heights)
        .any(|(n, &h)| (n.dot(p) - h).abs() < EPS);

    let inside_all = normals
        .iter()
        .zip(heights)
        .all(|(n, &h)| n.dot(p) <= h + EPS);

    on_some_facet && inside_all
}

/// Get indices of active facets (facets that p lies on).
pub fn active_facets(
    p: &Vector4<f64>,
    normals: &[Vector4<f64>],
    heights: &[f64],
) -> Vec<usize> {
    normals
        .iter()
        .zip(heights)
        .enumerate()
        .filter(|(_, (n, &h))| (n.dot(p) - h).abs() < EPS)
        .map(|(i, _)| i)
        .collect()
}

/// Check if a point is strictly inside the polytope.
pub fn is_strictly_inside(
    p: &Vector4<f64>,
    normals: &[Vector4<f64>],
    heights: &[f64],
) -> bool {
    normals
        .iter()
        .zip(heights)
        .all(|(n, &h)| n.dot(p) < h - EPS)
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

    #[test]
    fn test_action_square_q_plane() {
        // Square in q-plane: (0,0,0,0) → (1,0,0,0) → (1,1,0,0) → (0,1,0,0)
        let vertices = vec![
            Vector4::new(0.0, 0.0, 0.0, 0.0),
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(1.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
        ];

        let action = action_of_closed_polygon(&vertices);
        // In q-plane, ω = 0 (Lagrangian), so action should be 0
        assert_relative_eq!(action, 0.0, epsilon = 1e-14);
    }

    #[test]
    fn test_action_symplectic_square() {
        // Square in (q₁, p₁) plane: area 1, action = area
        let vertices = vec![
            Vector4::new(0.0, 0.0, 0.0, 0.0),
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(1.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
        ];

        let action = action_of_closed_polygon(&vertices);
        // In (q₁, p₁) plane with CCW orientation, action = 1
        assert_relative_eq!(action, 1.0, epsilon = 1e-14);
    }

    #[test]
    fn test_action_reversed_orientation() {
        // Square in (q₁, p₁) plane, reversed (CW)
        let vertices = vec![
            Vector4::new(0.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(1.0, 0.0, 1.0, 0.0),
            Vector4::new(1.0, 0.0, 0.0, 0.0),
        ];

        let action = action_of_closed_polygon(&vertices);
        // Reversed orientation gives negative action
        assert_relative_eq!(action, -1.0, epsilon = 1e-14);
    }

    #[test]
    fn test_is_on_boundary() {
        // Unit cube in first 4 coordinates: [-1,1]^2 in (q₁, q₂)
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
        ];
        let heights = vec![1.0, 1.0, 1.0, 1.0];

        // Point on boundary
        let p_boundary = Vector4::new(1.0, 0.0, 0.0, 0.0);
        assert!(is_on_boundary(&p_boundary, &normals, &heights));

        // Point strictly inside
        let p_inside = Vector4::new(0.0, 0.0, 0.0, 0.0);
        assert!(!is_on_boundary(&p_inside, &normals, &heights));

        // Point outside
        let p_outside = Vector4::new(2.0, 0.0, 0.0, 0.0);
        assert!(!is_on_boundary(&p_outside, &normals, &heights));
    }

    #[test]
    fn test_active_facets() {
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
        ];
        let heights = vec![1.0, 1.0, 1.0, 1.0];

        // Corner point: active on facets 0 and 1
        let corner = Vector4::new(1.0, 1.0, 0.0, 0.0);
        let active = active_facets(&corner, &normals, &heights);
        assert!(active.contains(&0));
        assert!(active.contains(&1));
        assert_eq!(active.len(), 2);
    }
}
