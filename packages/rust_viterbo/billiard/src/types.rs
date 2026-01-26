//! Core data structures for the billiard algorithm.

use nalgebra::{Vector2, Vector4};
use thiserror::Error;

/// Numerical tolerance for floating point comparisons.
pub const EPS: f64 = 1e-10;

/// Tolerance for constraint satisfaction.
pub const CONSTRAINT_TOL: f64 = 1e-8;

/// Tolerance for edge parameter bounds.
pub const EDGE_PARAM_TOL: f64 = 1e-9;

/// Minimum action to consider (below this is "zero length").
pub const MIN_ACTION: f64 = 1e-8;

/// A convex polygon in R² with 0 in its interior.
/// Edges and vertices are in CCW order.
#[derive(Debug, Clone)]
pub struct Polygon2D {
    /// Vertices in CCW order. v[i] is vertex i.
    pub vertices: Vec<Vector2<f64>>,
    /// Outward unit normals. n[i] is the normal to edge i (from v[i] to v[i+1]).
    pub normals: Vec<Vector2<f64>>,
    /// Heights. h[i] = ⟨n[i], v[i]⟩ > 0 (positive since 0 is in interior).
    pub heights: Vec<f64>,
}

impl Polygon2D {
    /// Number of edges (same as number of vertices for a polygon).
    pub fn num_edges(&self) -> usize {
        self.vertices.len()
    }

    /// Number of vertices (same as number of edges for a polygon).
    pub fn num_vertices(&self) -> usize {
        self.vertices.len()
    }

    /// Get the start vertex of edge i.
    pub fn edge_start(&self, i: usize) -> Vector2<f64> {
        self.vertices[i]
    }

    /// Get the end vertex of edge i.
    pub fn edge_end(&self, i: usize) -> Vector2<f64> {
        self.vertices[(i + 1) % self.num_vertices()]
    }

    /// Point on edge i at parameter t ∈ [0, 1].
    /// t=0 gives vertex i, t=1 gives vertex i+1.
    pub fn point_on_edge(&self, i: usize, t: f64) -> Vector2<f64> {
        let v0 = self.edge_start(i);
        let v1 = self.edge_end(i);
        v0 + (v1 - v0) * t
    }

    /// Validate polygon structure.
    pub fn validate(&self) -> Result<(), BilliardError> {
        let n = self.num_vertices();
        if n < 3 {
            return Err(BilliardError::InvalidPolygon(
                "Polygon must have at least 3 vertices".to_string(),
            ));
        }

        if self.normals.len() != n || self.heights.len() != n {
            return Err(BilliardError::InvalidPolygon(
                "Normals and heights must have same length as vertices".to_string(),
            ));
        }

        // Check normals are unit vectors
        for (i, normal) in self.normals.iter().enumerate() {
            if (normal.norm() - 1.0).abs() > EPS {
                return Err(BilliardError::InvalidPolygon(format!(
                    "Normal {} is not unit: {}",
                    i,
                    normal.norm()
                )));
            }
        }

        // Check heights are positive (0 in interior)
        for (i, &h) in self.heights.iter().enumerate() {
            if h <= EPS {
                return Err(BilliardError::InvalidPolygon(format!(
                    "Height {} is not positive: {} (0 not in interior)",
                    i, h
                )));
            }
        }

        // Check CCW orientation (signed area > 0)
        let mut signed_area = 0.0;
        for i in 0..n {
            let v0 = self.vertices[i];
            let v1 = self.vertices[(i + 1) % n];
            signed_area += v0[0] * v1[1] - v1[0] * v0[1];
        }
        if signed_area <= 0.0 {
            return Err(BilliardError::InvalidPolygon(
                "Vertices are not in CCW order".to_string(),
            ));
        }

        Ok(())
    }
}

/// A Lagrangian product K = K_q × K_p in R⁴.
#[derive(Debug, Clone)]
pub struct LagrangianProduct {
    /// Factor in q-space (the "billiard table").
    pub k_q: Polygon2D,
    /// Factor in p-space (determines the "metric").
    pub k_p: Polygon2D,
}

impl LagrangianProduct {
    /// Create a new Lagrangian product, validating both factors.
    pub fn new(k_q: Polygon2D, k_p: Polygon2D) -> Result<Self, BilliardError> {
        k_q.validate()?;
        k_p.validate()?;
        Ok(Self { k_q, k_p })
    }

    /// Convert to 4D H-representation (normals and heights).
    pub fn to_hrep(&self) -> (Vec<Vector4<f64>>, Vec<f64>) {
        let mut normals = Vec::new();
        let mut heights = Vec::new();

        // q-facets: normals of form (n_q, 0)
        for i in 0..self.k_q.num_edges() {
            let n = self.k_q.normals[i];
            normals.push(Vector4::new(n[0], n[1], 0.0, 0.0));
            heights.push(self.k_q.heights[i]);
        }

        // p-facets: normals of form (0, n_p)
        for i in 0..self.k_p.num_edges() {
            let n = self.k_p.normals[i];
            normals.push(Vector4::new(0.0, 0.0, n[0], n[1]));
            heights.push(self.k_p.heights[i]);
        }

        (normals, heights)
    }
}

/// An edge selection for a k-bounce trajectory.
#[derive(Debug, Clone)]
pub struct EdgeCombination {
    /// Indices of edges in K_q (length = num_bounces).
    pub q_edges: Vec<usize>,
    /// Indices of edges in K_p (length = num_bounces).
    pub p_edges: Vec<usize>,
}

/// A k-bounce billiard trajectory.
#[derive(Debug, Clone)]
pub struct BilliardTrajectory {
    /// Number of bounces.
    pub num_bounces: usize,
    /// Bounce points in q-space (on ∂K_q).
    pub q_positions: Vec<Vector2<f64>>,
    /// Corresponding p-positions (on ∂K_p).
    pub p_positions: Vec<Vector2<f64>>,
    /// Edge parameters t ∈ [0,1] for q-positions.
    pub q_params: Vec<f64>,
    /// Edge parameters t ∈ [0,1] for p-positions.
    pub p_params: Vec<f64>,
    /// Edge indices in K_q.
    pub q_edges: Vec<usize>,
    /// Edge indices in K_p.
    pub p_edges: Vec<usize>,
    /// Total action (= T°-length = capacity).
    pub action: f64,
}

impl BilliardTrajectory {
    /// Convert to 4D breakpoints.
    pub fn to_4d_breakpoints(&self) -> Vec<Vector4<f64>> {
        self.q_positions
            .iter()
            .zip(&self.p_positions)
            .map(|(q, p)| Vector4::new(q[0], q[1], p[0], p[1]))
            .collect()
    }
}

/// Result of billiard capacity computation.
#[derive(Debug, Clone)]
pub struct BilliardResult {
    /// The computed EHZ capacity.
    pub capacity: f64,
    /// The optimal trajectory achieving the minimum.
    pub witness: BilliardTrajectory,
    /// Number of edge combinations evaluated.
    pub combinations_evaluated: usize,
}

/// Errors that can occur during billiard computation.
#[derive(Debug, Error)]
pub enum BilliardError {
    #[error("Invalid polygon: {0}")]
    InvalidPolygon(String),

    #[error("Not a Lagrangian product: {0}")]
    NotLagrangianProduct(String),

    #[error("No valid trajectory found")]
    NoValidTrajectory,

    #[error("Numerical error: {0}")]
    NumericalError(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;
    use std::f64::consts::PI;

    fn make_unit_square() -> Polygon2D {
        // Square [-1, 1]²
        Polygon2D {
            vertices: vec![
                Vector2::new(-1.0, -1.0),
                Vector2::new(1.0, -1.0),
                Vector2::new(1.0, 1.0),
                Vector2::new(-1.0, 1.0),
            ],
            normals: vec![
                Vector2::new(0.0, -1.0),
                Vector2::new(1.0, 0.0),
                Vector2::new(0.0, 1.0),
                Vector2::new(-1.0, 0.0),
            ],
            heights: vec![1.0, 1.0, 1.0, 1.0],
        }
    }

    fn make_regular_pentagon() -> Polygon2D {
        let n = 5;
        let mut vertices = Vec::with_capacity(n);
        let mut normals = Vec::with_capacity(n);
        let mut heights = Vec::with_capacity(n);

        for k in 0..n {
            let angle = 2.0 * PI * (k as f64) / (n as f64);
            vertices.push(Vector2::new(angle.cos(), angle.sin()));
        }

        for k in 0..n {
            let v0 = vertices[k];
            let v1 = vertices[(k + 1) % n];
            let edge = v1 - v0;
            // Outward normal: rotate edge 90° CW and normalize
            let normal = Vector2::new(edge[1], -edge[0]).normalize();
            let height = normal.dot(&v0);
            normals.push(normal);
            heights.push(height);
        }

        Polygon2D {
            vertices,
            normals,
            heights,
        }
    }

    #[test]
    fn test_square_validation() {
        let square = make_unit_square();
        assert!(square.validate().is_ok());
    }

    #[test]
    fn test_pentagon_validation() {
        let pentagon = make_regular_pentagon();
        assert!(pentagon.validate().is_ok());
    }

    #[test]
    fn test_point_on_edge() {
        let square = make_unit_square();

        // Edge 0: from (-1,-1) to (1,-1)
        let p0 = square.point_on_edge(0, 0.0);
        let p1 = square.point_on_edge(0, 1.0);
        let pmid = square.point_on_edge(0, 0.5);

        assert_relative_eq!(p0[0], -1.0, epsilon = EPS);
        assert_relative_eq!(p0[1], -1.0, epsilon = EPS);
        assert_relative_eq!(p1[0], 1.0, epsilon = EPS);
        assert_relative_eq!(p1[1], -1.0, epsilon = EPS);
        assert_relative_eq!(pmid[0], 0.0, epsilon = EPS);
        assert_relative_eq!(pmid[1], -1.0, epsilon = EPS);
    }

    #[test]
    fn test_lagrangian_product_hrep() {
        let square = make_unit_square();
        let product =
            LagrangianProduct::new(square.clone(), square.clone()).expect("valid product");

        let (normals, heights) = product.to_hrep();

        // Should have 8 facets (4 from q, 4 from p)
        assert_eq!(normals.len(), 8);
        assert_eq!(heights.len(), 8);

        // First 4 normals should have form (n_q, 0)
        for i in 0..4 {
            assert_relative_eq!(normals[i][2], 0.0, epsilon = EPS);
            assert_relative_eq!(normals[i][3], 0.0, epsilon = EPS);
        }

        // Last 4 normals should have form (0, n_p)
        for i in 4..8 {
            assert_relative_eq!(normals[i][0], 0.0, epsilon = EPS);
            assert_relative_eq!(normals[i][1], 0.0, epsilon = EPS);
        }
    }
}
