//! 2D convex polygon representation and operations.

use crate::tolerances::EPS;
use nalgebra::Vector2;
use std::f64::consts::PI;
use thiserror::Error;

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
    pub fn validate(&self) -> Result<(), Polygon2DError> {
        let n = self.num_vertices();
        if n < 3 {
            return Err(Polygon2DError::InvalidPolygon(
                "Polygon must have at least 3 vertices".to_string(),
            ));
        }

        if self.normals.len() != n || self.heights.len() != n {
            return Err(Polygon2DError::InvalidPolygon(
                "Normals and heights must have same length as vertices".to_string(),
            ));
        }

        // Check normals are unit vectors
        for (i, normal) in self.normals.iter().enumerate() {
            if (normal.norm() - 1.0).abs() > EPS {
                return Err(Polygon2DError::InvalidPolygon(format!(
                    "Normal {} is not unit: {}",
                    i,
                    normal.norm()
                )));
            }
        }

        // Check heights are positive (0 in interior)
        for (i, &h) in self.heights.iter().enumerate() {
            if h <= EPS {
                return Err(Polygon2DError::InvalidPolygon(format!(
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
            return Err(Polygon2DError::InvalidPolygon(
                "Vertices are not in CCW order".to_string(),
            ));
        }

        Ok(())
    }

    /// Create a polygon from vertices in CCW order.
    /// Computes normals and heights automatically.
    pub fn from_vertices(vertices: Vec<Vector2<f64>>) -> Result<Self, Polygon2DError> {
        let n = vertices.len();
        if n < 3 {
            return Err(Polygon2DError::InvalidPolygon(
                "Need at least 3 vertices".to_string(),
            ));
        }

        let mut normals = Vec::with_capacity(n);
        let mut heights = Vec::with_capacity(n);

        for i in 0..n {
            let v0 = vertices[i];
            let v1 = vertices[(i + 1) % n];
            let edge = v1 - v0;

            // Outward normal: rotate edge 90° CW (for CCW vertices)
            let normal_unnorm = Vector2::new(edge[1], -edge[0]);
            let len = normal_unnorm.norm();
            if len < EPS {
                return Err(Polygon2DError::InvalidPolygon(format!(
                    "Edge {} has zero length",
                    i
                )));
            }
            let normal = normal_unnorm / len;
            let height = normal.dot(&v0);

            if height <= EPS {
                return Err(Polygon2DError::InvalidPolygon(format!(
                    "Origin not in interior: height {} = {}",
                    i, height
                )));
            }

            normals.push(normal);
            heights.push(height);
        }

        let polygon = Polygon2D {
            vertices,
            normals,
            heights,
        };
        polygon.validate()?;
        Ok(polygon)
    }

    /// Create a regular n-gon with given circumradius, centered at origin.
    /// First vertex is at angle `start_angle` from positive x-axis.
    pub fn regular(n: usize, circumradius: f64, start_angle: f64) -> Result<Self, Polygon2DError> {
        if n < 3 {
            return Err(Polygon2DError::InvalidPolygon(
                "Regular polygon needs at least 3 sides".to_string(),
            ));
        }
        if circumradius <= 0.0 {
            return Err(Polygon2DError::InvalidPolygon(
                "Circumradius must be positive".to_string(),
            ));
        }

        let vertices: Vec<Vector2<f64>> = (0..n)
            .map(|k| {
                let angle = start_angle + 2.0 * PI * (k as f64) / (n as f64);
                Vector2::new(circumradius * angle.cos(), circumradius * angle.sin())
            })
            .collect();

        Self::from_vertices(vertices)
    }

    /// Create a regular pentagon with circumradius 1, first vertex at (1, 0).
    pub fn regular_pentagon() -> Self {
        Self::regular(5, 1.0, 0.0).expect("regular pentagon is always valid")
    }

    /// Create a square [-s/2, s/2]² (side length s, centered at origin).
    pub fn square(side_length: f64) -> Result<Self, Polygon2DError> {
        if side_length <= 0.0 {
            return Err(Polygon2DError::InvalidPolygon(
                "Side length must be positive".to_string(),
            ));
        }
        let s = side_length / 2.0;
        Self::from_vertices(vec![
            Vector2::new(-s, -s),
            Vector2::new(s, -s),
            Vector2::new(s, s),
            Vector2::new(-s, s),
        ])
    }

    /// Rotate the polygon by angle (radians) CCW around the origin.
    pub fn rotate(&self, angle: f64) -> Self {
        let cos_a = angle.cos();
        let sin_a = angle.sin();

        let rotate_vec = |v: &Vector2<f64>| -> Vector2<f64> {
            Vector2::new(cos_a * v[0] - sin_a * v[1], sin_a * v[0] + cos_a * v[1])
        };

        Polygon2D {
            vertices: self.vertices.iter().map(rotate_vec).collect(),
            normals: self.normals.iter().map(rotate_vec).collect(),
            heights: self.heights.clone(), // Heights unchanged by rotation around origin
        }
    }

    /// Scale the polygon by factor lambda (from origin).
    pub fn scale(&self, lambda: f64) -> Self {
        Polygon2D {
            vertices: self.vertices.iter().map(|v| v * lambda).collect(),
            normals: self.normals.clone(), // Normals unchanged by scaling
            heights: self.heights.iter().map(|h| h * lambda).collect(),
        }
    }
}

/// Compute the support function h_K(v) = max_{x ∈ K} ⟨v, x⟩.
/// For a polygon, this is the max over vertices.
pub fn support_function(v: &Vector2<f64>, polygon: &Polygon2D) -> f64 {
    polygon
        .vertices
        .iter()
        .map(|w| v.dot(w))
        .fold(f64::NEG_INFINITY, f64::max)
}

/// Compute the T°-length of a vector: ||v||_{T°} = h_T(v).
/// This equals max_{x ∈ T} ⟨v, x⟩.
pub fn t_dual_length(v: &Vector2<f64>, t: &Polygon2D) -> f64 {
    support_function(v, t)
}

/// Errors that can occur during polygon operations.
#[derive(Debug, Error)]
pub enum Polygon2DError {
    #[error("Invalid polygon: {0}")]
    InvalidPolygon(String),
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;

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
    fn test_regular_pentagon() {
        let pentagon = Polygon2D::regular_pentagon();
        assert_eq!(pentagon.num_vertices(), 5);

        // First vertex should be at (1, 0)
        assert_relative_eq!(pentagon.vertices[0][0], 1.0, epsilon = EPS);
        assert_relative_eq!(pentagon.vertices[0][1], 0.0, epsilon = EPS);
    }

    #[test]
    fn test_square() {
        let square = Polygon2D::square(2.0).unwrap();
        assert_eq!(square.num_vertices(), 4);

        // All heights should be 1.0 for [-1,1]²
        for &h in &square.heights {
            assert_relative_eq!(h, 1.0, epsilon = EPS);
        }
    }

    #[test]
    fn test_rotate_pentagon() {
        let pentagon = Polygon2D::regular_pentagon();
        let rotated = pentagon.rotate(PI / 2.0);

        // First vertex should now be at (0, 1)
        assert_relative_eq!(rotated.vertices[0][0], 0.0, epsilon = 1e-9);
        assert_relative_eq!(rotated.vertices[0][1], 1.0, epsilon = 1e-9);

        // Should still be valid
        assert!(rotated.validate().is_ok());
    }

    #[test]
    fn test_support_function_square() {
        let square = Polygon2D::square(2.0).unwrap();

        // Support in direction (1, 0) should be 1.0
        let h = support_function(&Vector2::new(1.0, 0.0), &square);
        assert_relative_eq!(h, 1.0, epsilon = EPS);

        // Support in direction (1, 1) should be 2.0 (corner at (1,1))
        let h = support_function(&Vector2::new(1.0, 1.0), &square);
        assert_relative_eq!(h, 2.0, epsilon = EPS);
    }

    #[test]
    fn test_t_dual_length() {
        let square = Polygon2D::square(2.0).unwrap();

        // For a square centered at origin with half-width 1,
        // ||v||_{square°} = max(|v_x|, |v_y|) for the dual norm.
        // But T°-length uses the primal: max_{x ∈ T} ⟨v, x⟩
        // For v = (2, 0), T°-length = 2*1 = 2
        let len = t_dual_length(&Vector2::new(2.0, 0.0), &square);
        assert_relative_eq!(len, 2.0, epsilon = EPS);
    }
}
