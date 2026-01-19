//! Preprocessed polytope data for the tube algorithm.
//!
//! This module computes and caches geometric data about non-Lagrangian 2-faces
//! that is reused throughout the branch-and-bound search.
//!
//! Key insight: Only non-Lagrangian 2-faces can be crossed by Reeb orbits.
//! See thesis §4.2 for the Reeb dynamics on polytope boundaries.

use crate::polygon::Polygon2D;
use rust_viterbo_geom::{
    symplectic_form, trivialization, two_face_rotation, PolytopeHRep, SymplecticVector, Vector2f,
};

/// Tolerance for feasibility checks on vertices
pub const EPS_FEAS: f64 = 1e-10;
/// Tolerance for deduplication of vertices
pub const EPS_DEDUP: f64 = 1e-8;
/// Tolerance for Lagrangian detection
pub const EPS_LAGR: f64 = 1e-9;

/// Flow direction across a 2-face.
///
/// Determined by the sign of ω(nᵢ, nⱼ) where nᵢ, nⱼ are the facet normals.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FlowDir {
    /// Flow crosses from Eᵢ into Eⱼ (ω(nᵢ, nⱼ) > 0)
    ItoJ,
    /// Flow crosses from Eⱼ into Eᵢ (ω(nᵢ, nⱼ) < 0)
    JtoI,
}

/// Data for a single non-Lagrangian 2-face.
///
/// Precomputes everything needed to compute flow maps across this face.
#[derive(Clone, Debug)]
pub struct TwoFaceData {
    /// First facet index (always i < j)
    pub i: usize,
    /// Second facet index
    pub j: usize,
    /// Which way does the Reeb flow cross?
    pub flow_direction: FlowDir,
    /// Rotation increment ρ(F) ∈ (0, 0.5) in turns
    pub rotation: f64,
    /// Polygon vertices in 2D (trivialization coordinates, relative to centroid)
    pub polygon: Polygon2D,
    /// Reference point (centroid) in 4D
    pub centroid: SymplecticVector,
    /// Entry normal (normal of facet that flow is entering)
    pub entry_normal: SymplecticVector,
    /// Original 4D vertices for witness reconstruction
    pub vertices_4d: Vec<SymplecticVector>,
}

/// Precomputed data for the entire polytope.
///
/// Caches all non-Lagrangian 2-faces with their geometric data.
#[derive(Clone, Debug)]
pub struct PolytopeData {
    pub hrep: PolytopeHRep,
    /// Non-Lagrangian 2-faces, indexed by (i, j) pair
    pub two_faces: Vec<TwoFaceData>,
}

impl PolytopeData {
    /// Precompute all 2-face data for the polytope.
    pub fn new(hrep: PolytopeHRep) -> Self {
        let raw_faces = hrep.two_faces(EPS_FEAS, EPS_DEDUP);
        let mut two_faces = Vec::new();

        for face in raw_faces {
            let ni = hrep.normals[face.i];
            let nj = hrep.normals[face.j];

            let omega = symplectic_form(ni, nj);
            if omega.abs() < EPS_LAGR {
                continue; // Skip Lagrangian faces
            }

            let flow_direction = if omega > 0.0 {
                FlowDir::ItoJ
            } else {
                FlowDir::JtoI
            };

            // Compute rotation using exit/entry normals based on flow direction
            let (exit_normal, entry_normal) = match flow_direction {
                FlowDir::ItoJ => (ni, nj),
                FlowDir::JtoI => (nj, ni),
            };

            let rotation = match two_face_rotation(exit_normal, entry_normal) {
                Some(r) => r,
                None => continue,
            };

            // Compute centroid of 4D vertices
            let n_verts = face.vertices.len() as f64;
            let centroid = face
                .vertices
                .iter()
                .fold(SymplecticVector::zeros(), |acc, v| acc + v)
                / n_verts;

            // Convert vertices to 2D using trivialization, relative to centroid
            let polygon_vertices: Vec<Vector2f> = face
                .vertices
                .iter()
                .map(|v| trivialization(*v - centroid, entry_normal))
                .collect();

            two_faces.push(TwoFaceData {
                i: face.i,
                j: face.j,
                flow_direction,
                rotation,
                polygon: Polygon2D::new(polygon_vertices),
                centroid,
                entry_normal,
                vertices_4d: face.vertices,
            });
        }

        Self { hrep, two_faces }
    }

    /// Get a 2-face by facet indices.
    pub fn get_two_face(&self, i: usize, j: usize) -> Option<&TwoFaceData> {
        let (i, j) = if i < j { (i, j) } else { (j, i) };
        self.two_faces.iter().find(|f| f.i == i && f.j == j)
    }

    /// Get all 2-faces adjacent to a given facet.
    pub fn faces_adjacent_to(&self, facet: usize) -> Vec<&TwoFaceData> {
        self.two_faces
            .iter()
            .filter(|f| f.i == facet || f.j == facet)
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use rust_viterbo_geom::{PolytopeHRep, SymplecticVector};

    /// Standard tesseract B^2 × B^2 (unit 4-cube).
    fn tesseract() -> PolytopeHRep {
        let normals = vec![
            SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(-1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
            SymplecticVector::new(0.0, -1.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
            SymplecticVector::new(0.0, 0.0, -1.0, 0.0),
            SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
            SymplecticVector::new(0.0, 0.0, 0.0, -1.0),
        ];
        PolytopeHRep::new(normals, vec![1.0; 8])
    }

    /// Test that get_two_face retrieves face by indices (order-independent).
    #[test]
    fn get_two_face_order_independent() {
        let data = PolytopeData::new(tesseract());
        assert!(!data.two_faces.is_empty(), "tesseract should have non-Lagrangian faces");

        let first = &data.two_faces[0];
        let by_ij = data.get_two_face(first.i, first.j);
        let by_ji = data.get_two_face(first.j, first.i);

        assert!(by_ij.is_some());
        assert!(by_ji.is_some());
        assert_eq!(by_ij.unwrap().i, by_ji.unwrap().i);
    }

    /// Test that faces_adjacent_to finds all faces containing a given facet.
    #[test]
    fn faces_adjacent_to_includes_facet() {
        let data = PolytopeData::new(tesseract());

        // Find a facet that appears in some 2-face
        if let Some(face) = data.two_faces.first() {
            let adjacent = data.faces_adjacent_to(face.i);
            assert!(
                adjacent.iter().any(|f| f.i == face.i || f.j == face.i),
                "faces_adjacent_to should include the face containing facet {}", face.i
            );
        }
    }

    /// Test that Lagrangian 2-faces are filtered out.
    ///
    /// The tesseract B^2 × B^2 has 28 raw 2-faces but only 8 non-Lagrangian ones
    /// (the faces where q-facets meet p-facets).
    #[test]
    fn lagrangian_detection_uses_adjacent_faces() {
        let data = PolytopeData::new(tesseract());
        // Tesseract = B^2 × B^2 has 8 facets (4 q-facets + 4 p-facets)
        // Non-Lagrangian faces: q-facet meets p-facet = 4×4 = 16 pairs / 2 (symmetry) = 8
        // But rotation filter removes some, so we expect roughly 8
        assert_eq!(data.two_faces.len(), 8,
            "tesseract should have exactly 8 non-Lagrangian 2-faces");
    }

    /// Test that rotation values are in valid range (0, 0.5).
    #[test]
    fn two_faces_for_tesseract() {
        let data = PolytopeData::new(tesseract());
        for face in &data.two_faces {
            assert!(face.rotation > 0.0 && face.rotation < 0.5,
                "rotation should be in (0, 0.5), got {}", face.rotation);
        }
    }
}
