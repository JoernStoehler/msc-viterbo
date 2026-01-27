//! Preprocessing for the HK2017 algorithm.
//!
//! Computes and validates precomputed facet data before the main algorithm runs.

use nalgebra::DMatrix;

use crate::symplectic::{reeb_vector, symplectic_form};
use crate::types::{validate_for_hk2017, FacetData, Hk2017Error, PolytopeHRep, EPS};

impl FacetData {
    /// Precompute facet data from a polytope.
    ///
    /// This computes:
    /// - Reeb vectors p_i = (2/h_i) * J * n_i
    /// - Symplectic form matrix omega[(i,j)] = omega(n_i, n_j)
    ///
    /// # Errors
    ///
    /// Returns an error if the polytope is invalid (see `validate_for_hk2017`).
    pub fn from_polytope(polytope: &PolytopeHRep) -> Result<Self, Hk2017Error> {
        validate_for_hk2017(polytope)?;

        let f = polytope.num_facets();
        let normals = polytope.normals.clone();
        let heights = polytope.heights.clone();

        // Compute Reeb vectors
        let reeb_vectors: Vec<_> = (0..f)
            .map(|i| reeb_vector(&normals[i], heights[i]))
            .collect();

        // Precompute symplectic form matrix
        let mut omega_matrix = DMatrix::zeros(f, f);
        for i in 0..f {
            for j in 0..f {
                omega_matrix[(i, j)] = symplectic_form(&normals[i], &normals[j]);
            }
        }

        let data = FacetData {
            num_facets: f,
            normals,
            heights,
            reeb_vectors,
            omega_matrix,
        };

        // Validate the computed data in debug builds
        if cfg!(debug_assertions) {
            data.validate();
        }

        Ok(data)
    }

    /// Validate the internal consistency of precomputed data.
    ///
    /// Checks:
    /// - Reeb vectors are perpendicular to normals
    /// - Omega matrix is antisymmetric
    /// - Diagonal of omega is zero
    ///
    /// Panics on validation failure in debug builds.
    pub fn validate(&self) {
        // Check Reeb vectors are perpendicular to normals
        // Jn is perpendicular to n because <Jn, n> = omega(n, n) = 0
        for i in 0..self.num_facets {
            let dot = self.reeb_vectors[i].dot(&self.normals[i]);
            debug_assert!(
                dot.abs() < EPS,
                "Reeb vector {} not perpendicular to normal: dot = {}",
                i,
                dot
            );
        }

        // Check omega matrix is antisymmetric
        for i in 0..self.num_facets {
            for j in 0..self.num_facets {
                let sum = self.omega_matrix[(i, j)] + self.omega_matrix[(j, i)];
                debug_assert!(
                    sum.abs() < EPS,
                    "Omega matrix not antisymmetric at ({}, {}): sum = {}",
                    i,
                    j,
                    sum
                );
            }
        }

        // Check diagonal is zero
        for i in 0..self.num_facets {
            debug_assert!(
                self.omega_matrix[(i, i)].abs() < EPS,
                "Omega diagonal not zero at {}: value = {}",
                i,
                self.omega_matrix[(i, i)]
            );
        }
    }

    /// Check if two facets form a Lagrangian pair (omega = 0).
    ///
    /// Returns `true` if |omega(n_i, n_j)| < LAGRANGIAN_TOL.
    #[inline]
    pub fn is_lagrangian_pair(&self, i: usize, j: usize) -> bool {
        self.omega_matrix[(i, j)].abs() < crate::types::LAGRANGIAN_TOL
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use approx::assert_relative_eq;
    use nalgebra::Vector4;

    fn make_tesseract() -> PolytopeHRep {
        // Tesseract [-1, 1]^4 has 8 facets with normals +/- e_i
        let normals = vec![
            Vector4::new(1.0, 0.0, 0.0, 0.0),
            Vector4::new(-1.0, 0.0, 0.0, 0.0),
            Vector4::new(0.0, 1.0, 0.0, 0.0),
            Vector4::new(0.0, -1.0, 0.0, 0.0),
            Vector4::new(0.0, 0.0, 1.0, 0.0),
            Vector4::new(0.0, 0.0, -1.0, 0.0),
            Vector4::new(0.0, 0.0, 0.0, 1.0),
            Vector4::new(0.0, 0.0, 0.0, -1.0),
        ];
        let heights = vec![1.0; 8];
        PolytopeHRep::new(normals, heights)
    }

    #[test]
    fn test_facet_data_from_tesseract() {
        let polytope = make_tesseract();
        let data = FacetData::from_polytope(&polytope).unwrap();

        assert_eq!(data.num_facets, 8);
        assert_eq!(data.normals.len(), 8);
        assert_eq!(data.heights.len(), 8);
        assert_eq!(data.reeb_vectors.len(), 8);
        assert_eq!(data.omega_matrix.nrows(), 8);
        assert_eq!(data.omega_matrix.ncols(), 8);
    }

    #[test]
    fn test_omega_matrix_antisymmetric() {
        let polytope = make_tesseract();
        let data = FacetData::from_polytope(&polytope).unwrap();

        for i in 0..data.num_facets {
            for j in 0..data.num_facets {
                assert_relative_eq!(
                    data.omega_matrix[(i, j)],
                    -data.omega_matrix[(j, i)],
                    epsilon = EPS
                );
            }
        }
    }

    #[test]
    fn test_omega_diagonal_zero() {
        let polytope = make_tesseract();
        let data = FacetData::from_polytope(&polytope).unwrap();

        for i in 0..data.num_facets {
            assert_relative_eq!(data.omega_matrix[(i, i)], 0.0, epsilon = EPS);
        }
    }

    #[test]
    fn test_reeb_vectors_perpendicular() {
        let polytope = make_tesseract();
        let data = FacetData::from_polytope(&polytope).unwrap();

        for i in 0..data.num_facets {
            let dot = data.reeb_vectors[i].dot(&data.normals[i]);
            assert_relative_eq!(dot, 0.0, epsilon = EPS);
        }
    }

    #[test]
    fn test_tesseract_lagrangian_pairs() {
        // In the tesseract, facets with normals in the q-plane (e1, e2) are
        // Lagrangian with respect to facets in the p-plane (e3, e4)
        let polytope = make_tesseract();
        let data = FacetData::from_polytope(&polytope).unwrap();

        // Facets 0,1 have normals +/- e1 (q1 direction)
        // Facets 2,3 have normals +/- e2 (q2 direction)
        // Facets 4,5 have normals +/- e3 (p1 direction)
        // Facets 6,7 have normals +/- e4 (p2 direction)

        // q-q pairs are Lagrangian
        assert!(data.is_lagrangian_pair(0, 2)); // e1 vs e2
        assert!(data.is_lagrangian_pair(0, 3)); // e1 vs -e2

        // p-p pairs are Lagrangian
        assert!(data.is_lagrangian_pair(4, 6)); // e3 vs e4
        assert!(data.is_lagrangian_pair(5, 7)); // -e3 vs -e4

        // q-p pairs are NOT Lagrangian (omega = +/- 1)
        assert!(!data.is_lagrangian_pair(0, 4)); // e1 vs e3: omega = 1
        assert!(!data.is_lagrangian_pair(2, 6)); // e2 vs e4: omega = 1
    }
}
