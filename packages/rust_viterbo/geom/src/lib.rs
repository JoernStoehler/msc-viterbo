//! Core symplectic geometry structures and operations for the Viterbo project.
//!
//! Conventions are locked to \(\mathbb{R}^4\) with coordinates (q1,q2,p1,p2).

use nalgebra::Vector4;
use rand::{Rng, SeedableRng};
use rand_chacha::ChaCha8Rng;

/// Symplectic vector in \(\mathbb{R}^4\) with coordinates (q1,q2,p1,p2).
pub type SymplecticVector = Vector4<f64>;

/// Apply the almost complex structure J(q,p)=(-p,q).
pub fn j_map(x: SymplecticVector) -> SymplecticVector {
    SymplecticVector::new(-x.z, -x.w, x.x, x.y)
}

/// Standard symplectic form omega(x,y) = <Jx, y>.
pub fn symplectic_form(x: SymplecticVector, y: SymplecticVector) -> f64 {
    j_map(x).dot(&y)
}

/// Irredundant H-representation of a convex polytope in \(\mathbb{R}^4\).
#[derive(Debug, Clone)]
pub struct Polytope4HRep {
    pub normals: Vec<SymplecticVector>,
    pub heights: Vec<f64>,
}

impl Polytope4HRep {
    pub fn new(normals: Vec<SymplecticVector>, heights: Vec<f64>) -> Self {
        Self { normals, heights }
    }

    /// Validate lengths, finiteness, positive heights, and unit normals.
    pub fn validate(&self, unit_tol: f64) -> Result<(), PolytopeHRepErrors> {
        validate_hrep(&self.normals, &self.heights, unit_tol)
    }

    /// Detect whether any pair of normals is near-Lagrangian.
    pub fn has_near_lagrangian_pair(&self, eps_lagr: f64) -> bool {
        has_near_lagrangian_pair(&self.normals, eps_lagr)
    }
}

#[derive(Debug, Clone, PartialEq)]
pub enum PolytopeHRepError {
    LengthMismatch {
        normals: usize,
        heights: usize,
    },
    NormalNonFinite {
        index: usize,
        component: usize,
        value: f64,
    },
    HeightNonFinite {
        index: usize,
        value: f64,
    },
    HeightNonPositive {
        index: usize,
        value: f64,
    },
    NormalNonUnit {
        index: usize,
        norm: f64,
        tol: f64,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct PolytopeHRepErrors {
    pub errors: Vec<PolytopeHRepError>,
}

impl std::fmt::Display for PolytopeHRepErrors {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for (idx, err) in self.errors.iter().enumerate() {
            if idx > 0 {
                writeln!(f)?;
            }
            write!(f, "{err:?}")?;
        }
        Ok(())
    }
}

impl std::error::Error for PolytopeHRepErrors {}

pub fn validate_hrep(
    normals: &[SymplecticVector],
    heights: &[f64],
    unit_tol: f64,
) -> Result<(), PolytopeHRepErrors> {
    let mut errors = Vec::new();

    if normals.len() != heights.len() {
        errors.push(PolytopeHRepError::LengthMismatch {
            normals: normals.len(),
            heights: heights.len(),
        });
    }

    for (idx, normal) in normals.iter().enumerate() {
        for (component, value) in normal.iter().enumerate() {
            if !value.is_finite() {
                errors.push(PolytopeHRepError::NormalNonFinite {
                    index: idx,
                    component,
                    value: *value,
                });
            }
        }
        let norm = normal.norm();
        if !norm.is_finite() || (norm - 1.0).abs() > unit_tol {
            errors.push(PolytopeHRepError::NormalNonUnit {
                index: idx,
                norm,
                tol: unit_tol,
            });
        }
    }

    for (idx, height) in heights.iter().enumerate() {
        if !height.is_finite() {
            errors.push(PolytopeHRepError::HeightNonFinite {
                index: idx,
                value: *height,
            });
        } else if *height <= 0.0 {
            errors.push(PolytopeHRepError::HeightNonPositive {
                index: idx,
                value: *height,
            });
        }
    }

    if errors.is_empty() {
        Ok(())
    } else {
        Err(PolytopeHRepErrors { errors })
    }
}

pub fn has_near_lagrangian_pair(normals: &[SymplecticVector], eps_lagr: f64) -> bool {
    for (i, ni) in normals.iter().enumerate() {
        for nj in normals.iter().skip(i + 1) {
            if symplectic_form(*ni, *nj).abs() <= eps_lagr {
                return true;
            }
        }
    }
    false
}

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct PerturbationMetadata {
    pub seed: u64,
    pub epsilon: f64,
    pub perturbed_count: usize,
    pub lagrangian_detected: bool,
}

/// Perturb normals with seeded jitter if a near-Lagrangian pair is detected.
pub fn perturb_hrep_if_lagrangian(
    hrep: &Polytope4HRep,
    eps_lagr: f64,
    eps_perturb: f64,
    seed: u64,
) -> (Polytope4HRep, PerturbationMetadata) {
    let lagrangian_detected = has_near_lagrangian_pair(&hrep.normals, eps_lagr);
    if !lagrangian_detected {
        return (
            hrep.clone(),
            PerturbationMetadata {
                seed,
                epsilon: eps_perturb,
                perturbed_count: 0,
                lagrangian_detected,
            },
        );
    }

    let mut rng = ChaCha8Rng::seed_from_u64(seed);
    let normals: Vec<SymplecticVector> = hrep
        .normals
        .iter()
        .map(|n| {
            let jitter = SymplecticVector::new(
                rng.gen_range(-1.0..=1.0),
                rng.gen_range(-1.0..=1.0),
                rng.gen_range(-1.0..=1.0),
                rng.gen_range(-1.0..=1.0),
            ) * eps_perturb;
            normalize(*n + jitter)
        })
        .collect();

    let metadata = PerturbationMetadata {
        seed,
        epsilon: eps_perturb,
        perturbed_count: normals.len(),
        lagrangian_detected,
    };

    (
        Polytope4HRep {
            normals,
            heights: hrep.heights.clone(),
        },
        metadata,
    )
}

fn normalize(v: SymplecticVector) -> SymplecticVector {
    let norm = v.norm();
    if norm.is_finite() && norm > 0.0 {
        v / norm
    } else {
        v
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn j_squared_is_minus_identity() {
        let x = SymplecticVector::new(1.0, 2.0, 3.0, 4.0);
        let jj = j_map(j_map(x));
        assert_eq!(jj, -x);
    }

    #[test]
    fn omega_is_antisymmetric() {
        let x = SymplecticVector::new(1.0, 2.0, 3.0, 4.0);
        let y = SymplecticVector::new(-2.0, 1.0, 0.5, -1.5);
        let omega_xy = symplectic_form(x, y);
        let omega_yx = symplectic_form(y, x);
        assert!((omega_xy + omega_yx).abs() < 1e-12);
    }

    #[test]
    fn omega_matches_coordinate_formula() {
        let x = SymplecticVector::new(1.0, 2.0, 3.0, 4.0);
        let y = SymplecticVector::new(5.0, 6.0, 7.0, 8.0);
        let expected = (1.0 * 7.0 + 2.0 * 8.0) - (3.0 * 5.0 + 4.0 * 6.0);
        assert!((symplectic_form(x, y) - expected).abs() < 1e-12);
    }

    #[test]
    fn perturbation_is_deterministic_and_preserves_heights() {
        let hrep = Polytope4HRep::new(
            vec![
                SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
                SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
            ],
            vec![0.8, 1.2],
        );

        let (perturbed_a, meta_a) = perturb_hrep_if_lagrangian(&hrep, 1e-12, 1e-3, 42);
        let (perturbed_b, meta_b) = perturb_hrep_if_lagrangian(&hrep, 1e-12, 1e-3, 42);

        assert_eq!(meta_a, meta_b);
        assert_eq!(perturbed_a.heights, hrep.heights);
        assert_eq!(perturbed_b.heights, hrep.heights);
        assert_eq!(perturbed_a.normals.len(), perturbed_b.normals.len());

        for (na, nb) in perturbed_a.normals.iter().zip(perturbed_b.normals.iter()) {
            for (a, b) in na.iter().zip(nb.iter()) {
                assert!((a - b).abs() < 1e-12);
            }
            assert!((na.norm() - 1.0).abs() < 1e-10);
        }
    }
}
