//! Core symplectic geometry structures and operations for the Viterbo project.
//!
//! Conventions (locked): coordinates (q1,q2,p1,p2) and J(q,p)=(-p,q).

use nalgebra::Vector4;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::fmt;

pub type Vector4f = Vector4<f64>;
pub type SymplecticVector = Vector4f;

/// Apply the almost complex structure J(q,p)=(-p,q).
pub fn apply_j(v: SymplecticVector) -> SymplecticVector {
    SymplecticVector::new(-v.z, -v.w, v.x, v.y)
}

/// Compute the standard symplectic form ω(x,y)=⟨Jx,y⟩.
pub fn symplectic_form(x: SymplecticVector, y: SymplecticVector) -> f64 {
    apply_j(x).dot(&y)
}

#[derive(Clone, Debug)]
pub struct PolytopeHRep {
    pub normals: Vec<SymplecticVector>,
    pub heights: Vec<f64>,
}

#[derive(Clone, Debug)]
pub enum PolytopeValidationError {
    MismatchedLengths {
        normals: usize,
        heights: usize,
    },
    NonFiniteNormal {
        index: usize,
        component: usize,
        value: f64,
    },
    NonFiniteHeight {
        index: usize,
        value: f64,
    },
    NonPositiveHeight {
        index: usize,
        value: f64,
    },
    NonUnitNormal {
        index: usize,
        norm: f64,
        tolerance: f64,
    },
}

impl fmt::Display for PolytopeValidationError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MismatchedLengths { normals, heights } => write!(
                f,
                "normals/heights length mismatch: normals={normals}, heights={heights}"
            ),
            Self::NonFiniteNormal {
                index,
                component,
                value,
            } => write!(
                f,
                "normal[{index}] has non-finite component {component}: {value}"
            ),
            Self::NonFiniteHeight { index, value } => {
                write!(f, "height[{index}] is non-finite: {value}")
            }
            Self::NonPositiveHeight { index, value } => {
                write!(f, "height[{index}] is not positive: {value}")
            }
            Self::NonUnitNormal {
                index,
                norm,
                tolerance,
            } => write!(
                f,
                "normal[{index}] is not unit: norm={norm} (tolerance={tolerance})"
            ),
        }
    }
}

impl std::error::Error for PolytopeValidationError {}

impl PolytopeHRep {
    pub fn new(normals: Vec<SymplecticVector>, heights: Vec<f64>) -> Self {
        Self { normals, heights }
    }

    pub fn validate(&self, unit_tolerance: f64) -> Result<(), PolytopeValidationError> {
        if self.normals.len() != self.heights.len() {
            return Err(PolytopeValidationError::MismatchedLengths {
                normals: self.normals.len(),
                heights: self.heights.len(),
            });
        }

        for (i, normal) in self.normals.iter().enumerate() {
            for (j, value) in [normal.x, normal.y, normal.z, normal.w].iter().enumerate() {
                if !value.is_finite() {
                    return Err(PolytopeValidationError::NonFiniteNormal {
                        index: i,
                        component: j,
                        value: *value,
                    });
                }
            }
            let norm = normal.norm();
            if !norm.is_finite() {
                return Err(PolytopeValidationError::NonFiniteNormal {
                    index: i,
                    component: 4,
                    value: norm,
                });
            }
            if (norm - 1.0).abs() > unit_tolerance {
                return Err(PolytopeValidationError::NonUnitNormal {
                    index: i,
                    norm,
                    tolerance: unit_tolerance,
                });
            }
        }

        for (i, height) in self.heights.iter().enumerate() {
            if !height.is_finite() {
                return Err(PolytopeValidationError::NonFiniteHeight {
                    index: i,
                    value: *height,
                });
            }
            if *height <= 0.0 {
                return Err(PolytopeValidationError::NonPositiveHeight {
                    index: i,
                    value: *height,
                });
            }
        }

        Ok(())
    }
}

#[derive(Clone, Copy, Debug)]
pub struct LagrangianWitness {
    pub i: usize,
    pub j: usize,
    pub omega: f64,
}

#[derive(Clone, Copy, Debug)]
pub struct LagrangianDetection {
    pub detected: bool,
    pub eps_lagr: f64,
    pub witness: Option<LagrangianWitness>,
}

pub fn detect_near_lagrangian(normals: &[SymplecticVector], eps_lagr: f64) -> LagrangianDetection {
    for (i, ni) in normals.iter().enumerate() {
        for (j, nj) in normals.iter().enumerate().skip(i + 1) {
            let omega = symplectic_form(*ni, *nj);
            if omega.abs() <= eps_lagr {
                return LagrangianDetection {
                    detected: true,
                    eps_lagr,
                    witness: Some(LagrangianWitness { i, j, omega }),
                };
            }
        }
    }
    LagrangianDetection {
        detected: false,
        eps_lagr,
        witness: None,
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PerturbationMetadata {
    pub seed: u64,
    pub epsilon: f64,
    pub perturbed_count: usize,
}

#[derive(Clone, Debug)]
pub struct PerturbationOutcome {
    pub polytope: PolytopeHRep,
    pub metadata: PerturbationMetadata,
}

pub fn perturb_polytope_normals(
    polytope: &PolytopeHRep,
    seed: u64,
    epsilon: f64,
) -> PerturbationOutcome {
    if epsilon == 0.0 {
        return PerturbationOutcome {
            polytope: polytope.clone(),
            metadata: PerturbationMetadata {
                seed,
                epsilon,
                perturbed_count: 0,
            },
        };
    }

    let mut rng = StdRng::seed_from_u64(seed);
    let mut new_normals = Vec::with_capacity(polytope.normals.len());
    for normal in &polytope.normals {
        let mut delta = SymplecticVector::new(
            rng.gen_range(-1.0..1.0),
            rng.gen_range(-1.0..1.0),
            rng.gen_range(-1.0..1.0),
            rng.gen_range(-1.0..1.0),
        );
        if delta.norm() <= f64::EPSILON {
            delta = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        }
        let perturbed = (normal + delta.scale(epsilon)).normalize();
        new_normals.push(perturbed);
    }

    PerturbationOutcome {
        polytope: PolytopeHRep::new(new_normals, polytope.heights.clone()),
        metadata: PerturbationMetadata {
            seed,
            epsilon,
            perturbed_count: polytope.normals.len(),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn j_squared_is_minus_identity() {
        let v = SymplecticVector::new(1.5, -2.0, 3.0, 4.5);
        let jj = apply_j(apply_j(v));
        let expected = SymplecticVector::new(-v.x, -v.y, -v.z, -v.w);
        assert_eq!(jj, expected);
    }

    #[test]
    fn omega_is_antisymmetric() {
        let x = SymplecticVector::new(1.0, 2.0, 3.0, 4.0);
        let y = SymplecticVector::new(-2.0, 1.5, -1.0, 0.5);
        let sum = symplectic_form(x, y) + symplectic_form(y, x);
        assert!(sum.abs() < 1e-12);
    }

    #[test]
    fn omega_matches_coordinate_formula() {
        let x = SymplecticVector::new(1.0, -2.0, 3.0, -4.0);
        let y = SymplecticVector::new(-0.5, 1.5, 2.0, -3.0);
        let omega = symplectic_form(x, y);
        let q_dot_p = x.x * y.z + x.y * y.w;
        let p_dot_q = x.z * y.x + x.w * y.y;
        assert!((omega - (q_dot_p - p_dot_q)).abs() < 1e-12);
    }

    #[test]
    fn perturbation_is_deterministic_and_unit() {
        let polytope = PolytopeHRep::new(
            vec![
                SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
                SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
            ],
            vec![1.0, 2.0],
        );
        let first = perturb_polytope_normals(&polytope, 7, 1e-3);
        let second = perturb_polytope_normals(&polytope, 7, 1e-3);
        assert_eq!(first.polytope.heights, polytope.heights);
        assert_eq!(first.polytope.heights, second.polytope.heights);
        for normal in &first.polytope.normals {
            assert!((normal.norm() - 1.0).abs() < 1e-8);
        }
        assert_eq!(first.polytope.normals, second.polytope.normals);
    }
}
