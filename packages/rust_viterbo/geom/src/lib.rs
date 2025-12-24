//! Core symplectic geometry structures and operations for the Viterbo project.
//!
//! Conventions follow the thesis: coordinates (q1,q2,p1,p2), J(q,p)=(-p,q),
//! and omega(x,y)=<Jx,y>.

use nalgebra::Vector4;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

/// 4D vector in standard symplectic coordinates (q1,q2,p1,p2).
pub type SymplecticVector = Vector4<f64>;

/// Apply the almost-complex structure J(q,p)=(-p,q).
pub fn apply_j(v: SymplecticVector) -> SymplecticVector {
    SymplecticVector::new(-v.z, -v.w, v.x, v.y)
}

/// Standard symplectic form omega(x,y)=<Jx,y>.
pub fn omega(x: SymplecticVector, y: SymplecticVector) -> f64 {
    apply_j(x).dot(&y)
}

/// Backwards-compatible name for the symplectic form.
pub fn symplectic_form(x: SymplecticVector, y: SymplecticVector) -> f64 {
    omega(x, y)
}

/// Irredundant H-representation of a convex polytope in R^4.
#[derive(Debug, Clone)]
pub struct Polytope4H {
    normals: Vec<SymplecticVector>,
    heights: Vec<f64>,
}

impl Polytope4H {
    pub fn new(normals: Vec<SymplecticVector>, heights: Vec<f64>) -> Self {
        Self { normals, heights }
    }

    pub fn normals(&self) -> &[SymplecticVector] {
        &self.normals
    }

    pub fn heights(&self) -> &[f64] {
        &self.heights
    }

    pub fn validate(&self, tol_unit: f64) -> Result<(), PolytopeValidationError> {
        if self.normals.len() != self.heights.len() {
            return Err(PolytopeValidationError::LengthMismatch {
                normals: self.normals.len(),
                heights: self.heights.len(),
            });
        }

        for (i, n) in self.normals.iter().enumerate() {
            let comps = [n.x, n.y, n.z, n.w];
            for (j, value) in comps.iter().enumerate() {
                if !value.is_finite() {
                    return Err(PolytopeValidationError::NonFiniteNormal {
                        index: i,
                        component: j,
                        value: *value,
                    });
                }
            }
            let norm = n.norm();
            if !norm.is_finite() {
                return Err(PolytopeValidationError::NonUnitNormal {
                    index: i,
                    norm,
                    tol: tol_unit,
                });
            }
            if (norm - 1.0).abs() > tol_unit {
                return Err(PolytopeValidationError::NonUnitNormal {
                    index: i,
                    norm,
                    tol: tol_unit,
                });
            }
        }

        for (i, h) in self.heights.iter().enumerate() {
            if !h.is_finite() {
                return Err(PolytopeValidationError::NonFiniteHeight {
                    index: i,
                    value: *h,
                });
            }
            if *h <= 0.0 {
                return Err(PolytopeValidationError::NonPositiveHeight {
                    index: i,
                    value: *h,
                });
            }
        }

        Ok(())
    }

    pub fn is_near_lagrangian(&self, eps_lagr: f64) -> bool {
        is_near_lagrangian_normals(&self.normals, eps_lagr)
    }
}

#[derive(Debug, Clone)]
pub enum PolytopeValidationError {
    LengthMismatch {
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
        tol: f64,
    },
}

impl std::fmt::Display for PolytopeValidationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            PolytopeValidationError::LengthMismatch { normals, heights } => {
                write!(f, "length mismatch: normals={normals}, heights={heights}")
            }
            PolytopeValidationError::NonFiniteNormal {
                index,
                component,
                value,
            } => {
                write!(
                    f,
                    "normal[{index}] component {component} is non-finite: {value}"
                )
            }
            PolytopeValidationError::NonFiniteHeight { index, value } => {
                write!(f, "height[{index}] is non-finite: {value}")
            }
            PolytopeValidationError::NonPositiveHeight { index, value } => {
                write!(f, "height[{index}] is not positive: {value}")
            }
            PolytopeValidationError::NonUnitNormal { index, norm, tol } => {
                write!(f, "normal[{index}] is not unit (norm={norm}, tol={tol})")
            }
        }
    }
}

impl std::error::Error for PolytopeValidationError {}

/// Metadata for perturbing Lagrangian polytopes.
#[derive(Debug, Clone, Copy)]
pub struct PerturbationMetadata {
    pub seed: u64,
    pub epsilon: f64,
    pub eps_lagr: f64,
    pub perturbed_count: usize,
    pub was_lagrangian: bool,
}

/// Perturb normals if a near-Lagrangian 2-face is detected.
pub fn perturb_polytope_if_lagrangian(
    polytope: &Polytope4H,
    eps_lagr: f64,
    eps_perturb: f64,
    seed: u64,
) -> (Polytope4H, PerturbationMetadata) {
    let was_lagrangian = is_near_lagrangian_normals(&polytope.normals, eps_lagr);
    if !was_lagrangian || eps_perturb <= 0.0 {
        let metadata = PerturbationMetadata {
            seed,
            epsilon: eps_perturb,
            eps_lagr,
            perturbed_count: 0,
            was_lagrangian,
        };
        return (
            Polytope4H::new(polytope.normals.clone(), polytope.heights.clone()),
            metadata,
        );
    }

    let mut rng = StdRng::seed_from_u64(seed);
    let mut perturbed = Vec::with_capacity(polytope.normals.len());
    for n in &polytope.normals {
        let jitter = SymplecticVector::new(
            rng.gen_range(-1.0..=1.0),
            rng.gen_range(-1.0..=1.0),
            rng.gen_range(-1.0..=1.0),
            rng.gen_range(-1.0..=1.0),
        ) * eps_perturb;
        let candidate = (*n + jitter).normalize();
        perturbed.push(candidate);
    }

    let metadata = PerturbationMetadata {
        seed,
        epsilon: eps_perturb,
        eps_lagr,
        perturbed_count: perturbed.len(),
        was_lagrangian,
    };

    (
        Polytope4H::new(perturbed, polytope.heights.clone()),
        metadata,
    )
}

fn is_near_lagrangian_normals(normals: &[SymplecticVector], eps_lagr: f64) -> bool {
    for i in 0..normals.len() {
        for j in (i + 1)..normals.len() {
            if omega(normals[i], normals[j]).abs() <= eps_lagr {
                return true;
            }
        }
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn j_squared_is_minus_identity() {
        let x = SymplecticVector::new(1.5, -2.0, 0.25, 3.0);
        let jjx = apply_j(apply_j(x));
        let expected = SymplecticVector::new(-x.x, -x.y, -x.z, -x.w);
        assert_eq!(jjx, expected);
    }

    #[test]
    fn omega_is_antisymmetric() {
        let x = SymplecticVector::new(1.0, 0.0, 2.0, -1.0);
        let y = SymplecticVector::new(-0.5, 3.0, 0.25, 2.5);
        let xy = omega(x, y);
        let yx = omega(y, x);
        assert!((xy + yx).abs() < 1e-12);
    }

    #[test]
    fn omega_matches_coordinate_formula() {
        let x = SymplecticVector::new(1.0, 2.0, 3.0, 4.0);
        let y = SymplecticVector::new(5.0, 6.0, 7.0, 8.0);
        let expected = x.x * y.z + x.y * y.w - x.z * y.x - x.w * y.y;
        assert!((omega(x, y) - expected).abs() < 1e-12);
    }

    #[test]
    fn perturbation_is_deterministic_and_keeps_units() {
        let normals = vec![
            SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
            SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
        ];
        let heights = vec![1.0, 2.0];
        let poly = Polytope4H::new(normals, heights.clone());

        let (p1, meta1) = perturb_polytope_if_lagrangian(&poly, 1e-12, 1e-3, 42);
        let (p2, meta2) = perturb_polytope_if_lagrangian(&poly, 1e-12, 1e-3, 42);

        assert_eq!(meta1.seed, meta2.seed);
        assert_eq!(p1.normals(), p2.normals());
        assert_eq!(p1.heights(), heights.as_slice());

        for n in p1.normals() {
            assert!((n.norm() - 1.0).abs() < 1e-6);
        }
    }
}
