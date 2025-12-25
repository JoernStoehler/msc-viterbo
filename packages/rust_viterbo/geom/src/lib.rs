//! Core symplectic geometry structures and operations for the Viterbo project.
//!
//! Conventions (locked): coordinates (q1,q2,p1,p2) and J(q,p)=(-p,q).

use nalgebra::{Matrix4, Vector4};
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
pub struct TwoFace {
    pub i: usize,
    pub j: usize,
    pub vertices: Vec<SymplecticVector>,
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

    pub fn two_faces(&self, eps_feas: f64, eps_dedup: f64) -> Vec<TwoFace> {
        let mut faces = Vec::new();
        let n = self.normals.len();
        if n < 4 {
            return faces;
        }
        let eps_dedup_sq = eps_dedup * eps_dedup;

        for i in 0..n {
            for j in (i + 1)..n {
                let mut vertices: Vec<SymplecticVector> = Vec::new();
                for k in 0..n {
                    if k == i || k == j {
                        continue;
                    }
                    for l in (k + 1)..n {
                        if l == i || l == j {
                            continue;
                        }
                        let a = Matrix4::new(
                            self.normals[i].x,
                            self.normals[i].y,
                            self.normals[i].z,
                            self.normals[i].w,
                            self.normals[j].x,
                            self.normals[j].y,
                            self.normals[j].z,
                            self.normals[j].w,
                            self.normals[k].x,
                            self.normals[k].y,
                            self.normals[k].z,
                            self.normals[k].w,
                            self.normals[l].x,
                            self.normals[l].y,
                            self.normals[l].z,
                            self.normals[l].w,
                        );
                        let b = Vector4::new(
                            self.heights[i],
                            self.heights[j],
                            self.heights[k],
                            self.heights[l],
                        );
                        let Some(x) = a.lu().solve(&b) else {
                            continue;
                        };

                        let dot_i = self.normals[i].dot(&x);
                        let dot_j = self.normals[j].dot(&x);
                        if (dot_i - self.heights[i]).abs() > eps_feas
                            || (dot_j - self.heights[j]).abs() > eps_feas
                        {
                            continue;
                        }

                        let mut feasible = true;
                        for m in 0..n {
                            if self.normals[m].dot(&x) > self.heights[m] + eps_feas {
                                feasible = false;
                                break;
                            }
                        }
                        if !feasible {
                            continue;
                        }

                        if vertices
                            .iter()
                            .any(|v| (v - x).norm_squared() <= eps_dedup_sq)
                        {
                            continue;
                        }
                        vertices.push(x);
                    }
                }

                if vertices.len() < 3 {
                    continue;
                }

                if let Some((u, v)) = face_plane_basis(self.normals[i], self.normals[j]) {
                    let centroid = vertices
                        .iter()
                        .fold(SymplecticVector::zeros(), |acc, x| acc + x)
                        / (vertices.len() as f64);
                    let mut with_angle: Vec<(f64, SymplecticVector)> = vertices
                        .into_iter()
                        .map(|x| {
                            let d = x - centroid;
                            let angle = d.dot(&v).atan2(d.dot(&u));
                            (angle, x)
                        })
                        .collect();
                    with_angle.sort_by(|a, b| a.0.total_cmp(&b.0));
                    vertices = with_angle.into_iter().map(|(_, x)| x).collect();
                }

                faces.push(TwoFace { i, j, vertices });
            }
        }

        faces
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

pub fn detect_near_lagrangian(
    polytope: &PolytopeHRep,
    eps_lagr: f64,
    eps_feas: f64,
    eps_dedup: f64,
) -> LagrangianDetection {
    for face in polytope.two_faces(eps_feas, eps_dedup) {
        let omega = symplectic_form(polytope.normals[face.i], polytope.normals[face.j]);
        if omega.abs() <= eps_lagr {
            return LagrangianDetection {
                detected: true,
                eps_lagr,
                witness: Some(LagrangianWitness {
                    i: face.i,
                    j: face.j,
                    omega,
                }),
            };
        }
    }

    LagrangianDetection {
        detected: false,
        eps_lagr,
        witness: None,
    }
}

fn face_plane_basis(
    ni: SymplecticVector,
    nj: SymplecticVector,
) -> Option<(SymplecticVector, SymplecticVector)> {
    let mut basis: Vec<SymplecticVector> = Vec::new();
    let candidates = [
        SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
    ];
    for e in candidates {
        let mut v = e - ni * e.dot(&ni) - nj * e.dot(&nj);
        for b in &basis {
            v -= *b * v.dot(b);
        }
        let norm = v.norm();
        if norm > 1e-10 {
            basis.push(v / norm);
            if basis.len() == 2 {
                break;
            }
        }
    }
    if basis.len() == 2 {
        Some((basis[0], basis[1]))
    } else {
        None
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

    fn tesseract_hrep() -> PolytopeHRep {
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
        let heights = vec![1.0; normals.len()];
        PolytopeHRep::new(normals, heights)
    }

    #[test]
    fn tesseract_two_faces_are_squares() {
        let polytope = tesseract_hrep();
        let eps_feas = 1e-9;
        let eps_dedup = 1e-7;
        let faces = polytope.two_faces(eps_feas, eps_dedup);
        assert_eq!(faces.len(), 24);

        for face in &faces {
            assert_eq!(face.vertices.len(), 4);
            for v in &face.vertices {
                for (normal, height) in polytope.normals.iter().zip(polytope.heights.iter()) {
                    assert!(normal.dot(v) <= height + eps_feas);
                }
            }
        }
    }

    #[test]
    fn tesseract_lagrangian_faces_are_adjacent_only() {
        let polytope = tesseract_hrep();
        let eps_lagr = 1e-12;
        let eps_feas = 1e-9;
        let eps_dedup = 1e-7;
        let faces = polytope.two_faces(eps_feas, eps_dedup);
        let lagrangian_count = faces
            .iter()
            .filter(|face| {
                symplectic_form(polytope.normals[face.i], polytope.normals[face.j]).abs()
                    <= eps_lagr
            })
            .count();
        assert_eq!(lagrangian_count, 16);
        assert_eq!(faces.len() - lagrangian_count, 8);

        let detection = detect_near_lagrangian(&polytope, eps_lagr, eps_feas, eps_dedup);
        assert!(detection.detected);
        let witness = detection.witness.expect("expected lagrangian witness");
        assert!(
            faces
                .iter()
                .any(|face| face.i == witness.i && face.j == witness.j),
            "witness should correspond to an adjacent face"
        );
        assert!(witness.omega.abs() <= eps_lagr);
    }
}
