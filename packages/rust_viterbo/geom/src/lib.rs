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
        let facet_count = self.normals.len();
        if facet_count < 4 {
            return Vec::new();
        }

        let mut faces = Vec::new();
        for i in 0..facet_count {
            for j in (i + 1)..facet_count {
                let mut vertices = Vec::new();
                for k in 0..facet_count {
                    if k == i || k == j {
                        continue;
                    }
                    for l in (k + 1)..facet_count {
                        if l == i || l == j {
                            continue;
                        }
                        if let Some(candidate) =
                            solve_vertex(&self.normals, &self.heights, i, j, k, l)
                        {
                            if is_vertex_feasible(
                                &self.normals,
                                &self.heights,
                                candidate,
                                i,
                                j,
                                eps_feas,
                            ) {
                                push_dedup_vertex(&mut vertices, candidate, eps_dedup);
                            }
                        }
                    }
                }

                if vertices.len() >= 3 {
                    order_face_vertices(&mut vertices, self.normals[i], self.normals[j]);
                    faces.push(TwoFace { i, j, vertices });
                }
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
    let faces = polytope.two_faces(eps_feas, eps_dedup);
    for face in faces {
        let ni = polytope.normals[face.i];
        let nj = polytope.normals[face.j];
        let omega = symplectic_form(ni, nj);
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

fn solve_vertex(
    normals: &[SymplecticVector],
    heights: &[f64],
    i: usize,
    j: usize,
    k: usize,
    l: usize,
) -> Option<SymplecticVector> {
    let ni = normals[i];
    let nj = normals[j];
    let nk = normals[k];
    let nl = normals[l];
    let a = Matrix4::new(
        ni.x, ni.y, ni.z, ni.w, nj.x, nj.y, nj.z, nj.w, nk.x, nk.y, nk.z, nk.w, nl.x, nl.y, nl.z,
        nl.w,
    );
    let b = SymplecticVector::new(heights[i], heights[j], heights[k], heights[l]);
    let lu = a.lu();
    lu.solve(&b)
}

fn is_vertex_feasible(
    normals: &[SymplecticVector],
    heights: &[f64],
    candidate: SymplecticVector,
    i: usize,
    j: usize,
    eps_feas: f64,
) -> bool {
    let slack_i = normals[i].dot(&candidate) - heights[i];
    let slack_j = normals[j].dot(&candidate) - heights[j];
    if slack_i.abs() > eps_feas || slack_j.abs() > eps_feas {
        return false;
    }
    for (m, normal) in normals.iter().enumerate() {
        let slack = normal.dot(&candidate) - heights[m];
        if slack > eps_feas {
            return false;
        }
    }
    true
}

fn push_dedup_vertex(
    vertices: &mut Vec<SymplecticVector>,
    candidate: SymplecticVector,
    eps_dedup: f64,
) {
    if vertices
        .iter()
        .any(|existing| (existing - candidate).norm() <= eps_dedup)
    {
        return;
    }
    vertices.push(candidate);
}

fn order_face_vertices(
    vertices: &mut [SymplecticVector],
    n_i: SymplecticVector,
    n_j: SymplecticVector,
) {
    if vertices.len() < 3 {
        return;
    }
    let Some((u, v)) = face_basis(n_i, n_j) else {
        return;
    };
    let mut centroid = SymplecticVector::zeros();
    for vertex in vertices.iter() {
        centroid += vertex;
    }
    centroid /= vertices.len() as f64;
    vertices.sort_by(|a, b| {
        let da = *a - centroid;
        let db = *b - centroid;
        let angle_a = da.dot(&v).atan2(da.dot(&u));
        let angle_b = db.dot(&v).atan2(db.dot(&u));
        angle_a
            .partial_cmp(&angle_b)
            .unwrap_or(std::cmp::Ordering::Equal)
    });
}

fn face_basis(
    n_i: SymplecticVector,
    n_j: SymplecticVector,
) -> Option<(SymplecticVector, SymplecticVector)> {
    let basis = [
        SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
    ];
    let mut u = None;
    for e in basis {
        let mut candidate = e - n_i.scale(e.dot(&n_i)) - n_j.scale(e.dot(&n_j));
        if candidate.norm() > 1e-10 {
            candidate = candidate.normalize();
            u = Some(candidate);
            break;
        }
    }
    let u = u?;
    let mut v = None;
    for e in basis {
        let mut candidate =
            e - n_i.scale(e.dot(&n_i)) - n_j.scale(e.dot(&n_j)) - u.scale(e.dot(&u));
        if candidate.norm() > 1e-10 {
            candidate = candidate.normalize();
            v = Some(candidate);
            break;
        }
    }
    let v = v?;
    Some((u, v))
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

    fn cube_polytope() -> PolytopeHRep {
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
    fn cube_two_faces_are_squares() {
        let polytope = cube_polytope();
        let eps_feas = 1e-9;
        let eps_dedup = 1e-8;
        let faces = polytope.two_faces(eps_feas, eps_dedup);
        assert_eq!(faces.len(), 24);
        for face in &faces {
            assert_eq!(face.vertices.len(), 4);
            for vertex in &face.vertices {
                for (normal, height) in polytope.normals.iter().zip(polytope.heights.iter()) {
                    let slack = normal.dot(vertex) - height;
                    assert!(slack <= eps_feas);
                }
            }
        }
    }

    #[test]
    fn cube_lagrangian_faces_match_expectations() {
        let polytope = cube_polytope();
        let eps_lagr = 1e-12;
        let eps_feas = 1e-9;
        let eps_dedup = 1e-8;
        let faces = polytope.two_faces(eps_feas, eps_dedup);
        let lagrangian_faces = faces
            .iter()
            .filter(|face| {
                let omega = symplectic_form(polytope.normals[face.i], polytope.normals[face.j]);
                omega.abs() <= eps_lagr
            })
            .count();
        assert_eq!(lagrangian_faces, 16);
        assert_eq!(faces.len() - lagrangian_faces, 8);

        let detection = detect_near_lagrangian(&polytope, eps_lagr, eps_feas, eps_dedup);
        assert!(detection.detected);
        let witness = detection.witness.expect("expected a witness");
        assert!(faces.iter().any(|face| {
            (face.i == witness.i && face.j == witness.j)
                || (face.i == witness.j && face.j == witness.i)
        }));
    }
}
