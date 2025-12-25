//! Core symplectic geometry structures and operations for the Viterbo project.
//!
//! Conventions (locked): coordinates (q1,q2,p1,p2) and J(q,p)=(-p,q).

use nalgebra::{Matrix4, Vector4};
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};
use std::cmp::Ordering;
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
                        if let Some(x) = solve_vertex(&self.normals, &self.heights, i, j, k, l) {
                            if is_vertex_feasible(&x, &self.normals, &self.heights, eps_feas)
                                && is_vertex_on_facet(
                                    &x,
                                    self.normals[i],
                                    self.heights[i],
                                    eps_feas,
                                )
                                && is_vertex_on_facet(
                                    &x,
                                    self.normals[j],
                                    self.heights[j],
                                    eps_feas,
                                )
                            {
                                insert_dedup(&mut vertices, x, eps_dedup);
                            }
                        }
                    }
                }
                if vertices.len() >= 3 {
                    order_face_vertices(&mut vertices, self.normals[i], self.normals[j], eps_feas);
                    faces.push(TwoFace { i, j, vertices });
                }
            }
        }
        faces
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
    let n_i = normals[i];
    let n_j = normals[j];
    let n_k = normals[k];
    let n_l = normals[l];
    let h_i = heights[i];
    let h_j = heights[j];
    let h_k = heights[k];
    let h_l = heights[l];
    let a = Matrix4::new(
        n_i.x, n_i.y, n_i.z, n_i.w, n_j.x, n_j.y, n_j.z, n_j.w, n_k.x, n_k.y, n_k.z, n_k.w, n_l.x,
        n_l.y, n_l.z, n_l.w,
    );
    let b = Vector4::new(h_i, h_j, h_k, h_l);
    let lu = a.lu();
    let x = lu.solve(&b)?;
    if x.x.is_finite() && x.y.is_finite() && x.z.is_finite() && x.w.is_finite() {
        Some(x)
    } else {
        None
    }
}

fn is_vertex_feasible(
    x: &SymplecticVector,
    normals: &[SymplecticVector],
    heights: &[f64],
    eps_feas: f64,
) -> bool {
    normals
        .iter()
        .zip(heights.iter())
        .all(|(n, h)| n.dot(x) <= h + eps_feas)
}

fn is_vertex_on_facet(
    x: &SymplecticVector,
    normal: SymplecticVector,
    height: f64,
    eps_feas: f64,
) -> bool {
    (normal.dot(x) - height).abs() <= eps_feas
}

fn insert_dedup(vertices: &mut Vec<SymplecticVector>, candidate: SymplecticVector, eps: f64) {
    if vertices
        .iter()
        .any(|existing| (candidate - *existing).norm() <= eps)
    {
        return;
    }
    vertices.push(candidate);
}

fn order_face_vertices(
    vertices: &mut [SymplecticVector],
    n_i: SymplecticVector,
    n_j: SymplecticVector,
    eps_basis: f64,
) {
    if vertices.len() < 3 {
        return;
    }
    let Some((u, v)) = face_plane_basis(n_i, n_j, eps_basis) else {
        return;
    };
    let centroid = vertices
        .iter()
        .fold(SymplecticVector::zeros(), |acc, x| acc + *x)
        / (vertices.len() as f64);
    let mut with_angles: Vec<(f64, SymplecticVector)> = vertices
        .iter()
        .map(|x| {
            let d = *x - centroid;
            let angle = d.dot(&v).atan2(d.dot(&u));
            (angle, *x)
        })
        .collect();
    with_angles.sort_by(|(a, _), (b, _)| a.partial_cmp(b).unwrap_or(Ordering::Equal));
    for (slot, (_, vtx)) in vertices.iter_mut().zip(with_angles.into_iter()) {
        *slot = vtx;
    }
}

fn face_plane_basis(
    n_i: SymplecticVector,
    n_j: SymplecticVector,
    eps: f64,
) -> Option<(SymplecticVector, SymplecticVector)> {
    let a = n_i.normalize();
    let mut b = n_j - a * n_j.dot(&a);
    if b.norm() <= eps {
        return None;
    }
    b = b.normalize();

    let basis = [
        SymplecticVector::new(1.0, 0.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 1.0, 0.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 1.0, 0.0),
        SymplecticVector::new(0.0, 0.0, 0.0, 1.0),
    ];

    let mut u = None;
    for e in basis.iter() {
        let mut candidate = *e - a * e.dot(&a) - b * e.dot(&b);
        let norm = candidate.norm();
        if norm > eps {
            candidate /= norm;
            u = Some(candidate);
            break;
        }
    }
    let u = u?;

    for e in basis.iter() {
        let mut candidate = *e - a * e.dot(&a) - b * e.dot(&b) - u * e.dot(&u);
        let norm = candidate.norm();
        if norm > eps {
            candidate /= norm;
            return Some((u, candidate));
        }
    }
    None
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
    fn two_faces_for_tesseract() {
        let polytope = cube_polytope();
        let eps_feas = 1e-9;
        let eps_dedup = 1e-8;
        let faces = polytope.two_faces(eps_feas, eps_dedup);
        assert_eq!(faces.len(), 24);
        for face in faces {
            assert_eq!(face.vertices.len(), 4);
            for vertex in face.vertices {
                for (normal, height) in polytope.normals.iter().zip(polytope.heights.iter()) {
                    assert!(normal.dot(&vertex) <= height + eps_feas);
                }
            }
        }
    }

    #[test]
    fn lagrangian_detection_uses_adjacent_faces() {
        let polytope = cube_polytope();
        let eps_lagr = 1e-9;
        let eps_feas = 1e-9;
        let eps_dedup = 1e-8;
        let faces = polytope.two_faces(eps_feas, eps_dedup);
        let lagrangian_faces = faces
            .iter()
            .filter(|face| {
                symplectic_form(polytope.normals[face.i], polytope.normals[face.j]).abs()
                    <= eps_lagr
            })
            .count();
        assert_eq!(lagrangian_faces, 16);
        assert_eq!(faces.len() - lagrangian_faces, 8);

        let detection = detect_near_lagrangian(&polytope, eps_lagr, eps_feas, eps_dedup);
        assert!(detection.detected);
        let witness = detection.witness.expect("expected witness");
        let witness_adjacent = faces.iter().any(|face| {
            (face.i == witness.i && face.j == witness.j)
                || (face.i == witness.j && face.j == witness.i)
        });
        assert!(witness_adjacent);
    }
}
