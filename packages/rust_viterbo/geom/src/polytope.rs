//! Convex polytope representation in H-rep (half-space intersection).
//!
//! A polytope K ⊂ ℝ⁴ is defined by: K = { x : ⟨nᵢ, x⟩ ≤ hᵢ for all i }.
//! Each facet Fᵢ is the intersection of K with the hyperplane ⟨nᵢ, x⟩ = hᵢ.
//! A 2-face is the intersection of two facets Fᵢ ∩ Fⱼ.

use crate::types::SymplecticVector;
use nalgebra::{Matrix4, Vector4};
use std::cmp::Ordering;
use std::fmt;

/// H-representation of a convex polytope in ℝ⁴.
#[derive(Clone, Debug)]
pub struct PolytopeHRep {
    pub normals: Vec<SymplecticVector>,
    pub heights: Vec<f64>,
}

/// A 2-face (codimension-2 face) of a polytope.
#[derive(Clone, Debug)]
pub struct TwoFace {
    /// Index of first bounding facet.
    pub i: usize,
    /// Index of second bounding facet.
    pub j: usize,
    /// Vertices of the 2-face (ordered cyclically).
    pub vertices: Vec<SymplecticVector>,
}

/// Validation errors for polytope input.
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

    /// Enumerate all 2-faces of the polytope.
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

/// Solve for the vertex at the intersection of 4 hyperplanes.
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

#[cfg(test)]
mod tests {
    use super::*;
    use crate::symplectic::symplectic_form;

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

    #[test]
    fn two_faces_for_tesseract() {
        let hrep = tesseract();
        let faces = hrep.two_faces(1e-6, 1e-6);
        // Tesseract has 24 2-faces
        assert_eq!(faces.len(), 24);
    }

    #[test]
    fn flow_direction_from_omega_sign() {
        let n1 = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let n2 = SymplecticVector::new(0.0, 0.0, 1.0, 0.0);
        let omega = symplectic_form(n1, n2);
        assert!(omega > 0.0);
    }

    #[test]
    fn reeb_velocity_is_tangent() {
        use crate::symplectic::apply_j;
        let n = SymplecticVector::new(1.0, 0.0, 0.0, 0.0);
        let v = apply_j(n);
        assert!(n.dot(&v).abs() < 1e-12);
    }

    #[test]
    fn perturbation_is_deterministic_and_unit() {
        use crate::perturbation::perturb_polytope_normals;
        let hrep = tesseract();
        let out1 = perturb_polytope_normals(&hrep, 123, 1e-4);
        let out2 = perturb_polytope_normals(&hrep, 123, 1e-4);
        for (n1, n2) in out1.polytope.normals.iter().zip(&out2.polytope.normals) {
            assert!((n1 - n2).norm() < 1e-12);
            assert!((n1.norm() - 1.0).abs() < 1e-12);
        }
    }

    #[test]
    fn lagrangian_detection_uses_adjacent_faces() {
        use crate::perturbation::detect_near_lagrangian;
        let hrep = tesseract();
        let det = detect_near_lagrangian(&hrep, 0.1, 1e-6, 1e-6);
        // Tesseract has all-Lagrangian 2-faces
        assert!(det.detected);
    }
}
