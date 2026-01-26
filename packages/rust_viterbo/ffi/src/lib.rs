//! Python FFI for EHZ capacity algorithms.
//!
//! This crate provides Python bindings for the tube algorithm and related
//! geometric computations.

use nalgebra::Vector4;
use pyo3::exceptions::{PyNotImplementedError, PyValueError};
use pyo3::prelude::*;
use tube::{PolytopeHRep, tube_capacity};

const ARCHIVED_MSG: &str =
    "Archived. See docs/developer-spec.md to re-implement, or checkout tag v0.1.0-archive";

/// Return the symplectic form ω(x,y) in R^4.
///
/// ω(x, y) = q₁p₁' + q₂p₂' - p₁q₁' - p₂q₂'
/// where x = (q₁, q₂, p₁, p₂) and y = (q₁', q₂', p₁', p₂')
#[pyfunction]
fn symplectic_form_4d(a: [f64; 4], b: [f64; 4]) -> f64 {
    a[0] * b[2] + a[1] * b[3] - a[2] * b[0] - a[3] * b[1]
}

/// Compute EHZ capacity using the tube algorithm.
///
/// The tube algorithm applies to polytopes with NO Lagrangian 2-faces
/// (i.e., ω(nᵢ, nⱼ) ≠ 0 for all adjacent facet pairs).
///
/// # Arguments
/// * `normals` - List of unit outward facet normals (each as [q1, q2, p1, p2])
/// * `heights` - List of facet heights (must be positive, implying 0 ∈ int(K))
/// * `unit_tol` - Tolerance for unit normal validation (default: 1e-9)
///
/// # Returns
/// * `float` - The EHZ capacity (minimum action of closed Reeb orbits)
///
/// # Raises
/// * `ValueError` - If input validation fails or polytope has Lagrangian 2-faces
#[pyfunction]
#[pyo3(signature = (normals, heights, unit_tol=1e-9))]
fn tube_capacity_hrep(
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
    unit_tol: f64,
) -> PyResult<f64> {
    // Convert normals to nalgebra vectors
    let normals: Vec<Vector4<f64>> = normals
        .into_iter()
        .map(|n| Vector4::new(n[0], n[1], n[2], n[3]))
        .collect();

    // Validate unit normals
    for (i, n) in normals.iter().enumerate() {
        let norm = n.norm();
        if (norm - 1.0).abs() > unit_tol {
            return Err(PyValueError::new_err(format!(
                "Normal {} is not a unit vector: ||n|| = {}",
                i, norm
            )));
        }
    }

    // Create H-rep
    let hrep = PolytopeHRep::new(normals, heights).map_err(|e| {
        PyValueError::new_err(format!("Invalid polytope: {}", e))
    })?;

    // Run tube algorithm
    let (capacity, _orbit) = tube_capacity(&hrep).map_err(|e| {
        PyValueError::new_err(format!("Tube algorithm failed: {}", e))
    })?;

    Ok(capacity)
}

/// Compute EHZ capacity using the Minkowski billiard algorithm.
/// ARCHIVED - Returns NotImplementedError.
#[pyfunction]
#[pyo3(signature = (_normals, _heights, _unit_tol=1e-9))]
fn billiard_capacity_hrep(
    _normals: Vec<[f64; 4]>,
    _heights: Vec<f64>,
    _unit_tol: f64,
) -> PyResult<f64> {
    Err(PyNotImplementedError::new_err(ARCHIVED_MSG))
}

/// Compute EHZ capacity using the HK2019 quadratic programming algorithm.
/// ARCHIVED - Returns NotImplementedError.
#[pyfunction]
#[pyo3(signature = (_normals, _heights, _unit_tol=1e-9))]
fn hk2019_capacity_hrep(
    _normals: Vec<[f64; 4]>,
    _heights: Vec<f64>,
    _unit_tol: f64,
) -> PyResult<f64> {
    Err(PyNotImplementedError::new_err(ARCHIVED_MSG))
}

#[pymodule]
fn rust_viterbo_ffi(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(symplectic_form_4d, m)?)?;
    m.add_function(wrap_pyfunction!(tube_capacity_hrep, m)?)?;
    m.add_function(wrap_pyfunction!(billiard_capacity_hrep, m)?)?;
    m.add_function(wrap_pyfunction!(hk2019_capacity_hrep, m)?)?;
    Ok(())
}
