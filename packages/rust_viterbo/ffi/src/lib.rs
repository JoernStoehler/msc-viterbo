//! ARCHIVED STUB - Implementation deleted
//!
//! This crate previously provided Python FFI for EHZ capacity algorithms.
//! The implementation has been archived at tag `v0.1.0-archive`.
//!
//! To re-implement:
//! 1. Read `docs/developer-spec.md` for algorithm specifications
//! 2. Read `docs/ffi-contract.md` for the Python API contract
//! 3. Reference the archived code via `git show v0.1.0-archive:packages/rust_viterbo/`

use pyo3::exceptions::PyNotImplementedError;
use pyo3::prelude::*;

const ARCHIVED_MSG: &str =
    "Archived. See docs/developer-spec.md to re-implement, or checkout tag v0.1.0-archive";

/// Return the symplectic form ω(x,y) in R^4.
///
/// This is the only function that still works - it's a simple computation.
#[pyfunction]
fn symplectic_form_4d(a: [f64; 4], b: [f64; 4]) -> f64 {
    // ω(x, y) = q₁p₁' + q₂p₂' - p₁q₁' - p₂q₂'
    // where x = (q₁, q₂, p₁, p₂) and y = (q₁', q₂', p₁', p₂')
    a[0] * b[2] + a[1] * b[3] - a[2] * b[0] - a[3] * b[1]
}

/// Entry point for the tube capacity algorithm (H-rep only).
/// ARCHIVED - Returns NotImplementedError.
#[pyfunction]
#[pyo3(signature = (_normals, _heights, _unit_tol=1e-9))]
fn tube_capacity_hrep(
    _normals: Vec<[f64; 4]>,
    _heights: Vec<f64>,
    _unit_tol: f64,
) -> PyResult<f64> {
    Err(PyNotImplementedError::new_err(ARCHIVED_MSG))
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
