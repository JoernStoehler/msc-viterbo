//! PyO3 bindings for exposing Rust functionality to Python.

#![allow(clippy::useless_conversion)]

use pyo3::exceptions::{PyNotImplementedError, PyValueError};
use pyo3::prelude::*;
use rust_viterbo_algorithm::compute_capacity_stub;
use rust_viterbo_geom::{perturb_polytope_if_lagrangian, Polytope4H, SymplecticVector};

fn normals_from_python(normals: Vec<Vec<f64>>) -> PyResult<Vec<SymplecticVector>> {
    let mut out = Vec::with_capacity(normals.len());
    for (i, raw) in normals.into_iter().enumerate() {
        if raw.len() != 4 {
            return Err(PyValueError::new_err(format!(
                "normal[{i}] has length {}, expected 4",
                raw.len()
            )));
        }
        out.push(SymplecticVector::new(raw[0], raw[1], raw[2], raw[3]));
    }
    Ok(out)
}

/// H-rep-only capacity entrypoint (algorithm stub).
#[pyfunction]
#[pyo3(signature = (normals, heights, *, eps_lagr=1.0e-8, eps_perturb=1.0e-6, seed=0, tol_unit=1.0e-6))]
#[allow(clippy::useless_conversion)]
fn capacity_hrep(
    normals: Vec<Vec<f64>>,
    heights: Vec<f64>,
    eps_lagr: f64,
    eps_perturb: f64,
    seed: u64,
    tol_unit: f64,
) -> PyResult<()> {
    let normals = normals_from_python(normals)?;
    let polytope = Polytope4H::new(normals, heights);
    if let Err(err) = polytope.validate(tol_unit) {
        return Err(PyValueError::new_err(err.to_string()));
    }

    let (polytope, metadata) =
        perturb_polytope_if_lagrangian(&polytope, eps_lagr, eps_perturb, seed);

    let algorithm_result = compute_capacity_stub(&polytope);
    let diagnostics = format!(
        "lagrangian_detected={}, perturbed_count={}, seed={}, eps_lagr={}, eps_perturb={}",
        metadata.was_lagrangian,
        metadata.perturbed_count,
        metadata.seed,
        metadata.eps_lagr,
        metadata.epsilon
    );

    match algorithm_result {
        Ok(_) => Ok(()),
        Err(err) => Err(PyNotImplementedError::new_err(format!(
            "tube algorithm not implemented ({diagnostics}): {}",
            err
        ))),
    }
}

#[pymodule]
fn rust_viterbo_ffi(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(capacity_hrep, m)?)?;
    Ok(())
}
