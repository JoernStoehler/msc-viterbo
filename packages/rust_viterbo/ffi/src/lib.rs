//! PyO3 bindings for exposing Rust functionality to Python.
#![allow(clippy::useless_conversion)]

use pyo3::exceptions::{PyNotImplementedError, PyValueError};
use pyo3::prelude::*;
use rust_viterbo_algorithm::{tube_capacity_hrep, AlgorithmError};
use rust_viterbo_geom::{perturb_hrep_if_lagrangian, Polytope4HRep, SymplecticVector};

const DEFAULT_EPS_LAGR: f64 = 1e-12;
const DEFAULT_EPS_PERTURB: f64 = 1e-6;
const DEFAULT_UNIT_TOL: f64 = 1e-8;
const DEFAULT_SEED: u64 = 0;

fn parse_normals(normals: Vec<Vec<f64>>) -> PyResult<Vec<SymplecticVector>> {
    let mut parsed = Vec::with_capacity(normals.len());
    for (idx, normal) in normals.into_iter().enumerate() {
        if normal.len() != 4 {
            return Err(PyValueError::new_err(format!(
                "normal {idx} has length {} (expected 4)",
                normal.len()
            )));
        }
        parsed.push(SymplecticVector::new(
            normal[0], normal[1], normal[2], normal[3],
        ));
    }
    Ok(parsed)
}

/// H-rep-only capacity entrypoint (tube algorithm stub).
#[pyfunction]
#[pyo3(signature = (normals, heights, eps_lagr=None, eps_perturb=None, seed=None, unit_tol=None))]
fn capacity_hrep(
    normals: Vec<Vec<f64>>,
    heights: Vec<f64>,
    eps_lagr: Option<f64>,
    eps_perturb: Option<f64>,
    seed: Option<u64>,
    unit_tol: Option<f64>,
) -> PyResult<f64> {
    let eps_lagr = eps_lagr.unwrap_or(DEFAULT_EPS_LAGR);
    let eps_perturb = eps_perturb.unwrap_or(DEFAULT_EPS_PERTURB);
    let seed = seed.unwrap_or(DEFAULT_SEED);
    let unit_tol = unit_tol.unwrap_or(DEFAULT_UNIT_TOL);

    let normals = parse_normals(normals)?;
    let hrep = Polytope4HRep::new(normals, heights);
    if let Err(errors) = hrep.validate(unit_tol) {
        return Err(PyValueError::new_err(format!(
            "H-rep validation failed:\n{errors}"
        )));
    }

    let (perturbed, metadata) = perturb_hrep_if_lagrangian(&hrep, eps_lagr, eps_perturb, seed);
    match tube_capacity_hrep(&perturbed) {
        Ok(value) => Ok(value),
        Err(AlgorithmError::NotImplemented) => Err(PyNotImplementedError::new_err(format!(
            "tube capacity algorithm not implemented yet; lagrangian_detected={}, perturbed_count={}, seed={}, eps_lagr={}, eps_perturb={}, unit_tol={}",
            metadata.lagrangian_detected,
            metadata.perturbed_count,
            metadata.seed,
            eps_lagr,
            metadata.epsilon,
            unit_tol,
        ))),
    }
}

#[pymodule]
fn rust_viterbo_ffi(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(capacity_hrep, m)?)?;
    Ok(())
}
