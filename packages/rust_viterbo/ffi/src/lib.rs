//! PyO3 bindings for exposing Rust functionality to Python.
#![allow(clippy::useless_conversion)]

use pyo3::exceptions::{PyNotImplementedError, PyValueError};
use pyo3::prelude::*;
use rust_viterbo_algorithm::{
    tube_capacity_hrep as tube_capacity_hrep_algorithm, AlgorithmError, CapacityDiagnostics,
};
use rust_viterbo_geom::{
    detect_near_lagrangian, perturb_polytope_normals, symplectic_form, PolytopeHRep,
    PolytopeValidationError, SymplecticVector,
};

fn map_validation_error(err: PolytopeValidationError) -> PyErr {
    PyValueError::new_err(err.to_string())
}

fn lagrangian_summary(detection: &rust_viterbo_geom::LagrangianDetection) -> String {
    if let Some(witness) = detection.witness {
        format!(
            "detected=true (pair=({},{}) omega={:.6e}, eps_lagr={:.3e})",
            witness.i, witness.j, witness.omega, detection.eps_lagr
        )
    } else {
        format!("detected=false (eps_lagr={:.3e})", detection.eps_lagr)
    }
}

/// Return the symplectic form ω(x,y) in R^4.
#[pyfunction]
fn symplectic_form_4d(a: [f64; 4], b: [f64; 4]) -> f64 {
    symplectic_form(
        SymplecticVector::new(a[0], a[1], a[2], a[3]),
        SymplecticVector::new(b[0], b[1], b[2], b[3]),
    )
}

/// Entry point for the tube capacity algorithm (H-rep only).
#[pyfunction]
#[pyo3(signature = (normals, heights, eps_lagr=1e-9, eps_perturb=1e-6, seed=0, unit_tol=1e-9))]
#[allow(clippy::useless_conversion)]
fn tube_capacity_hrep(
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
    eps_lagr: f64,
    eps_perturb: f64,
    seed: u64,
    unit_tol: f64,
) -> PyResult<PyObject> {
    let normals_vec: Vec<SymplecticVector> = normals
        .into_iter()
        .map(|n| SymplecticVector::new(n[0], n[1], n[2], n[3]))
        .collect();
    let polytope = PolytopeHRep::new(normals_vec, heights);
    polytope.validate(unit_tol).map_err(map_validation_error)?;

    let eps_feas = 1e-9;
    let eps_dedup = 1e-8;
    let lagrangian_detection = detect_near_lagrangian(&polytope, eps_lagr, eps_feas, eps_dedup);
    let (polytope, perturbation) = if lagrangian_detection.detected {
        let outcome = perturb_polytope_normals(&polytope, seed, eps_perturb);
        (outcome.polytope, Some(outcome.metadata))
    } else {
        (polytope, None)
    };

    let diagnostics = CapacityDiagnostics {
        eps_lagr,
        lagrangian_detection,
        perturbation,
    };

    match tube_capacity_hrep_algorithm(&polytope, diagnostics) {
        Ok(_result) => Err(PyNotImplementedError::new_err(
            "tube capacity algorithm not implemented yet (unexpected success path)",
        )),
        Err(AlgorithmError::NotImplemented { diagnostics }) => {
            let lagrangian = lagrangian_summary(&diagnostics.lagrangian_detection);
            let perturbation = if let Some(meta) = diagnostics.perturbation {
                format!(
                    "applied=true (seed={}, eps_perturb={:.3e}, perturbed_normals={})",
                    meta.seed, meta.epsilon, meta.perturbed_count
                )
            } else {
                "applied=false".to_string()
            };
            Err(PyNotImplementedError::new_err(format!(
                "tube capacity algorithm not implemented; lagrangian {lagrangian}; perturbation {perturbation}"
            )))
        }
    }
}

#[pymodule]
fn rust_viterbo_ffi(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(symplectic_form_4d, m)?)?;
    m.add_function(wrap_pyfunction!(tube_capacity_hrep, m)?)?;
    Ok(())
}
