//! PyO3 bindings for exposing Rust functionality to Python.
#![allow(clippy::useless_conversion)]

use pyo3::exceptions::{PyRuntimeError, PyValueError};
use pyo3::prelude::*;
use pyo3::types::PyDict;
use rust_viterbo_algorithm::{
    compute_capacity, AlgorithmError, CapacityAlgorithm, CapacityResult, HK2019Algorithm,
    MinkowskiBilliardAlgorithm,
};
use rust_viterbo_geom::{
    symplectic_form, LagrangianDetection, PerturbationMetadata, PolytopeHRep,
    PolytopeValidationError, SymplecticVector,
};

fn map_validation_error(err: PolytopeValidationError) -> PyErr {
    PyValueError::new_err(err.to_string())
}

fn lagrangian_summary(detection: &LagrangianDetection) -> String {
    if let Some(witness) = detection.witness {
        format!(
            "detected=true (pair=({},{}) omega={:.6e}, eps_lagr={:.3e})",
            witness.i, witness.j, witness.omega, detection.eps_lagr
        )
    } else {
        format!("detected=false (eps_lagr={:.3e})", detection.eps_lagr)
    }
}

fn perturbation_summary(perturbation: &Option<PerturbationMetadata>) -> String {
    if let Some(meta) = perturbation {
        format!(
            "applied=true (seed={}, eps_perturb={:.3e}, perturbed_normals={})",
            meta.seed, meta.epsilon, meta.perturbed_count
        )
    } else {
        "applied=false".to_string()
    }
}

/// Build a Python dict from the capacity result.
fn build_result_dict(py: Python<'_>, result: &CapacityResult) -> PyResult<PyObject> {
    let dict = PyDict::new_bound(py);

    dict.set_item("capacity", result.capacity)?;

    // Diagnostics
    let diag = PyDict::new_bound(py);
    diag.set_item("nodes_explored", result.diagnostics.nodes_explored)?;
    diag.set_item("nodes_pruned_empty", result.diagnostics.nodes_pruned_empty)?;
    diag.set_item("nodes_pruned_action", result.diagnostics.nodes_pruned_action)?;
    diag.set_item(
        "nodes_pruned_rotation",
        result.diagnostics.nodes_pruned_rotation,
    )?;
    diag.set_item("best_action_found", result.diagnostics.best_action_found)?;

    if let Some(ref detection) = result.diagnostics.lagrangian_detection {
        diag.set_item("lagrangian", lagrangian_summary(detection))?;
    }
    diag.set_item(
        "perturbation",
        perturbation_summary(&result.diagnostics.perturbation),
    )?;

    dict.set_item("diagnostics", diag)?;

    // Witness (if present)
    if let Some(ref witness) = result.witness {
        let witness_dict = PyDict::new_bound(py);
        witness_dict.set_item("facet_sequence", witness.facet_sequence.clone())?;
        witness_dict.set_item("segment_times", witness.segment_times.clone())?;
        // Convert breakpoints to list of lists
        let breakpoints: Vec<[f64; 4]> = witness
            .breakpoints
            .iter()
            .map(|v| [v.x, v.y, v.z, v.w])
            .collect();
        witness_dict.set_item("breakpoints", breakpoints)?;
        dict.set_item("witness", witness_dict)?;
    } else {
        dict.set_item("witness", py.None())?;
    }

    Ok(dict.into())
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
///
/// Args:
///     normals: List of unit outward normals, each as [f64; 4]
///     heights: List of positive heights
///     unit_tol: Tolerance for unit normal validation (default 1e-9)
///
/// Returns:
///     Dict with keys:
///         - capacity: f64
///         - diagnostics: Dict with search statistics
///         - witness: Optional dict with orbit details
///
/// Raises:
///     ValueError: If input validation fails
///     RuntimeError: If algorithm fails (empty polytope or no valid orbits)
#[pyfunction]
#[pyo3(signature = (normals, heights, unit_tol=1e-9))]
#[allow(clippy::useless_conversion)]
fn tube_capacity_hrep(
    py: Python<'_>,
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
    unit_tol: f64,
) -> PyResult<PyObject> {
    let normals_vec: Vec<SymplecticVector> = normals
        .into_iter()
        .map(|n| SymplecticVector::new(n[0], n[1], n[2], n[3]))
        .collect();
    let polytope = PolytopeHRep::new(normals_vec, heights);
    polytope.validate(unit_tol).map_err(map_validation_error)?;

    match compute_capacity(polytope) {
        Ok(result) => build_result_dict(py, &result),
        Err(AlgorithmError::EmptyPolytope) => Err(PyRuntimeError::new_err(
            "polytope has no non-Lagrangian 2-faces",
        )),
        Err(AlgorithmError::NoValidOrbits) => Err(PyRuntimeError::new_err(
            "no valid periodic orbits found (this may indicate a bug or degenerate input)",
        )),
        Err(AlgorithmError::ValidationError(msg)) => Err(PyValueError::new_err(msg)),
    }
}

/// Compute EHZ capacity using the Minkowski billiard algorithm.
///
/// This algorithm only works for Lagrangian products K = K₁ × K₂.
/// The capacity equals the minimal length of a closed K₂°-billiard in K₁.
///
/// Args:
///     normals: List of unit outward normals, each as [f64; 4]
///     heights: List of positive heights
///     unit_tol: Tolerance for unit normal validation (default 1e-9)
///
/// Returns:
///     Dict with keys:
///         - capacity: f64
///         - diagnostics: Dict with search statistics
///         - witness: Optional dict with orbit details
///
/// Raises:
///     ValueError: If input validation fails or polytope is not a Lagrangian product
///     RuntimeError: If algorithm fails
#[pyfunction]
#[pyo3(signature = (normals, heights, unit_tol=1e-9))]
fn billiard_capacity_hrep(
    py: Python<'_>,
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
    unit_tol: f64,
) -> PyResult<PyObject> {
    let normals_vec: Vec<SymplecticVector> = normals
        .into_iter()
        .map(|n| SymplecticVector::new(n[0], n[1], n[2], n[3]))
        .collect();
    let polytope = PolytopeHRep::new(normals_vec, heights);
    polytope.validate(unit_tol).map_err(map_validation_error)?;

    let algo = MinkowskiBilliardAlgorithm::new();

    // Check if input is supported
    if let Err(msg) = algo.supports_input(&polytope) {
        return Err(PyValueError::new_err(msg));
    }

    match algo.compute(polytope) {
        Ok(result) => build_result_dict(py, &result),
        Err(AlgorithmError::EmptyPolytope) => Err(PyRuntimeError::new_err(
            "polytope has no non-Lagrangian 2-faces",
        )),
        Err(AlgorithmError::NoValidOrbits) => {
            Err(PyRuntimeError::new_err("no valid periodic orbits found"))
        }
        Err(AlgorithmError::ValidationError(msg)) => Err(PyValueError::new_err(msg)),
    }
}

/// Compute EHZ capacity using the HK2019 quadratic programming algorithm.
///
/// This algorithm works for any 4D polytope but has O(F!) complexity in the
/// number of facets. It is limited to polytopes with at most 10 facets.
///
/// Args:
///     normals: List of unit outward normals, each as [f64; 4]
///     heights: List of positive heights
///     unit_tol: Tolerance for unit normal validation (default 1e-9)
///
/// Returns:
///     Dict with keys:
///         - capacity: f64
///         - diagnostics: Dict with search statistics
///         - witness: Optional dict with orbit details
///
/// Raises:
///     ValueError: If input validation fails or polytope has too many facets
///     RuntimeError: If algorithm fails or times out
#[pyfunction]
#[pyo3(signature = (normals, heights, unit_tol=1e-9))]
fn hk2019_capacity_hrep(
    py: Python<'_>,
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
    unit_tol: f64,
) -> PyResult<PyObject> {
    let normals_vec: Vec<SymplecticVector> = normals
        .into_iter()
        .map(|n| SymplecticVector::new(n[0], n[1], n[2], n[3]))
        .collect();
    let polytope = PolytopeHRep::new(normals_vec, heights);
    polytope.validate(unit_tol).map_err(map_validation_error)?;

    let algo = HK2019Algorithm::new();

    // Check if input is supported
    if let Err(msg) = algo.supports_input(&polytope) {
        return Err(PyValueError::new_err(msg));
    }

    match algo.compute(polytope) {
        Ok(result) => build_result_dict(py, &result),
        Err(AlgorithmError::EmptyPolytope) => Err(PyRuntimeError::new_err(
            "polytope has no non-Lagrangian 2-faces",
        )),
        Err(AlgorithmError::NoValidOrbits) => {
            Err(PyRuntimeError::new_err("no valid periodic orbits found"))
        }
        Err(AlgorithmError::ValidationError(msg)) => Err(PyValueError::new_err(msg)),
    }
}

#[pymodule]
fn rust_viterbo_ffi(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(symplectic_form_4d, m)?)?;
    m.add_function(wrap_pyfunction!(tube_capacity_hrep, m)?)?;
    m.add_function(wrap_pyfunction!(billiard_capacity_hrep, m)?)?;
    m.add_function(wrap_pyfunction!(hk2019_capacity_hrep, m)?)?;
    Ok(())
}
