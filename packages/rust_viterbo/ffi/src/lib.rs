//! Python FFI bindings for EHZ capacity algorithms.
//!
//! This crate provides Python access to Rust implementations of algorithms
//! for computing the Ekeland-Hofer-Zehnder (EHZ) capacity of convex polytopes.
//!
//! ## Implemented Algorithms
//!
//! - **HK2017**: Haim-Kislev's combinatorial formula (fully implemented)
//!
//! ## Legacy/Archived Algorithms
//!
//! The following were previously implemented but are now archived stubs:
//! - `tube_capacity_hrep`: Archived at tag `v0.1.0-archive`
//! - `billiard_capacity_hrep`: Archived at tag `v0.1.0-archive`

use nalgebra::Vector4;
use pyo3::exceptions::{PyNotImplementedError, PyValueError};
use pyo3::prelude::*;

use hk2017::{hk2017_capacity, Hk2017Config, Hk2017Error, PolytopeHRep};

const ARCHIVED_MSG: &str =
    "Archived. See docs/developer-spec.md to re-implement, or checkout tag v0.1.0-archive";

/// Return the symplectic form omega(x, y) in R^4.
///
/// The symplectic form is defined as:
/// omega(x, y) = x[0]*y[2] + x[1]*y[3] - x[2]*y[0] - x[3]*y[1]
///
/// where x = (q1, q2, p1, p2) and y = (q1', q2', p1', p2').
///
/// # Arguments
/// * `a` - First vector [q1, q2, p1, p2]
/// * `b` - Second vector [q1', q2', p1', p2']
///
/// # Returns
/// The symplectic form value omega(a, b)
#[pyfunction]
fn symplectic_form_4d(a: [f64; 4], b: [f64; 4]) -> f64 {
    hk2017::symplectic_form(
        &Vector4::new(a[0], a[1], a[2], a[3]),
        &Vector4::new(b[0], b[1], b[2], b[3]),
    )
}

/// Compute EHZ capacity using the HK2017 algorithm.
///
/// This implements the combinatorial formula from Haim-Kislev's paper
/// "On the Symplectic Size of Convex Polytopes" (arXiv:1712.03494).
///
/// # Arguments
/// * `normals` - List of unit outward normal vectors for each facet
/// * `heights` - List of signed distances from origin to each facet (must be positive)
///
/// # Returns
/// A dictionary with:
/// - `capacity`: The computed EHZ capacity
/// - `q_max`: The maximum Q value achieved
/// - `optimal_permutation`: Indices of facets in the optimal ordering
/// - `permutations_evaluated`: Number of permutations checked
/// - `permutations_rejected`: Number of permutations rejected
///
/// # Raises
/// * `ValueError` if the polytope is invalid (non-unit normals, non-positive heights, etc.)
///
/// # Example
/// ```python
/// import rust_viterbo_ffi as ffi
///
/// # Tesseract [-1, 1]^4
/// normals = [
///     [1, 0, 0, 0], [-1, 0, 0, 0],
///     [0, 1, 0, 0], [0, -1, 0, 0],
///     [0, 0, 1, 0], [0, 0, -1, 0],
///     [0, 0, 0, 1], [0, 0, 0, -1],
/// ]
/// heights = [1.0] * 8
///
/// result = ffi.hk2017_capacity_hrep(normals, heights)
/// print(f"Capacity: {result['capacity']}")  # Should be 4.0
/// ```
///
/// # Warning
///
/// This implementation assumes the global maximum of Q occurs at an interior
/// point. If the true maximum is on the boundary, the result may be incorrect.
/// See the hk2017 crate documentation for details.
#[pyfunction]
#[pyo3(signature = (normals, heights, use_graph_pruning=false))]
fn hk2017_capacity_hrep(
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
    use_graph_pruning: bool,
) -> PyResult<Hk2017ResultPy> {
    // Convert to nalgebra vectors
    let normals_vec: Vec<Vector4<f64>> = normals
        .into_iter()
        .map(|n| Vector4::new(n[0], n[1], n[2], n[3]))
        .collect();

    let polytope = PolytopeHRep::new(normals_vec, heights);

    // Both variants pass all tests and share the QP solver code.
    // Naive is default for simplicity; GraphPruned is ~20x faster for tesseract.
    let config = if use_graph_pruning {
        Hk2017Config::graph_pruned()
    } else {
        Hk2017Config::naive()
    };

    match hk2017_capacity(&polytope, &config) {
        Ok(result) => Ok(Hk2017ResultPy {
            capacity: result.capacity,
            q_max: result.q_max,
            optimal_permutation: result.optimal_permutation,
            optimal_beta: result.optimal_beta,
            permutations_evaluated: result.permutations_evaluated,
            permutations_rejected: result.permutations_rejected,
        }),
        Err(e) => Err(convert_error(e)),
    }
}

/// Result of HK2017 capacity computation.
#[pyclass]
#[derive(Clone)]
struct Hk2017ResultPy {
    #[pyo3(get)]
    capacity: f64,
    #[pyo3(get)]
    q_max: f64,
    #[pyo3(get)]
    optimal_permutation: Vec<usize>,
    #[pyo3(get)]
    optimal_beta: Vec<f64>,
    #[pyo3(get)]
    permutations_evaluated: usize,
    #[pyo3(get)]
    permutations_rejected: usize,
}

#[pymethods]
impl Hk2017ResultPy {
    fn __repr__(&self) -> String {
        format!(
            "Hk2017Result(capacity={}, q_max={}, permutation={:?})",
            self.capacity, self.q_max, self.optimal_permutation
        )
    }
}

/// Convert Hk2017Error to PyErr.
fn convert_error(e: Hk2017Error) -> PyErr {
    match e {
        Hk2017Error::InvalidPolytope(msg) => PyValueError::new_err(format!("Invalid polytope: {}", msg)),
        Hk2017Error::NoFeasibleInteriorPoint { checked, rejected, .. } => {
            PyValueError::new_err(format!(
                "No feasible interior critical point found ({} checked, {} rejected). \
                 The maximum may be on the boundary, which this implementation cannot find.",
                checked, rejected
            ))
        }
        Hk2017Error::NoPositiveQ { checked } => {
            PyValueError::new_err(format!(
                "All {} permutations have non-positive Q value",
                checked
            ))
        }
        Hk2017Error::SingularKkt { permutation } => {
            PyValueError::new_err(format!(
                "KKT system is singular for permutation {:?}",
                permutation
            ))
        }
        Hk2017Error::NumericalInstability(msg) => {
            PyValueError::new_err(format!("Numerical instability: {}", msg))
        }
        Hk2017Error::VerificationFailed(msg) => {
            PyValueError::new_err(format!("Result verification failed: {}", msg))
        }
    }
}

// ============================================================================
// Legacy/Archived Functions
// ============================================================================

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

/// LEGACY: Compute EHZ capacity using the HK2019 quadratic programming algorithm.
///
/// This is an alias for `hk2017_capacity_hrep` for backwards compatibility.
/// The algorithm is from HK2017 (arXiv date), published in GAFA 2019.
#[pyfunction]
#[pyo3(signature = (normals, heights, _unit_tol=1e-9))]
fn hk2019_capacity_hrep(
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
    _unit_tol: f64,
) -> PyResult<f64> {
    // Delegate to hk2017 and return just the capacity for backwards compatibility
    let result = hk2017_capacity_hrep(normals, heights, false)?;
    Ok(result.capacity)
}

#[pymodule]
fn rust_viterbo_ffi(m: &Bound<'_, PyModule>) -> PyResult<()> {
    // Core functions
    m.add_function(wrap_pyfunction!(symplectic_form_4d, m)?)?;
    m.add_function(wrap_pyfunction!(hk2017_capacity_hrep, m)?)?;

    // Legacy/archived functions
    m.add_function(wrap_pyfunction!(tube_capacity_hrep, m)?)?;
    m.add_function(wrap_pyfunction!(billiard_capacity_hrep, m)?)?;
    m.add_function(wrap_pyfunction!(hk2019_capacity_hrep, m)?)?;

    // Result class
    m.add_class::<Hk2017ResultPy>()?;

    Ok(())
}
