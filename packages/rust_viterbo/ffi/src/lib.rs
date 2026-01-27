//! Python FFI bindings for EHZ capacity algorithms.
//!
//! This crate provides Python access to Rust implementations of algorithms
//! for computing the Ekeland-Hofer-Zehnder (EHZ) capacity of convex polytopes.
//!
//! ## Implemented Algorithms
//!
//! - **HK2017**: Haim-Kislev's combinatorial formula from "On the Symplectic
//!   Size of Convex Polytopes" (arXiv:1712.03494, published GAFA 2019).
//!
//! ## Usage from Python
//!
//! ```python
//! import rust_viterbo_ffi as ffi
//!
//! # Tesseract [-1, 1]^4
//! normals = [
//!     [1, 0, 0, 0], [-1, 0, 0, 0],
//!     [0, 1, 0, 0], [0, -1, 0, 0],
//!     [0, 0, 1, 0], [0, 0, -1, 0],
//!     [0, 0, 0, 1], [0, 0, 0, -1],
//! ]
//! heights = [1.0] * 8
//!
//! result = ffi.hk2017_capacity_hrep(normals, heights)
//! print(f"Capacity: {result.capacity}")  # 4.0
//! ```

// Clippy false positive with PyO3's PyResult type annotations
#![allow(clippy::useless_conversion)]

use nalgebra::Vector4;
use pyo3::exceptions::PyValueError;
use pyo3::prelude::*;

use hk2017::{hk2017_capacity, Hk2017Config, Hk2017Error, PolytopeHRep};

/// Compute EHZ capacity using the HK2017 algorithm.
///
/// Implements the combinatorial formula from Haim-Kislev's paper
/// "On the Symplectic Size of Convex Polytopes" (arXiv:1712.03494).
///
/// # Arguments
/// * `normals` - Unit outward normal vectors for each facet
/// * `heights` - Signed distances from origin to each facet (must be positive)
/// * `use_graph_pruning` - If true, use graph-based cycle enumeration (faster)
///
/// # Returns
/// An `Hk2017Result` with:
/// - `capacity`: The computed EHZ capacity
/// - `q_max`: The maximum Q value achieved
/// - `optimal_permutation`: Indices of facets in the optimal ordering
/// - `optimal_beta`: The beta values at the optimum
/// - `permutations_evaluated`: Number of permutations checked
/// - `permutations_rejected`: Number of permutations rejected by pruning
///
/// # Raises
/// * `ValueError` if the polytope is invalid (non-unit normals, non-positive heights, etc.)
///
/// # Warning
/// This implementation assumes the global maximum of Q occurs at an interior
/// point. If the true maximum is on the boundary, the result may be incorrect.
/// See the hk2017 crate documentation for details.
#[pyfunction]
#[pyo3(signature = (normals, heights, use_graph_pruning=false))]
fn hk2017_capacity_hrep(
    normals: Vec<[f64; 4]>,
    heights: Vec<f64>,
    use_graph_pruning: bool,
) -> PyResult<Hk2017Result> {
    let normals_vec: Vec<Vector4<f64>> = normals
        .into_iter()
        .map(|n| Vector4::new(n[0], n[1], n[2], n[3]))
        .collect();

    let polytope = PolytopeHRep::new(normals_vec, heights);

    let config = if use_graph_pruning {
        Hk2017Config::graph_pruned()
    } else {
        Hk2017Config::naive()
    };

    match hk2017_capacity(&polytope, &config) {
        Ok(result) => Ok(Hk2017Result {
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
struct Hk2017Result {
    /// The computed EHZ capacity.
    #[pyo3(get)]
    capacity: f64,

    /// The maximum Q value achieved (capacity = 4/q_max).
    #[pyo3(get)]
    q_max: f64,

    /// Indices of facets in the optimal cyclic ordering.
    #[pyo3(get)]
    optimal_permutation: Vec<usize>,

    /// The beta values (time spent on each facet) at the optimum.
    #[pyo3(get)]
    optimal_beta: Vec<f64>,

    /// Number of permutations evaluated.
    #[pyo3(get)]
    permutations_evaluated: usize,

    /// Number of permutations rejected by pruning criteria.
    #[pyo3(get)]
    permutations_rejected: usize,
}

#[pymethods]
impl Hk2017Result {
    fn __repr__(&self) -> String {
        format!(
            "Hk2017Result(capacity={:.6}, q_max={:.6}, permutation={:?})",
            self.capacity, self.q_max, self.optimal_permutation
        )
    }
}

/// Compute the symplectic form ω(a, b) in R⁴.
///
/// The standard symplectic form is:
///   ω(x, y) = x₁y₃ + x₂y₄ - x₃y₁ - x₄y₂
///
/// where x = (q₁, q₂, p₁, p₂) and y = (q₁', q₂', p₁', p₂').
///
/// # Arguments
/// * `a` - First vector [q₁, q₂, p₁, p₂]
/// * `b` - Second vector [q₁', q₂', p₁', p₂']
///
/// # Returns
/// The symplectic form value ω(a, b).
#[pyfunction]
fn symplectic_form_4d(a: [f64; 4], b: [f64; 4]) -> f64 {
    hk2017::symplectic_form(
        &Vector4::new(a[0], a[1], a[2], a[3]),
        &Vector4::new(b[0], b[1], b[2], b[3]),
    )
}

/// Convert Hk2017Error to PyErr.
fn convert_error(e: Hk2017Error) -> PyErr {
    match e {
        Hk2017Error::InvalidPolytope(msg) => {
            PyValueError::new_err(format!("Invalid polytope: {}", msg))
        }
        Hk2017Error::NoFeasibleInteriorPoint {
            checked, rejected, ..
        } => PyValueError::new_err(format!(
            "No feasible interior critical point found ({} checked, {} rejected). \
             The maximum may be on the boundary, which this implementation cannot find.",
            checked, rejected
        )),
        Hk2017Error::NoPositiveQ { checked } => PyValueError::new_err(format!(
            "All {} permutations have non-positive Q value",
            checked
        )),
        Hk2017Error::SingularKkt { permutation } => PyValueError::new_err(format!(
            "KKT system is singular for permutation {:?}",
            permutation
        )),
        Hk2017Error::NumericalInstability(msg) => {
            PyValueError::new_err(format!("Numerical instability: {}", msg))
        }
        Hk2017Error::VerificationFailed(msg) => {
            PyValueError::new_err(format!("Result verification failed: {}", msg))
        }
    }
}

/// Python module for EHZ capacity algorithms.
#[pymodule]
fn rust_viterbo_ffi(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(hk2017_capacity_hrep, m)?)?;
    m.add_function(wrap_pyfunction!(symplectic_form_4d, m)?)?;
    m.add_class::<Hk2017Result>()?;
    Ok(())
}
