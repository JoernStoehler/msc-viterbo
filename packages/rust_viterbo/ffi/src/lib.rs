//! PyO3 bindings for exposing Rust functionality to Python.

use pyo3::prelude::*;
use rust_viterbo_geom::{symplectic_form, SymplecticVector};

/// Return the oriented symplectic area spanned by two vectors.
#[pyfunction]
fn oriented_area(ax: f64, ay: f64, bx: f64, by: f64) -> f64 {
    symplectic_form(SymplecticVector::new(ax, ay), SymplecticVector::new(bx, by))
}

#[pymodule]
fn rust_viterbo_ffi(_py: Python<'_>, m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add_function(wrap_pyfunction!(oriented_area, m)?)?;
    Ok(())
}
