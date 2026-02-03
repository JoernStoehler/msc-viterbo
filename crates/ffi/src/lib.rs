//! Python bindings for Viterbo crates via PyO3.
//!
//! Build with: `cd crates/ffi && maturin develop`

use pyo3::prelude::*;

/// Viterbo FFI module
#[pymodule]
fn viterbo_ffi(m: &Bound<'_, PyModule>) -> PyResult<()> {
    m.add("__version__", env!("CARGO_PKG_VERSION"))?;
    Ok(())
}
