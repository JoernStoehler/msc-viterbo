# Python FFI (PyO3 + maturin)
- Purpose: Provide Python bindings for the high performance Rust library `rust_viterbo`.

## Build
- `cd packages/python_viterbo && uv run maturin develop --manifest-path ../rust_viterbo/Cargo.toml`
- Test with: `cd packages/python_viterbo && uv run pytest -q tests/smoke`

## FFI Contract (MVP, working contract)

Locked constraints were confirmed on **2025-12-22**; the **main input contract** was updated on
**2025-12-24**.

The FFI is intended to be a thin boundary around the Rust implementation. The main goals are:

- callers are explicit about what algorithm is run and what assumptions are made,
- inputs are validated at the boundary (even in release builds),
- outputs include a witness (so Python can validate/plot/store results).

### Main algorithm call

Owner decision (2025-12-24): the main capacity routine takes **only** an irredundant H-rep:

- outward unit normals \(n_i \in \mathbb{R}^4\) and heights \(h_i>0\).

The FFI entrypoint should be a wrapper that:

1) validates inputs and conventions,  
2) detects (numerically) Lagrangian 2-faces and applies a seeded perturbation (heights fixed) if needed,  
3) runs the tube algorithm, and  
4) returns `capacity + witness + diagnostics` including perturbation metadata.

### Optional helper calls

If conversions (H↔V) are needed for secondary computations (e.g. volume/systolic ratio) they may be
implemented as internal Rust helpers or as separate explicit FFI calls. The main capacity call itself
remains H-rep-only.

### Validation at the boundary

FFI entrypoints should validate (and return structured errors) for:

- correct shapes and finite floats,
- unit normals (within tolerance) and positive heights,
- irredundancy assumptions (where cheaply checkable),
- bounded/full-dimensional polytope and \(0 \in \mathrm{int}(K)\) (as feasible).

## Output payload expectations

The capacity output should include a witness orbit, at least:

- `breakpoints` (cyclic points in \(\mathbb{R}^4\)).

Preferred (redundant) fields for datasets/debugging:

- `segment_times`, `segment_facets`, diagnostics, and perturbation metadata (seed/epsilon/eps_lagr/etc.).

## Code Conventions
- Keep PyO3 wrappers thin; convert types near the boundary.
- Avoid breaking Python-facing APIs without coordinating with python_viterbo.
- Avoid complex ownership/lifetime logic in PyO3 code.
