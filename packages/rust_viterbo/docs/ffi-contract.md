# Python FFI (PyO3 + maturin)
- Purpose: Provide Python bindings for the high performance Rust library `rust_viterbo`.

## Build
- `cd packages/python_viterbo && uv run maturin develop --manifest-path ../rust_viterbo/Cargo.toml`
- Test with: `cd packages/python_viterbo && uv run pytest -q tests/smoke`

## FFI Contract (MVP, owner-approved 2025-12-22)

The FFI is intended to be a thin boundary around the Rust implementation. The main goals are:

- callers are explicit about what algorithm is run and what assumptions are made,
- inputs are validated at the boundary (even in release builds),
- outputs include a witness (so Python can validate/plot/store results).

### Main algorithm call

Owner decision (KISS/YAGNI): the main capacity routine must require the caller to provide **both**
representations of the polytope:

- irredundant H-rep: outward unit normals \(n_i \in \mathbb{R}^4\) and heights \(h_i>0\),
- irredundant V-rep: vertices in \(\mathbb{R}^4\).

Rationale: no “magic” conversions inside the called function; callers should consciously choose their
pipeline and costs.

### Optional helper calls

Conversions between H-rep and V-rep are allowed as **separate** explicit FFI calls (or Python-side steps),
but must not be performed implicitly by the main algorithm call.

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
