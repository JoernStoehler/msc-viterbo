# Billiard Crate Cleanup Task

Clean up billiard crate contamination before thesis writing.

## Context

The billiard crate was implemented by agents who created band-aid fixes and reverse-engineered documentation. The implementation is broken (triangle×triangle gives wrong answers) and its documentation/tests would contaminate thesis writing by causing agents to describe the implementation rather than cite literature theorems.

## Goal

1. Move general 2D convex geometry code to geom crate (not billiard-specific)
2. Delete billiard algorithm implementation and contaminated documentation
3. Clean up FFI exports and TODO.md

## Tasks

### Part 1: Move Polygon2D to geom crate

1. Create `packages/rust_viterbo/geom/src/polygon2d.rs`

2. Move from `packages/rust_viterbo/billiard/src/types.rs`:
   - `Polygon2D` struct (lines 18-109)
   - Keep dependency on `nalgebra::Vector2`
   - Tests from types.rs::tests module: `test_square_validation`, `test_pentagon_validation`, `test_point_on_edge`

3. Move entire `packages/rust_viterbo/billiard/src/polygon.rs` to geom/src/polygon2d.rs:
   - Merge with Polygon2D struct as impl blocks
   - Include all methods: `from_vertices`, `regular`, `regular_pentagon`, `square`, `rotate`, `scale`
   - Include functions: `support_function`, `t_dual_length`
   - Include all tests

4. Update `packages/rust_viterbo/geom/src/lib.rs`:
   - Add `pub mod polygon2d;`
   - Add `pub use polygon2d::{Polygon2D, support_function, t_dual_length};`

5. Update `packages/rust_viterbo/geom/Cargo.toml`:
   - Add `nalgebra = "0.33"` to dependencies if not present

6. Run tests: `cd packages/rust_viterbo/geom && cargo test`

### Part 2: Delete billiard crate

1. Delete entire directory: `rm -rf packages/rust_viterbo/billiard/`

2. Update `packages/rust_viterbo/Cargo.toml`:
   - Remove `"billiard"` from workspace members list

3. Remove from `packages/rust_viterbo/ffi/Cargo.toml`:
   - Remove `billiard = { path = "../billiard" }` from dependencies

4. Update `packages/rust_viterbo/ffi/src/lib.rs`:
   - Remove `billiard_capacity_from_polygons()` function and all billiard imports

5. Update `packages/python_viterbo/src/rust_viterbo_ffi.pyi`:
   - Remove billiard type stubs (if any)

### Part 3: Clean up TODO.md

1. Delete lines 27-106 in `TODO.md` (Agent 3's unverified observations)

2. Verify deletion removed the entire "⚠️ UNVERIFIED OBSERVATIONS" section

### Part 4: Validation

1. Build workspace: `cd packages/rust_viterbo && cargo build`

2. Run all tests: `cargo test --workspace`

3. Verify geom tests pass with new polygon2d module

4. Verify FFI builds without billiard dependency

5. Check no remaining references: `grep -r "billiard" packages/rust_viterbo/`
   - Expected matches: only git history and comments about "billiard algorithm to be implemented"

## Success Criteria

- [ ] Polygon2D available in geom crate with all tests passing
- [ ] billiard/ directory deleted
- [ ] FFI compiles without billiard dependency
- [ ] Workspace builds and all tests pass
- [ ] No grep matches for "billiard" except expected references
- [ ] TODO.md cleaned of Agent 3's observations

## Important Notes

- Do NOT archive or keep any billiard algorithm implementation
- Do NOT keep TEST_SPEC.md or test comparison results
- LagrangianProduct and to_hrep() get deleted with the crate (not useful without algorithm)
- Git history preserves everything if needed later

## Commit Message

After completion, commit with:

```
refactor: move Polygon2D to geom, delete broken billiard implementation

Moves general 2D convex geometry to geom crate. Deletes billiard algorithm
implementation with Agent 3's band-aid fixes and reverse-engineered docs to
prevent thesis contamination. Will reimplement from thesis spec after
algorithms.tex section complete.
```
