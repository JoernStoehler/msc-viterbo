# Developing in Lean
- Package: `packages/lean_viterbo`
- Goal: Formalizing our mathematical results in Lean4 using mathlib4 for verification.
- Toolchain: Lean 4.25.0 (elan default set to `leanprover/lean4:v4.25.0`), mathlib pinned via lakefile. It's a recent stable version.
- Caching: We cache dependencies via the symlink `.lake/packages -> /workspaces/worktrees/shared/lean/packages`. Build output is shared at `/workspaces/worktrees/shared/lean/build-global` via the `.lake/build` symlink.
- Commands: `lake build -q` for normal work; search the mathlib4 docs/source as needed. Run the root prep script `scripts/worktree-prepare.sh <worktree>` to link caches before building.
- Quality: We must pass `lake build` without errors. `sorry` in proofs is allowed temporarily, or with explicit documented permission from the project owner. We target the same quality as mathlib4 itself. We document the why behind design decisions in code comments, and reference the thesis writeup's notation where definitions correspond or where they differ.

## Tips
- The syntax of mathlib changed a lot, and agents have almost-right-but-wrong intuitions. Expect to spend time reading mathlib4 docs and source code while iterating until you get the right types and lemmas.
- To not be overwhelmed by errors, write one file and fix its errors before proceeding to the next.
- Do not revert back and forth when choosing a definition; ask the project owner for help if you are unsure which definition is doable and most useful for later work.
- We want Lean code to read similar to our thesis writeup. Pick similar types and notation where possible, and discuss differences with the project owner, and document the differences and rationale in code comments.
