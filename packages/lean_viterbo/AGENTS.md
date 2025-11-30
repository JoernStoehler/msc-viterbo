# AGENTS – Lean Viterbo Package

You are in `packages/lean_viterbo/`, which contains Lean4 code for formalizing key parts of the project and (eventually) certificate verification.

## Goals

- Formalize the correctness of the main algorithm, in particular lemmas about closed characteristics and minimum-action closed characteristics on 4D polytopes.
- Where appropriate, use axioms for standard low-level differential geometry instead of reproving everything from scratch.
- Optionally, implement a certificate verifier that can confirm for each polytope in the dataset that a computed minimum orbit is indeed minimal and an orbit.

## Layout

- `lakefile.lean` – Lake project definition.
- `lean-toolchain` – Lean version pin.
- `ProbingViterbo` namespace under `ProbingViterbo/` (to be refined as the project evolves).

## Architecture context

- Lean proofs justify algorithmic steps implemented in `packages/rust_viterbo`. Keep theorem/lemma names aligned with the Rust modules they certify.
- The future certificate verifier will ingest artifacts emitted by `packages/python_viterbo` experiments; design data formats in collaboration with that package.
- When Lean code depends on external libraries, document the rationale in comments so the Dockerfile/elan pins remain coherent.

## Tooling and commands

- Build: `cd packages/lean_viterbo && lake build -q` (quiet but keeps warnings; use plain `lake build` if you need full progress noise).
- REPL/editor: `lake env lean` (or your editor integration) for interactive development.
- Fast startup: `scripts/worktree-prepare.sh --lean` (default root prep already includes it). It links `.lake/packages` to `/workspaces/worktrees/shared/lean/packages`, pulls mathlib via `lake exe cache get`, and stops (no build). Run the build only when you actually touch Lean code.
- Docs: `scripts/build-docs.sh` symlinks `packages/lean_viterbo/docbuild/.lake/build` to `/workspaces/worktrees/shared/lean/docbuild-build` so doc-gen4 output is reused across worktrees; the first run populates the shared folder.
### Lean build and docs cache (global)

- Build output (`.lake/build`) is shared across worktrees at `/workspaces/worktrees/shared/lean/build-global` via the symlink `packages/lean_viterbo/.lake/build`.
- Doc output stays in that shared tree at `.lake/build/doc`; `stage-hub.sh` stages from there.
- Builds/docs use shared deps in `.lake/packages` (already symlinked) and a shared docbuild build cache.
- Concurrency: acquire the shared lock when running Lean builds/docs: `flock /workspaces/worktrees/shared/lean/locks/lean-docs.lock -- lake -Kdoc=on build ProbingViterbo:docs`. `scripts/build-docs.sh` already wraps the doc build with this lock.
- Clean rebuild (only if the cache is bad): remove `/workspaces/worktrees/shared/lean/build-global/doc` and rerun `scripts/build-docs.sh`.

Docs build policy
- Shared cache makes warm Lean doc builds fast (~30s). A cold build (empty cache) can take ~20–25m.
- `packages/docs-site/scripts/docs-publish.sh` now builds Lean docs by default; skip via `SKIP_LEAN=1` or `LEAN_DOCS=0` if you know the cache is cold and time is tight.
- You can run `packages/lean_viterbo/scripts/build-docs.sh` anytime for quick verification; it keeps outputs in the shared cache.

### Mathlib cache warning (harmless)

Mathlib’s post-update hook compares `Lean.versionString` to the `lean-toolchain` line with a naive string check. With our toolchain (`leanprover/lean4:v4.25.0`) it may print:

```
Not running `lake exe cache get` yet, as the `lake` version does not match the toolchain version in the project.
You should run `lake exe cache get` manually.
```

This is a known upstream string-comparison quirk, not a real mismatch. Action: run `lake exe cache get` manually (as usual) and proceed; if `lake build` succeeds, you’re consistent.

## Toolchain and cache alignment

- We pin Lean to `leanprover/lean4:v4.25.0`; mathlib and doc-gen4 are pinned to their `v4.25.0` tags in `lakefile.lean` / `docbuild/lakefile.toml`. Keep these in lockstep—if mathlib bumps, copy its `lean-toolchain` version to the project root and update the git tags.
- Shared caches live under `/workspaces/worktrees/shared/lean/{packages,build,docbuild-build}`. `worktree-prepare.sh` links `.lake/packages` to the shared cache; `build-docs.sh` ensures `docbuild/.lake/build` points at the shared doc build cache.
- If you see Lake errors about missing `bindSync`/`bindAsync` or missing modules after a toolchain bump, the shared cache likely contains old mathlib/doc-gen4 builds. Fix: remove `/workspaces/worktrees/shared/lean/packages/{mathlib,doc-gen4}`, run `lake update`, then `lake exe cache get`.
- After retagging deps, always run `lake update` to refresh `lake-manifest.json`, then rerun `lake exe cache get` before `lake build`.

## Import note

- In mathlib v4.25 the real topology facts live under `Mathlib.Topology.Algebra.Ring.Real` (not `Topology.Instances.Real`). Use the new path to avoid missing-module errors after updates.
