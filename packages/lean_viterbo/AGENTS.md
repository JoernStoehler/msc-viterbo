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

## Tooling and commands

- Use `lake build` to build the project.
- Use `lake env lean` (or your editor integration) for interactive development.

