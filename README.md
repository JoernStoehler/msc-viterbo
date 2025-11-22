# Probing Viterbo's Conjecture

This repo contains the full code, experiments, proofs, tooling, and writeup for my MSc thesis **"Probing Viterbo's Conjecture"**.

The project is **agents-first**: almost all work is done by AI agents running in a devcontainer on a single canonical clone, coordinated via GitHub issues/PRs (through the authenticated `gh` CLI) and git worktrees. The automation architecture is documented in `AGENTS.md` plus `packages/agentctl/docs/architecture-decisions.md`.

## Getting started

1. Open the repo in the devcontainer defined in `.devcontainer/`.
2. Read `AGENTS.md` for repo-wide onboarding plus `packages/agentctl/docs/architecture-decisions.md` for the automation tooling design.
3. For the package you work on, read `packages/<name>/AGENTS.md`.
4. Pick or create a GitHub issue (use `gh issue list` / `gh issue create --body-file <file>`).

## Packages (high level)

- `packages/rust_viterbo/` – high-performance Rust math and FFI crates.
- `packages/python_viterbo/` – Python `viterbo` package for orchestration, data pipelines, and ML.
- `packages/lean_viterbo/` – Lean4 project for formalizing the key parts of the argument and building certificate verifiers.
- `packages/thesis/` – thesis sources and build pipeline.
- `packages/docs-site/` – Astro-based GitHub Pages site that renders the thesis MDX plus aggregated API docs.
- `packages/agentctl/` – Rust CLI + daemon that manage Codex agents.

For more detail, see `AGENTS.md` and the package-level `AGENTS.md` files.
