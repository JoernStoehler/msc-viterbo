# Architecture – Monorepo, Packages, and Tooling

This document describes the high-level architecture of the repository: packages, how they fit together, and the devcontainer + volume pattern.

## Single owner, single clone

- The project is used and developed by a single project owner (Jörn) and many AI agents who do almost all of the work.
- There are no external dependents or users; external humans are not expected to contribute.
- Public-facing content is limited to:
  - `README.md` – GitHub landing page for interested external researchers.
  - The gh-pages site – aggregated documentation (including generated API docs).
- There is one canonical git clone, using one devcontainer environment and many git worktrees.
- We do **not** use GitHub CI; all builds, tests, and benchmarks run locally in the devcontainer.

Owner-only responsibilities:
- Review and merge feature PRs into `main`.
- Create the first drafts of GitHub issues that define feature goals.
- Trigger devcontainer rebuilds.

## Monorepo structure

We pick the right language for the right job. The monorepo contains multiple packages, each with its own toolchain, scripts, onboarding material, documentation, build system, source, and tests.

Top-level:
- `.devcontainer/` – devcontainer definition (Dockerfile + config).
- `scripts/` – helper scripts for the monorepo (devcontainer hooks, worktrees, docs).
- `packages/` – language- and domain-specific packages.

Packages:
- `packages/rust_viterbo/` – Rust + Cargo workspace with several crates for high-performance math:
  - `geom` crate: basic symplectic geometry structures and operations.
  - `ffi` crate: PyO3/maturin glue so Rust code is conveniently callable from Python.
- `packages/python_viterbo/` – Python + uv project with a single `viterbo` namespace:
  - orchestration and experimentation logic,
  - data pipelines and ML code,
  - end-to-end tests that tie components together.
- `packages/lean_viterbo/` – Lean4 + Lake project for formalisation and verification:
  - uses axioms for standard low-level differential geometry where appropriate,
  - focuses on correctness of the main algorithm, especially lemmas about closed characteristics and minimum-action closed characteristics on 4D polytopes,
  - may include a certificate verifier that, for each polytope, confirms that a computed minimum orbit is indeed minimal and an orbit.
- `packages/thesis/` – thesis sources and build pipeline:
  - canonical sources are Markdown files during development,
  - roughly a week before submission we convert to LaTeX and finalise a print-ready version.
- `packages/agentx/` – Rust CLI tooling for agents and the project owner:
  - commands for managing worktrees and branches,
  - tracking autonomous agents in a lightweight local database,
  - supporting local integration and PR preparation flows (GitHub-specific tasks are handled directly via `gh`).

## Devcontainer and volume pattern

- The devcontainer defines the **canonical** development environment:
  - OS image and base tools.
  - Installation of Node/npm, `uv`, Rust (via rustup), and Lean (via elan).
  - Any future global tools needed by multiple packages.
- The git clone is bind-mounted into the container as the workspace.
- Persistent, repo-specific and user-specific state is kept in host directories that are bind-mounted into the container, for example:
  - `~/.codex` (Codex CLI configuration),
  - `~/.config/gh` (GitHub CLI auth/config),
  - `~/.cache/uv` (uv caches),
  - `~/.bash_history_dir` (shell history),
  - `~/.agentx` (agentx databases and project metadata),
  - `/var/tmp/msc-viterbo/worktrees` (project worktrees, backed by a host directory such as `/srv/devworktrees/msc-viterbo/worktrees`).
- Inside the devcontainer we use **symlinks** to provide stable, discoverable paths:
  - `/workspaces/worktrees` points at `/var/tmp/msc-viterbo/worktrees`.
- This pattern ensures that:
  - devcontainer rebuilds do not delete worktrees or other important state,
  - authentication and agent tooling state can be shared across multiple repositories if desired,
  - the overall environment stays simple and transparent for agents.

## Documentation tooling (overview)

- The top-level `scripts/docs-deploy.sh` script is responsible for orchestrating documentation builds and aggregating them into a gh-pages site.
- Each package uses whichever Markdown-based documentation tooling is most natural for its ecosystem. Examples:
  - Lean: doc-gen4 or similar integrated with the Lake project.
  - Rust: `cargo doc` plus potentially mdBook or similar for higher-level docs.
  - Python: mkdocs or sphinx, chosen per future issue.
- The exact tool choices and wiring are made incrementally via dedicated GitHub issues; this document only records the intention to:
  - keep documentation Markdown-centric where possible,
  - integrate package docs into a single gh-pages site.
