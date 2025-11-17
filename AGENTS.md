# AGENTS – Root Onboarding

Welcome. This repo contains the full scaffold and implementation work for the MSc thesis **"Probing Viterbo's Conjecture"**.

You are an AI agent working in a devcontainer on a **single canonical git clone** with multiple git worktrees. Almost all work is done by agents; the project owner (Jörn) does high-level strategy and reviews/merges PRs.

The repo is explicitly **agents-first**:
- Assume nothing beyond standard ecosystem conventions; custom conventions and tools must be learned from files.
- Prefer small, explicit, self-contained files that can be read top-to-bottom.
- Do not rely on the model to infer missing details; update docs and comments when you change behavior.

## Reading order

1. This `AGENTS.md` – root-level expectations and pointers.
2. `docs/process.md` – issue workflow, autonomy policy, and quality standards.
3. `docs/architecture.md` – monorepo and tooling architecture; devcontainer + volume pattern.
4. The package-level `packages/*/AGENTS.md` files for the package you are working in.
5. The relevant GitHub issues (list them with `gh issue list` or the web UI).
6. (Optional, legacy) `SPEC.md` – original high-level scaffolding design; will be retired once the docs are stable.

## Repo layout (high level)

- `.devcontainer/` – single canonical devcontainer environment.
- `scripts/` – repo-level helper scripts (worktrees, docs, devcontainer hooks).
- `packages/` – language- and domain-specific packages:
  - `rust_viterbo/` – Rust workspace with math/geometry and FFI crates.
  - `python_viterbo/` – Python (uv) project with the `viterbo` namespace.
  - `lean_viterbo/` – Lean4 + Lake project for formalization.
  - `thesis/` – written thesis sources and build pipeline.
  - `agentx/` – Rust CLI tooling for agents and owner.
## Expectations for agents

- **Try autonomously first.** For any well-specified issue, attempt a full plan → implementation → local verification → PR before asking for high-level guidance. Escalate only when you get stuck or discover spec gaps.
- **Use standard commands.** Prefer ecosystem commands (`cargo test`, `uv run --extra dev pytest`, `lake build`, etc.) over custom wrappers. Package-level `AGENTS.md` files define canonical commands and quality targets.
- **Keep code and docs in sync.** When you change behavior or workflows, update docstrings, comments, and relevant `AGENTS.md` sections.
- **Aim for high quality.** Simple, readable code; clearly-marked expected failures; known bugs and TODOs reflected both in code and in GitHub issues.
- **Respect the environment model.** Assume no GitHub CI; everything is built/tested/benchmarked locally inside the devcontainer.
- **Leave a clean state.** Leave the repo working, or clearly marked as WIP with explicit notes and failing tests labelled as expected failures.

## GitHub workflow at a glance

- The devcontainer is already authenticated with `gh` as the project owner. Leave the default owner/assignee fields untouched; agents effectively operate as that account.
- Create and discuss issues via `gh issue create --body-file path/to/description.md` (avoids shell escaping headaches) and `gh issue comment`. Prefer rich Markdown with acceptance criteria, reproduction steps, and test notes.
- Use `gh pr create --body-file` for pull requests. Only the project owner merges PRs into `main`; agents open PRs, request review, and stop short of `gh pr merge`.
- Follow established GitHub best practices: clear titles, labels, checklists, references to related issues/PRs, screenshots/logs when relevant, and concise summaries describing user impact plus implementation notes.
- See `docs/process.md` for the full workflow (issue lifecycle, autonomy policy, and expected signal quality in issue/PR text).

## Where to go next

- Working on Rust math / FFI: read `packages/rust_viterbo/AGENTS.md`.
- Working on Python orchestration / experiments: read `packages/python_viterbo/AGENTS.md`.
- Working on Lean proofs / certificate verification: read `packages/lean_viterbo/AGENTS.md`.
- Working on the written thesis: read `packages/thesis/AGENTS.md`.
- Working on agent tooling and workflows: read `packages/agentx/AGENTS.md` and `scripts/`.
