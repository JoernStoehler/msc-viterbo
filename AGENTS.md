# AGENTS.md

## Project Overview
Monorepo for the MSc thesis **"Probing Viterbo's Conjecture"** (code, experiments, proofs, thesis, tooling, environment, agents). Agents work in a single defined devcontainer; GitHub issues/PRs coordinate the work.

Repo layout (top level):
- `packages/rust_viterbo/`: Rust library.
- `packages/python_viterbo/`: Python experiments/pipelines.
- `packages/lean_viterbo/`: Lean4 formalization.
- `packages/thesis/`: Written thesis.
- `.devcontainer/*`, `scripts/*`: Environment definition and convenience scripts.
- `AGENTS.md`, `agent_docs/`: package- and environment-specific onboarding (progressive disclosure).

## Toolchains
- Rust 1.91.1, cargo 1.91.1, clippy, rustfmt, sccache.
- Python 3.12.3, uv 0.9.13, pyright, ruff, pytest (via `uv run ruff/pyright/pytest`).
- Node.js 22.21.0, npm 10.9.4.
- Lean 4.25.0, lake 5.0.0.
- git 2.52.0, gh 2.45.0, git lfs.
- MkDocs 1.5.13, Material for MkDocs 9.1.11.
- Misc: `rg, fd, jq, tree, bash -lc, ctags`.
- Codex CLI >=0.63.0.

## Worktrees
- Main worktree: `/workspaces/msc-viterbo`.
- Keep additional worktrees under `/workspaces/worktrees/<name>`.
- Prep script: `git worktree add <path> <branch>` + `scripts/worktree-prepare.sh <path>`.
- Shared caches between worktrees to minimize rebuild times.
- GitHub CLI: always use `--body-file` for issues/PRs to avoid shell quoting pain. Always include a footer
  `Written-by: codex agent running in worktree <path>`.
- Only project owner approves PRs targeting `main`.

## Universal Conventions
- **Communication**: Be literally correct, specific, unambiguous. Escalate blockers and repeat unanswered questions; do not assume silence is approval. Disclose progressively to respect project owner time.
- **Quality**: This is a thesis: prioritize mathematical correctness. Code targets senior developers; keep APIs clean, simple, idiomatic. Request reviews from project owner for complex or high-stakes changes.
- **Testing**: Catch errors and regressions early. Use static analysis (linters, type checkers) and runtime tests (unit, integration, e2e) as appropriate per package. Document manual test procedures in comments/docstrings where not automated.
- **Documentation**: Explain the “why” in comments/docstrings; avoid legacy/migration lore entirely.
- **Agents**: Agents are first-class contributors. Agents have zero prior context about the project, but are already familiar with all popular toolchains, frameworks, patterns and domain knowledge. Maintain complete and high quality onboarding docs in `AGENTS.md` and `agent_docs/` so that future agents can onboard themselves quickly for their assigned tasks. Always err strongly towards the common, boring, simple solution that agents have been trained on, instead of a custom, superficially clever, complex solution.

## Project Owner
Jörn Stöhler. He owns the `main` worktree, including PRs to `main`.

## Subagents
- Run `codex exec "<prompt>" 2>/dev/null` to spawn a fresh agent in the cwd with zero prior context. The subagent can take actions, and will write a text message to stdout once done. Useful for delegating a subtask that is clearly defined and scoped to a known list of files, that is doable for agents without complex context about the ongoing task, and that has too many or too conceptually different steps to be worth doing directly in the main agent. Examples of subagent tasks: semantic search or comparison where many files need to be read but only a small text message needs to be returned; executing a refactoring across many files that is too tricky for mere text-replacement; reviewing the staged changes with fresh eyes.

## Where to Go Next
- Run `pwd && git status -sb` to confirm your worktree.
- Run `ls agent_docs/` to see available onboarding docs.
- Skip files that are not relevant to your assigned task and read them once they become relevant.
- Ask the project owner if you have any questions about your assigned task, or if you need context beyond what is in the onboarding docs.
- Happy coding!
