# AGENTS.md

## Project Overview
Monorepo for the MSc thesis **"Probing Viterbo's Conjecture"** (code, experiments, proofs, thesis, tooling, environment, agents). Agents work in a single defined devcontainer; GitHub issues/PRs coordinate the work.

Repo layout (top level):
- `packages/rust_viterbo/`: Rust library.
- `packages/python_viterbo/`: Python experiments/pipelines.
- `packages/lean_viterbo/`: Lean4 formalization.
- `packages/latex_viterbo/`: LaTeX thesis stack.
- `.devcontainer/*`, `scripts/*`: environment definition and convenience scripts.
- `AGENTS.md`, `agent_docs/`: onboarding (progressive disclosure).

The onboarding docs require explicit diff-level approval from the project owner due to their importance for future agents.
Other files in the repo can be changed via normal PRs and high-level project owner review.

## Worktrees
- Main worktree: `/workspaces/msc-viterbo`; additional worktrees under `/workspaces/worktrees/<name>`.
- Create: `git worktree add /workspaces/worktrees/<name> <branch>` then run `scripts/worktree-prepare.sh /workspaces/worktrees/<name>` once (wires Rust target, Lean caches, uv deps).
- Shared caches: see `agent_docs/maintain-environment.md`.
- Remove safely with `git worktree remove /workspaces/worktrees/<name>`.
- GitHub CLI: always use `--body-file` for issues/PRs; include footer `Written-by: codex agent running in worktree <path>`.
- Only the project owner approves PRs targeting `main`.

## Universal Conventions
- **Communication**: Be literally correct, specific, unambiguous. Escalate blockers and repeat unanswered questions; do not assume silence is approval. Disclose progressively to respect project owner time.
- **Quality**: This is a thesis: prioritize mathematical correctness. Code targets senior developers; keep APIs clean, simple, idiomatic. Request reviews from project owner for complex or high-stakes changes.
- **Testing**: Catch errors and regressions early. Use static analysis (linters, type checkers) and runtime tests (unit, integration, e2e) as appropriate per package. Document manual test procedures in comments/docstrings where not automated.
- **Documentation**: Explain the “why” in comments/docstrings; avoid legacy/migration lore entirely.
- **Agents**: Agents are first-class contributors. Agents have zero prior context about the project, but are already familiar with all popular toolchains, frameworks, patterns and domain knowledge. Always err strongly towards the common, boring, simple solution that agents have been trained on, instead of a custom, superficially clever, complex solution. Immediately fix incorrect or ambiguous or missing documentation. It is important that agents can rapidly onboard themselves without having to question and verify the correctness of documentation.

## Project Owner
Jörn Stöhler. Expert background in mathematics, machine learning, data science, ai agent design, scientific writing.

## Subagents
- Run `codex exec "<prompt>" 2>/dev/null` to spawn a fresh agent in the cwd with zero prior context. The subagent can take actions, and will write a text message to stdout once done. Useful for delegating a subtask that is clearly defined and scoped to a known list of files, that is doable for agents without complex context about the ongoing task, and that has too many or too conceptually different steps to be worth doing directly in the main agent. Examples of subagent tasks: semantic search or comparison where many files need to be read but only a small text message needs to be returned; executing a refactoring across many files that is too tricky for mere text-replacement; reviewing the staged changes with fresh eyes.

## Where to Go Next
- Run `pwd && git status -sb` to confirm your worktree.
- Run `ls agent_docs/` to see available onboarding docs.
- Skip files that are not relevant to your assigned task and read them once they become relevant.
- Ask the project owner if you have any questions about your assigned task, or if you need context beyond what is in the onboarding docs.
