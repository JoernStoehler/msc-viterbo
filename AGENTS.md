# AGENTS.md

## Project Overview
This repository contains all materials for the MSc thesis project "Probing Viterbo's Conjecture", including data, code, formal proofs, documentation, the written thesis, project management, the development environment definition and custom scripts.
We use a monorepo structure:
- `packages/thesis/`: Written thesis in Material for MkDocs.
- `packages/rust_viterbo/`: High-performance Rust implementation of symplectic geometry algorithms, including our custom algorithm to compute the Ekeland-Hofer-Zehnder capacity for convex polytopes in $\mathbb{R}^4$.
- `packages/python_viterbo/`: Python data science and machine learning experiments.
- `packages/lean_viterbo/`: Lean4 formalization of symplectic geometry on polytopes.
- `.devcontainer/{Dockerfile,devcontainer.json}`, `scripts/devcontainer-post-create.sh`: Definition of the sole development environment that all agents and the project owner use.
- `gh issues + prs`: Project management artifacts live on GitHub. All agents also share the project owner's GitHub identity.
- `/workspaces/worktrees/`: We use git worktrees for parallel development.
- `AGENTS.md`: onboarding documentation for all agents.
- `agent_docs/`: further readings that may be relevant depending on your task.
- `scripts/`, `packages/*/scripts/` folders: contain convenience shortcut scripts for frequent multi-step workflows.

## Available Tools

Installed and configured: `rg, fd, tree, jq, git, gh, cargo, uv run, lake, bash -lc`
Quick overview of commands:
- `git worktree add /workspaces/worktrees/{name} && scripts/worktree-prepare.sh /workspaces/worktrees/{name}`: prepare a new worktree with branch `{name}`.
- `cd {folder} && git status -sb && codex exec "{prompt}" &2> /dev/null`: run a new codex subagent. The subagent prints a message to stdout when done. Useful when you need a well-scoped task done but you don't want to do it yourself and deal with the context switching, the extra irrelevant file reads, or thinking through tool call sequences. Specify clearly and literally correct what the agent should do, and what files it is allowed to edit (if any).
- `gh issue create --title "..." --body-file path/to/body.md`: create a new GitHub issue. Use a body file to avoid shell-escaping pain.
- `gh pr create --title "..." --body-file path/to/body.md --base main --head {branch}`: create a new PR from branch `{branch}` into `main`. Use a body file to avoid shell-escaping pain.

Toolchain versions:
- Rust: rustc 1.91.1, cargo 1.91.1, sccache 0.3.4, clippy 1.91.1, rustfmt 1.91.1, cargo-chef 0.2.21
- Python: 3.12.3, uv 0.9.9 (ruff, pyright, pytest via `uv run`)
- Node.js: 22.21.0, npm 10.9.4
- Lean4: 4.25.0, Lake 5.0.0
- GitHub CLI: 2.45.0
- git: 2.51.1
- MkDocs: 1.5.13, Material for MkDocs: 9.1.11

## Main Conventions
- **Communication**: Be literal correct, specific, unambiguous, and do progressive disclosure when chatting with the project owner. Don't take silence as agreement, repeat questions or blockers until resolved.
- **Quality**: This project is a master thesis. Aim for literally correct, specific and interesting mathematics. The target audience of math writing are other mathematicians with a background in smooth symplectic geometry, but not necessarily on polytopes. The target audience of code are other senior developers familiar with all common libraries, toolchains, patterns, and best practices in Rust, Python, Lean4, Git, Bash, project management on GitHub, MkDocs, devcontainers, ...
- **Testing**: To assure mathematical correctness, we use formal proofs in Lean4, unit tests in Rust, and e2e sanity checks in Python experiments. We use static linters and type checkers to get even earlier feedback. Use the standard commands such as `uv run pytest <file>`, `cargo test --package <crate>`, `lake build -q`, `cargo clippy`, `uv run ruff check .`, etc.
- **Documentation**: We use high quality comments and docstrings to explain the why behind code, including contracts, design decisions and their reasons. We don't document legacy or migration paths, we focus entirely on the current commit and don't bother readers with irrelevant information about the past. We use cross references to link code to the thesis writeup and vice versa.
- **Agents**: We write for agents as first-class contributors to the project. Agents are familiar with all common libraries, toolchains, patterns, and best practices in all languages and ecosystems. They however start their work with an empty context window and need to be onboarded to the project and repo from scratch each time. Therefore we document in `AGENTS.md` and `agent_docs/` everything there is to know about the project and repo, minimizing the implicit knowledge held by the project owner. We focus on the current commit, and the plans for the future, and don't waste the agents' time with legacy or migration paths. Since agents are familiar with all common patterns, we only name-drop and optionally if non-obvious state the why, and we do not explain the how/what in detail. We use progressive disclosure, so that agents can pick their own reading material depending on their assigned tasks, and get to work without having to read everything upfront.

## Project Owner
The project owner is Jörn Stöhler. 
He is the user you talk to, unless your prompt mentioned that you are a subagent. 
Jörn has a strong background in mathematics, software engineering, and data science. He has a coherent vision for the project and you can ask him if you need context that wasn't covered by the onboarding materials.
Only Jörn can merge PRs into `main`, and he has to be consulted before making major architecture decisions that have long-term implications for the project, e.g. tech-stack, dependency upgrades, or changes to heavily used interfaces.

## Where to Go Next
You can at any point read further onboarding materials in the `agent_docs/` folder. The file names were chosen to be self-explanatory.
A good command to run right now is `bash scripts/hello-agent.sh` which gives you dynamic information about the repo state not captured in the less frequently updated onboarding materials.
