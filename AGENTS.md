# AGENTS.md

This is the root-level onboarding entry point for AI agents working on the **"Probing Viterbo's Conjecture"** MSc thesis project of Jörn Stöhler.

We employ a hybrid workforce of:
- **AntiGravity Agents**: Built-in agents in the AntiGravity VS Code fork, powered by **Gemini 3 Pro** or **Claude Sonnet 4.5**.
- **Codex Agents**: CLI-based agents managed via `agentctl`, powered by **GPT-5** series models.
- **Project Owner**: Jörn Stöhler (Human).

## Agent-Specific Documentation

Each agent type has access to different tools and capabilities. After reading this file, consult your agent-specific documentation:
- **Claude agents**: [`packages/agentctl/docs/antigravity-claude-agents.md`](packages/agentctl/docs/antigravity-claude-agents.md)
- **Gemini agents**: [`packages/agentctl/docs/antigravity-gemini-agents.md`](packages/agentctl/docs/antigravity-gemini-agents.md)
- **Codex agents**: [`packages/agentctl/docs/codex-gpt-agents.md`](packages/agentctl/docs/codex-gpt-agents.md)

These files document the specific tools available to each agent type and how to use them effectively.

## Project Overview

The project is a master thesis in mathematics. This repository contains all materials, including data, code, formal proofs, documentation, the written thesis, project management, and custom AI agent tooling.
The thesis topic is roughly:

For what convex polytopes $K \subset \mathbb{R}^4$ is the Viterbo conjecture true? 
$$\mathrm{sys}(K) := \frac{c_\mathrm{EHZ}(K)^2}{2 \mathrm{vol}(K)} \leq 1?$$ 
Here, $c_\mathrm{EHZ}(K)=A_\mathrm{min}(K)$ is the Ekeland-Hofer-Zehnder capacity, defined as the minimal action of a closed characteristic on the boundary of $K$.
Note that we constrain ourselves to 4 dimensions.

The main conceptual components of the project are:
- A novel, fast, trusted algorithm to compute $A_\mathrm{min}(K)$ for convex polytopes $K \subset \mathbb{R}^{4}$.
- Various data science and machine learning experiments to come up with and test hypotheses. Python for fast development, Rust for performance-critical code.
- A Lean4 library for symplectic geometry on polytopes.
- Lean4 formalized proofs of our algorithm and our main mathematical results.
- The written thesis, which documents the above and discusses results.
- Custom AI agent tooling for massive automation of code, proof, and document generation.
- A repo that covers the whole project, and is end-to-end reproducible for developers and reviewers.

## Repo Layout
The repo is a monorepo:
- `packages/rust_viterbo/`: Rust+cargo workspace with crates for reusable geometry math, our high-performance algorithm implementation, and FFI bindings.
- `packages/python_viterbo/`: Python+uv project with the `viterbo` namespace for data science and ML experiments.
- `packages/lean_viterbo/`: Lean4+Lake project for formalization.
- `packages/thesis/`: Written thesis.
- `packages/docs-site/`: Astro-based GitHub Pages site that renders the thesis MDX plus aggregated API docs.

We maintain up-to-date onboarding documents in
- `AGENTS.md`: this file, general onboarding for all agents.
- `packages/*/AGENTS.md`: onboarding for specific packages.
- `scripts/*`, `.devcontainer/*`: per-file comment blocks for each custom script or environment definition file to aide with troubleshooting and development.
The onboarding documents reference further readings, so that agents can triage which files they need to read for their work and which they can skip for now.

We generally encourage to use standard tools and commands, and edit our environment to make them work with low friction. For frequent multi-step workflows that are hard to get right we provide simple shortcut scripts in `scripts/` and `packages/*/scripts/`. The idea is that agents can also read the scripts and run commands manually in case of troubleshooting or custom needs.

All development happens in a single VS Code devcontainer that owns the lone git clone on the host.

## Environment, Agents, Git Worktrees, GitHub Issues, and `agentctl`

- **Devcontainer basics.** `.devcontainer/{Dockerfile,devcontainer.json}` plus `scripts/devcontainer-post-create.sh` describe the image, bind mounts, and lifecycle hooks. The container starts from `mcr.microsoft.com/devcontainers/base:ubuntu`, already has all toolchains installed, and persists caches via volumes/binds. Assume everything works; read the docs only when debugging or evolving the environment.
- **Toolchains baked on 2025-11-17.** Rust (rustup 1.91.1 + sccache, clippy, rustfmt, cargo-chef), Python 3.12.3 with uv 0.9.9 (ruff, pyright, pytest via `uv run`), Node.js 22.21.0 + npm 10.9.4, Lean 4.25.0 + Lake 5.0.0, GitHub CLI 2.45.0, git 2.51.1. Everything is authenticated under the project owner’s account.
- **Standard commands.** `cargo`, `uv run`, `lake`, `npm`, `git`, `gh`, `jq`, `rg`, `fd`, `tree`, `ctags`, `bash -lc`. Use `gh issue ...` / `gh pr ...` for GitHub management. Run every command from inside your assigned worktree. **When creating or editing issues/PRs with bodies, always use `--body-file` (never `--body`) to avoid shell-escaping surprises.**
- **Custom commands.** `scripts/devcontainer-post-create.sh` (lifecycle hook) and `packages/docs-site/scripts/docs-publish.sh` (docs deployment).
- **Prep scripts (pick what you need).** `scripts/worktree-prepare.sh /path/to/worktree` by default runs general + python + docs + lean cache + rust. Use `--minimal` to skip package prep, or flags (`--python`, `--docs`, `--lean`, `--rust`) to tailor. Package-local scripts live in `packages/*/scripts/worktree-prepare.sh` for direct use.
- **Caching defaults.**
  - Lean: `packages/lean_viterbo/scripts/worktree-prepare.sh` links `.lake/packages` to a shared cache under `/workspaces/worktrees/shared/lean/packages` and runs `lake exe cache get` (no build by default). Run `lake build` only when doing Lean work. Home-level `.lake` is bind-mounted to persist caches across container rebuilds.
  - Rust: Cargo now uses a shared target dir `../worktrees/shared/target` (set in `.cargo/config.toml`) so worktrees reuse builds. Keep it if you can; override with `CARGO_TARGET_DIR` if you must.
  - Python/Node: standard tool caches live in `$HOME` and persist across worktrees; nothing special to do.
- **Agent Control (`agentctl`).** Preinstalled in the devcontainer and already on `PATH`; never ask the project owner to install it. Verify with `agentctl --version`. AntiGravity agents can also use `agentctl` to spawn sub-agents. The `agentctl` binary handles:
  - `agentctl daemon`: starts the HTTP server and process supervisor. It reads `AGENTCTL_PORT` (default `3000`) plus `AGENTCTL_CODEX_BIN` for the Codex binary path.
  - `agentctl start --workdir <path> --prompt "..."`: starts a new turn. Returns the thread ID.
  - `agentctl status <id>`: checks the status of a thread.
  - `agentctl await <id>`: waits for a thread to complete.
  - `agentctl list`: lists all threads.
  - `agentctl stop <id>`: stops a thread.
  - Duplicate `agentctl daemon` invocations fail fast with a clear “already running on port …” error.
  - Agent shells are forced non-interactive for Git (`GIT_TERMINAL_PROMPT=0`, `GIT_SSH_COMMAND='ssh -oBatchMode=yes'`, etc.) via `~/.codex/config.toml`; project-owner shells stay interactive.
  Escalate to the project owner if the daemon or CLI subcommands behave unexpectedly.

- **Worktree ownership.** The main worktree/branch belongs to Jörn, only he can accept PRs or merge into main. Other worktrees are just normal git worktrees created via `git worktree add …` plus `scripts/worktree-prepare.sh`. Coordinate with Jörn before pushing or rebasing shared worktrees. Keep every auxiliary worktree under `/workspaces/worktrees/` (mounted by the devcontainer) instead of creating a `worktrees/` directory inside the repo.
- **Project-management artifacts.** Issues and PRs live on GitHub. Use the authenticated `gh` CLI to inspect or update them, and append the provenance footer whenever an agent authors GitHub text. All agents share one GitHub identity, and we do not run GitHub Actions/CI, so you must run the relevant checks locally before pushing:
    ```
    ---
    🤖 Author: codex agent on branch `agent/issue-123`
    🤖 Edited by: codex agent on branch `agent/issue-128`
    ```
- **Contacting the project owner.** The owner is Jörn Stöhler. Default channel: end your turn with a clear finalMessage (preferred) or leave a concise comment on the relevant GitHub issue/PR via `gh issue comment --body-file …` / `gh pr comment --body-file …` (with the provenance footer). Do not assume Slack/DM access.
- **Delegation hooks.** For large sub-issues you own, create another git worktree, run `scripts/worktree-prepare.sh`, and spin up a new `agentctl start --workdir <that-dir> …` turn dedicated to the subtask. For tiny helper tasks inside the same worktree, it is fine to run an additional `agentctl start --workdir <current-dir> --prompt "helper task"` turn and keep the deliverable short.

## The Most Frequent Workflows

**Note for AntiGravity Agents:** You are typically started via the IDE. The workflows below describe the rigorous process often used for Codex agents, but the principles (Worktree + Agent → PR) apply to you as well. You can also use `agentctl` to spawn Codex sub-agents if you need to parallelize work.

### Project Owner → Issue → Worktree + Agent → PR
1. Jörn files or references a GitHub issue (or gives you a prompt describing the target).
2. Jörn prepares a worktree (via `git worktree add …`, `scripts/worktree-prepare.sh`, and `agentctl start --workdir <path> --prompt "issue ###"`), then hands you that worktree and the initial instructions.
3. You execute the entire issue inside that worktree, produce the deliverable, and open a PR against `main` (or the branch named in the issue). Use a draft PR if anything is incomplete or blocked.
4. Jörn reviews, may request follow-ups, and merges or declines the PR. Assume you own the full lifecycle (planning, implementation, tests, docs) unless told otherwise.

### Project Owner → Agent on `main` → Chatting
Sometimes Jörn runs `agentctl start --workdir /workspaces/msc-viterbo --prompt "..."`, i.e. points an agent directly at the main worktree for rapid back-and-forth. The main worktree is still owned by Jörn, so keep edits minimal, gate risky changes behind confirmation, and be careful around uncommitted changes that other agents may be working on. The back-and-forth is driven by Jörn's prompt and your final message each turn, don't assume Jörn will read all the changes you made and all the action preambles you wrote while you worked.

### Agent → Sub-Issue → Worktree + Agent → Merge
If your issue spawns a substantial, independent task, create a new worktree (via `git worktree add …` and `scripts/worktree-prepare.sh`) tied back to your branch, start a helper agent there (`agentctl start --workdir <that-dir> …`), and integrate the results once it finishes (`agentctl await` followed by normal git workflows). Continue your main assignment with the sub-results integrated.

### Agent → Sub-Agent on same worktree → Chatting
For scoped helper tasks that do not deserve their own worktree (log triage, file reading, repetitive edits), start another turn bound to your current worktree: `agentctl start --workdir <current-dir> --prompt "helper task"` (or `agentctl reply --uuid <uuid> --prompt-file ...`). Keep helper prompts precise and short-lived, and integrate the result immediately so you do not overwrite each other.

## Working Autonomously

- Read the entire assignment (prompt, issue, linked files) before acting. Load context and onboard yourself to the project and repo; escalate early when the specification is contradictory, amigiously unclear, or missing critical data that you cannot find via a reasonable search.
- You are responsible to plan, implement, test, document, review, and deliver the assigned work, unless explicitly told otherwise. Follow established conventions in this file and in package-level `AGENTS.md` files. Follow best-practices in general.
- Prefer to batch questions to the project owner to avoid disrupting Jörn's flow, and use the expected direct tone—push back on unclear specs or mistakes immediately, propose fixes, and skip ceremonial politeness.
- Escalate blockers with actionable detail: what you attempted, which logs you gathered, why progress stopped, and what you need concretely (decisions, clarification, ideas, commands/actions to be taken, etc). Minimize the time Jörn needs to get up to speed and help you. Provide reproduction steps so that other agents could, in principle at least, also take a look and troubleshoot.
- Ensure every generated artifact (plots, datasets, binaries) are reproducible. Document command arguments or config values, so that future agents can regenerate them easily.
- Prefer a draft PR when work is incomplete but you uncovered important blockers or partial results. Describe gaps explicitly instead of hoping reviewers infer them.
- When delegating, specify success criteria clearly. You can reject work and retry with a new agent, if it's not worth trying a follow-up to build on a failed attempt. Use normal git workflows for cross-worktree integration. Use `agentctl reply` for follow-up actions or questions.

## Universal Conventions

The following conventions apply to all packages, and so they are mentioned once here. Package-level `AGENTS.md` files may mention extra conventions and workflows that are relevant when working in that package.

- **Writing Style**: We maintain a professional, clear, unambiguous, specific and accurate writing style. Avoid colloquialisms, vague terms, or synonyms when there's a single clear term for a concept. Our target audience are AI agents, who have been trained on basically all books, code, and workflows that exist, so they are familiar with common patterns, conventions, best practices, terminology, and expert knowledge in mathematics & software engineering & project management & all other domains. We optimize files to be read top-to-bottom without pauses, since agents usually open entire files and read their whole content at once. We minimize cognitive overhead so that agents can read and immediately continue working. We spell out implications to ensure agents have them available immediately without having to infer them. We don't explain common concepts, since agents have been trained on them already, but we do mention/name-drop them to remind the agents so that they load useful associative knowledge into their working memory. Since agents read whole files, we keep files below the agent's harness buffer limits (<250 lines, <10kB) where splitting files is sensible. We omit unnecessary redundant summaries or quick-reference sections, since agents read the whole file anyway and pay roughly equal attention to every single sentence regardless of location.
- **Math notation**: Prefer `\(...\)` for inline and `\[...\]` for display math to avoid shell-escaping pain with `$`. MkDocs is already configured via `pymdownx.arithmatex`, and the VS Code workspace file `thesis.code-workspace` enables these delimiters for local preview. Do **not** add `.vscode/settings.json`; if you need editor settings, update the workspace file instead.
- **Correctness**: We move the whole project commit-by-commit forward. Since we don't have any external contributors, only one project owner and many temporary agents, we don't need to migrate or document legacy commits. The documentation and code and data is always focused on the current commit, or on the issues-in-progress to be precise. Every now and then when no PRs are open and no agents are working on further feature branches, i.e. when the whole project is represented in main, we even run our end-to-end reproducibility pipeline and ask a read-only agent to confirm that the documentation is up-to-date and describes the current state of the repo accurately. Outdated information, or accidentally misleading or false information, has to be quickly removed or corrected as soon as it is discovered, to avoid misleading agents and causing wasted work or lost knowledge in the future. No legacy fallbacks or migration code should be kept, instead we migrate once, and then update code and documentation to only reflect the new reality.
- **Testing and Quality**: Every package has its own quality standards and testing conventions, described in the package-level `AGENTS.md` files. Overall we aim for readable, maintainable code that passes manual and automated, static and runtime checks. Manual checks are documented usually in the form of comments/docstrings to speed up later repetition and document our expectations. Agents are familiar with best practicies for different toolchains, and know what commands to run to e.g. check that two select unit tests in a Rust crate turned green after a code change. We use comments in code files to document the why behind implementation and architecture choices when they may be relevant to future tasks, e.g. to avoid regressions or to clarify that non-obviously needed complexity is indeed needed.
- **Simplicity**: Since agents are trained on basically all code and workflow patterns known to mankind, we heavily lean towards using well-known best practices, naming schemes, style conventions, commands and tools, frameworks and libraries, architecture and code patterns, documentation and comment styles, and project management approaches. We avoid custom, homegrown solutions unless necessary. Of course, a lot of code and documentation is specific to this master thesis project with no well-known alternatives to use instead, but we can still focus on keeping the project analogous/similar to well-known patterns and related projects. That's why we chose a clearly separated monorepo, so that the packages can each independently follow the best conventions for their respective purpose and toolchain and ecosystem. When we implement custom solutions, we heavily focus on rapid onboarding and a simple, accurate abstraction layer. This way agents do not have to understand our custom solutions' internals, but can just use them and rely on them to behave in well-known, expected ways.
- **Documentation**: Every package has its own documentation conventions, described in the package-level `AGENTS.md` files. Many packages keep a local `docs/` subdirectory for extra Markdown, alongside docstrings / comment blocks that tooling can extract into API docs. `packages/docs-site/scripts/docs-publish.sh` aggregates those package docs to GitHub Pages.
- **Official references only (no bluffing)**: When you say you “read” or “checked” a guide, that must mean you actually opened the canonical source for this toolchain/version. For Lean/mathlib the canonical docs are the mathlib4 HTML docs for the pinned tag (`https://leanprover-community.github.io/mathlib4_docs/`) plus the upstream mathlib source files in the shared cache. Do not cite external memory or vague book titles. If you haven’t opened the official source in this run, say so and read it before proceeding.

## Where to Go Next
After reading this file, agents must run `bash -lc 'pwd && agentctl self && git status -sb'`. This confirms the worktree path, prints the identity (`project_owner` or agent UUID), and exposes any uncommitted changes that cannot be restored via `git reset ...`. It is often sensible to backup uncommitted changes before overwriting them, e.g. via `cp path/to/file path/to/file.bak.$(date -Iseconds)` to a gitignored (`*.bak.*`) location.

After orienting wrt git, agents should identify which package(s) they will be working on, and read the respective package-level `packages/*/AGENTS.md` files next. The files will reference further readings of which some, or none, may be of interest depending on the agent's assigned issue(s).

Minimal prep matrix (opt-in; run only what you need):
- Docs/thesis only: `scripts/worktree-prepare.sh --docs /path/to/worktree` or run `packages/docs-site/scripts/worktree-prepare.sh` directly.
- Python experiments: `scripts/worktree-prepare.sh --python ...`.
- Lean work: `scripts/worktree-prepare.sh --lean ...` (shared `.lake/packages`, `lake exe cache get`, no build by default). Run `lake build` when you touch Lean code.
- Rust work: `scripts/worktree-prepare.sh --rust ...` (uses shared Cargo target dir `/workspaces/worktrees/shared/target`).
- Everything: default `scripts/worktree-prepare.sh` (or `--all`) runs general + python + docs + rust + lean-cache-only.
