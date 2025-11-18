# AGENTS.md

This is the root-level onboarding entry point for AI agents working on the **"Probing Viterbo's Conjecture"** MSc thesis project of Jörn Stöhler.

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

We maintain up-to-date onboarding documents in
- `AGENTS.md`: this file, general onboarding for all agents.
- `packages/*/AGENTS.md`: onboarding for specific packages.
- `scripts/*`, `.devcontainer/*`: per-file comment blocks for each custom script or environment definition file to aide with troubleshooting and development.
The onboarding documents reference further readings, so that agents can triage which files they need to read for their work and which they can skip for now.

We generally encourage to use standard tools and commands, and edit our environment to make them work with low friction. For frequent multi-step workflows that are hard to get right we provide simple shortcut scripts in `scripts/` and `packages/*/scripts/`. The idea is that agents can also read the scripts and run commands manually in case of troubleshooting or custom needs.

All development happens in a single vscode devcontainer, that owns the single repository clone for development and runs on the project owner's machine. 

## Agents, Git Worktrees, and Issues

- The main branch & worktree is owned by the project owner (Jörn). There is only one git clone inside the one devcontainer on the one host machine we use for development.
- Every git worktree besides main is owned by exactly one agent. Agents are bound to one worktree as working directory for their entire lifetime. Helper sub-agents may share the same worktree as their owning agent. We identify agents by their session uuid, or by their worktree path, or their worktree branch name if that uniquely identifies the agent.
- The worktrees are located in `/var/tmp/msc-viterbo/worktrees/` (bind-mounted from the host) and provisioned with `scripts/worktree-add.sh ...` which also runs the hook `scripts/worktree-post-add.sh` to bootstrap the packages' toolchains for the new worktree.
- Agents are built with the official `codex` cli as backend. A new agent turn can be started with `scripts/agent-start.sh <identifier> --prompt[-file] ...` which starts a detached process with `codex exec [resume]`.
- For sub-agents in the same worktree one can use the simpler `scripts/subagent-run.sh --prompt[-file] ...` which blockingly runs a single-turn agent with `codex exec` and prints the sub-agents final message to stdout once it is done.
- We do project management with GitHub issues and PRs. PRs are submitted only for merges against the project owner's main branch. Agents can freely merge changes into their owned worktree branch without PRs.
- Agents can inspect, edit and create issues and PRs with the `gh` cli, which is already authenticated in the devcontainer.
- To document which agent wrote or edited what text, please add a footer like this to issue/PR bodies or comments:
    ```
    ---
    🤖 Author: codex agent on branch `agent/issue-123`
    🤖 Edited by: codex agent on branch `agent/issue-128`
    ```
- Most commonly, agents have been given a minimal prompt that only includes the assigned issue number, e.g. `--prompt "/issue 123"`. Agents should then work through the issue autonomously, including self-onboarding, planning, implementation+testing+documentation, and review, until the acceptance criteria are met or until the agent gives up and consults with the project owner instead by stating the problem in its final message. If a target branch is specified in the issue, agents should create a PR against that branch.
- The active and inactive agents and worktrees can be listed with `scripts/agents-and-worktrees-list.sh` and filtered with `... | rg <pattern>`.

## Environment

The reproducible environment is defined in `.devcontainer/{Dockerfile,devcontainer.json}` and `scripts/devcontainer-post-create.sh`. Those files document every customization (base image, bind mounts, lifecycle hooks).
Agents can assume the container and their working directory are ready-to-use and were fully setup before the agent was started; use the docs only when debugging or evolving the environment.
The environment is a docker container based on `mcr.microsoft.com/devcontainers/base:ubuntu` with all toolchains and common tools preinstalled, configured, and ready to use. Data is persisted via volumes and bind mounts, so the container can be rebuilt without losing caches or worktrees.

Agents run commands from inside their worktrees; see the previous section for worktree locations and automation hooks.

Available toolchains (versions baked into the devcontainer image on 2025-11-17) include:
- Rust via rustup 1.91.1. Includes sccache, clippy, rustfmt, cargo workspaces, cargo-chef.
- Python 3.12.3 via uv 0.9.9. Includes ruff, pyright, pytest, all via `uv run`.
- Node.js `v22.21.0` + npm `10.9.4` for Codex CLI `1.*` and custom TS in documentation.
- Lean 4 (`lean 4.25.0`) with Lake `5.0.0`, installed through `elan`.
- GitHub CLI `2.45.0` and git `2.51.1` for issue/PR management; both are already authenticated in the devcontainer.

Available common commands include:
- `cargo`, `uv run`, `lake`, `npm`, ...
- `git`, `gh` (authenticated as the project owner's user identity)
  - In particular: `gh issue ...`, `gh pr ...` are available for issue and PR management.
- `jq`, `rg`, `fd`, `tree`, `ctags`, `bash -lc`

Available custom commands include:
- `scripts/devcontainer-post-create.sh`: lifecycle hook, automatically runs before any agent starts.
- `scripts/docs-deploy.sh`: build, collect, and deploy all packages' docs to GitHub Pages.
- `scripts/worktree-add.sh <path> --branch <branch> [--from-branch <from-branch>]`: validates safe operations possible, then creates a new git worktree.
- `scripts/worktree-post-add.sh`: lifecycle hook invoked after each worktree is created.
- `scripts/agent-start.sh <uuid|path|branch> --prompt[-file] <prompt-or-file> [--profile fast|smart]`: starts the next agent turn for an existing or new agent, runs in a detached process.
- `scripts/subagent-run.sh --prompt[-file] <prompt-or-file> [--profile fast|smart]`: starts a short-lived sub-agent in the current worktree, runs blockingly.
- `scripts/agents-and-worktrees-list.sh`: lists all existing worktrees and active or inactive agents. Filter with `... | rg <pattern>`.

## Project Owner and Agents Workflow

The basic workflow is:
- The project owner (Jörn) creates GitHub issues, or chats with an agent who then creates GitHub issues.
- The project owner (Jörn) uses `agentx` to start an agent in a new worktree with a specific issue assigned to it.
- The agent works on the issue autonomously, including self-onboarding, planning, implementation+testing+documentation, and review, until the acceptance criteria are met or until the agent gives up and consults with the project owner. Either way, at the end the agent creates a PR for review, or a draft PR for discussion.
- The project owner (Jörn) owns the main branch, and decides whether to merge PRs.
- Often the project owner (Jörn) will discuss with the agent, ask for clarifications, or request minor or major follow-up work before merging.

When you need to touch `agentx`, read `packages/agentx/AGENTS.md` first—this root doc only tells you *when* the tool is involved (provisioning worktrees, recording agent metadata). The package-level doc is the source of truth for CLI arguments and maintenance expectations.

Agents are explicitly encouraged to push back on unclear or incomplete requests, ideally via a batched, early question catalogue that the project owner can answer swiftly. Agents should then work autonomously and complete the full issue. Agents are allowed to use their own judgement and carry out their whole plan, including filled gaps in the spec, without asking for approval in advance. Instead they should flag and explain potentially unexpected changes to the project owner in the PR description, who can then accept or ask for reversal/alternative approaches. A general guiding principle is that the project owner is quite busy, so agents should take some extra time to optimize for minimizing the workload of the project owner, and in particular to batch requests or turn requests into a quick, alternating, contiguous conversation, rather than interrupting the project owner every few minutes.

Advanced recursive agent workflow:
- An agent can write sub-issues, start new agents to work through them, await the PRs that now target the agent's feature branch, and then integrate the results into its own work, or even ask agents for follow-up work just like a project owner would.
- It's important to target the agent's feature branch instead of `main`, since latter is owned by the project owner.
- There are only a few situations in which it is advantageous to delegate work to new agents, instead of carrying it out oneself:
  - The agent's work is quite complex, and sub-issues help to structure it and focus on the integration of the sub-results. Sources of complexity include required readings, iterative planning or troubleshooting or work, inherent complexity of the solution, and context-switching e.g. between toolchains or perspective or high-level and low-level work. The complexity of specifying sub-issues of course occurs regardless of whether or not the agent carries them out itself or delegates them.
  - The agent's work is quite long-running but lends itself to parallelization of independent sub-issues, which speeds up overall completion time from the project owner's perspective.
- Besides dedicated new agents, we sometimes spin up short-lived helper agents in the same worktree. Ask Jörn to launch one or consult `packages/agentx/AGENTS.md` if you need to understand how they integrate; keep deliverables tiny (paths, short reports, narrowly-scoped refactors) so the main agent stays focused.
  - Reading a lot of files and reporting back only the relevant ones as paths, e.g. code files that are related to the current feature request and ought to be read by the main agent. Here the sub-agent allows the main-agent to omit having to read a lot of irrelevant files, which would fill its context window and distract it in the future from focusing on the relevant content.
  - A tedious refactoring task while the main agent wants to maintain focus on other tasks without paying attention to dozens of manual file-edit tool calls. In particular edits that require character escaping or lots of slightly varied edits across many files.
  - A debug task that requires a lot of file reading, command tweaking, and log analysis, where the final result of interest however is only a single short report about the root cause and possible solutions.

## Universal Conventions

The following conventions apply to all packages, and so they are mentioned once here. Package-level `AGENTS.md` files may mention extra conventions and workflows that are relevant when working in that package.

- **Writing Style**: We maintain a professional, clear, unambiguous, specific and accurate writing style. Avoid colloquialisms, vague terms, or synonyms when there's a single clear term for a concept. Our target audience are AI agents, who have been trained on basically all books, code, and workflows that exist, so they are familiar with common patterns, conventions, best practices, terminology, and expert knowledge in mathematics & software engineering & project management & all other domains. We optimize files to be read top-to-bottom without pauses, since agents usually open entire files and read their whole content at once. We minimize cognitive overhead so that agents can read and immediately continue working. We spell out implications to ensure agents have them available immediately without having to infer them. We don't explain common concepts, since agents have been trained on them already, but we do mention/name-drop them to remind the agents so that they load useful associative knowledge into their working memory. Since agents read whole files, we keep files below the agent's harness buffer limits (<250 lines, <10kB) where splitting files is sensible. We omit unnecessary redundant summaries or quick-reference sections, since agents read the whole file anyway and pay roughly equal attention to every single sentence regardless of location.
- **Correctness**: We move the whole project commit-by-commit forward. Since we don't have any external contributors, only one project owner and many temporary agents, we don't need to migrate or document legacy commits. The documentation and code and data is always focused on the current commit, or on the issues-in-progress to be precise. Every now and then when no PRs are open and no agents are working on further feature branches, i.e. when the whole project is represented in main, we even run our end-to-end reproducibility pipeline and ask a read-only agent to confirm that the documentation is up-to-date and describes the current state of the repo accurately. Outdated information, or accidentally misleading or false information, has to be quickly removed or corrected as soon as it is discovered, to avoid misleading agents and causing wasted work or lost knowledge in the future.
- **Testing and Quality**: Every package has its own quality standards and testing conventions, described in the package-level `AGENTS.md` files. Overall we aim for readable, maintainable code that passes manual and automated, static and runtime checks. Manual checks are documented usually in the form of comments/docstrings to speed up later repetition and document our expectations. Agents are familiar with best practicies for different toolchains, and know what commands to run to e.g. check that two select unit tests in a Rust crate turned green after a code change. We use comments in code files to document the why behind implementation and architecture choices when they may be relevant to future tasks, e.g. to avoid regressions or to clarify that non-obviously needed complexity is indeed needed.
- **Simplicity**: Since agents are trained on basically all code and workflow patterns known to mankind, we heavily lean towards using well-known best practices, naming schemes, style conventions, commands and tools, frameworks and libraries, architecture and code patterns, documentation and comment styles, and project management approaches. We avoid custom, homegrown solutions unless necessary. Of course, a lot of code and documentation is specific to this master thesis project with no well-known alternatives to use instead, but we can still focus on keeping the project analogous/similar to well-known patterns and related projects. That's why we chose a clearly separated monorepo, so that the packages can each independently follow the best conventions for their respective purpose and toolchain and ecosystem. When we implement custom solutions, we heavily focus on rapid onboarding and a simple, accurate abstraction layer. This way agents do not have to understand our custom solutions' internals, but can just use them and rely on them to behave in well-known, expected ways.
- **Documentation**: Every package has its own documentation conventions, described in the package-level `AGENTS.md` files. Many packages keep a local `docs/` subdirectory for extra Markdown, alongside docstrings / comment blocks that tooling can extract into API docs. `scripts/docs-deploy.sh` aggregates those package docs to GitHub Pages.
- **GitHub Issues and PRs**: We follow established GitHub best practices for issues and PRs. Main exception/thing to keep in mind is that we only have one GitHub user identity which all agents and the project owner share. Spin up issues with `gh` to keep formatting clean, e.g.:
    - `gh issue create --title "Refactor symplectic solver" --body-file /tmp/issue.md`
    - `gh pr create --base main --title "Add new orbit search" --body-file /tmp/pr.md`
  We do **not** run GitHub CI; every agent is responsible for running the relevant tests/linters locally before pushing.
  We add a footer when issue/PR body/comment text was written by an agent:
    ```
    ---
    🤖 Author: codex agent on branch `agent/issue-123`
    🤖 Edited by: codex agent on branch `agent/issue-128`
    ```
  This way the project owner and other agents can quickly see which text comes from where, and which text comes from the project owner in particular.
- **Communication**: Jörn prefers a direct tone, optimized for information-transfer and project success, and explicitly frees agents from having to be polite or hold back in any way. Jörn asks agents to push back on mistakes, on unclear or incomplete specs, or other issues.

## Where to Go Next
After reading this file, agents should immediately run `pwd && git status -sb` to confirm what worktree they are in, and whether they have been handed uncommitted changes. This is relevant since uncommitted changes cannot be restored via `git reset ...`. It is often sensible to backup uncommitted changes before overwriting them, e.g. via `cp path/to/file path/to/file.bak.$(date -Iseconds)` to a gitignored (`*.bak.*`) location.

After orienting wrt git, agents should identify which package(s) they will be working on, and read the respective package-level `packages/*/AGENTS.md` files next. The files will reference further readings of which some, or none, may be of interest depending on the agent's assigned issue(s).
