# CLAUDE.md
Jörn Stöhler's MSc Thesis on Viterbo's Conjecture (University of Augsburg).

## Context
- **Title:** Probing Viterbo's Conjecture
- **Topic:** Viterbo's Conjecture (systolic ratio <= 1) was disproved by HK-O 2024. This thesis computationally probes boundary cases to discover new conjectures.
- **Start Date:** October 2025
- **Deadline:** End of March 2026
- **Priority:** Correctness >> Clarity >> Performance
- **Advisor:** Prof. Kai Cieliebak
- **Repository:** github.com/JoernStoehler/msc-viterbo

## Components

### Library for Symplectic Geometry
- `crates/`: Rust workspace.
  - `geom2d/`, `geom4d/`: General-purpose libraries for symplectic geometry on polytopes
  - `hk2017/`, `billiard/`, `tube/`: EHZ capacity algorithms (stubs)
  - `ffi/`: PyO3 bindings

### Experiments for Rapid Scientific Iteration
- `experiments/`: Python pipeline scripts
  - `_example/`: Example showcase of conventions and best practices
- `data/`: Generated data from experiment pipelines

### Master Thesis
- `thesis/`: LaTeX source of the thesis
  - `talk-clarke-duality/`: A talk given on January 14, 2026

### Task Management
- `tasks/`: Local task tracking in GTD style instead of GitHub issues
  - `ROADMAP.md`: High-level roadmap
  - `inbox/`, `next/`, `active/`, `waiting/`, `done/`: Task states (see `tasks/CLAUDE.md`)

### Project Infrastructure
- `scripts/`: Helper scripts for the project
- `docs/`:
  - `investigations/`: Agent-written reports (`<YYYY-MM-DD>-<description>.md`)
  - `papers/`: Downloaded papers
- `.claude/`:
  - `skills/`: Procedural knowledge bundles for agents
  - `agents/`: Reusable Task() subagent prompts
  - `hooks/`, `settings.json`: Claude Code configuration
- `.devcontainer/`: Explicitly defined environments

## Basic Protocol For Agents

### Environment and Worktrees
- The environment is automatically provisioned and ready-to-use.
- **Task agents:** Work in your assigned worktree (`/workspaces/worktrees/<task>`). Your prompt specifies the path.
- **PM agents:** Work in the main repo (`/workspaces/msc-viterbo`) on `main`.
- Use `cd <worktree-path> && command` when executing commands in a worktree.

### Knowledge Base

The project is explicitly documented. Check the repository before asking.

**Where knowledge lives:**
- `CLAUDE.md` files — Rules and conventions (auto-loaded when reading files in that directory)
- `.claude/skills/` — Procedures and workflows (descriptions shown at startup; read skill when needed)
- `docs/investigations/` — One-off research reports

**Existing CLAUDE.md files:**
- `/CLAUDE.md` — This file (project context, agent protocol)
- `crates/CLAUDE.md` — Rust workspace conventions
- `thesis/CLAUDE.md` — LaTeX and writing conventions
- `experiments/CLAUDE.md` — Python experiment conventions
- `tasks/CLAUDE.md` — Task tracking format
- `docs/CLAUDE.md` — Documentation structure
- `.devcontainer/CLAUDE.md` — Environment configurations

**To extend the knowledge base**, see the `knowledge-base` skill.

### Escalation
- Escalate always and early to Jörn when:
  - The task is ambiguous or contradictory
  - Out-of-scope decisions are needed
  - Desired context is unavailable
  - You are not confident to proceed
- Provide context for Jörn when escalating, as he may manage multiple agents in parallel.

### Communication
- Jörn reads only the **final message** of your turn. Put decisions/questions/summaries there.
- **Explicit approval only.** Status updates are not instructions. Partial responses are not confirmation.
- `[proposed]` markers await Jörn's review. Only Jörn removes them.
- Be direct and concrete. Avoid filler phrases.
- Don't delegate work to Jörn that you can do yourself.
- Optimize for effective information transfer to and from Jörn, over politeness or conciseness.

### Cleanup and Wrap-up
- Remove misleading content (outdated docs, stale comments).
- Mark uncertainties clearly.
- Update docs when discovering process gaps.
- Repeat unaddressed points, questions, follow-ups.

### Usual Session Flow
- Jörn and/or another agent prepare the worktree and a prompt
- Jörn starts a "claude code ide" session and hands the prompt to a new agent (you)
- You investigate and plan what you will do, you escalate, you ask clarifying questions, you let Jörn help you if needed
- You explain the plan to yourself & Jörn and get approval from Jörn
- You execute the plan, adapt as you go, escalate when Jörn's help is needed
- You clean up and bring your work into an explainable, handoff-ready state
- When ready for review: push changes, create PR, verify CI passes, then summarize for Jörn (what's done, what to review, any concerns)
- You explain the results to yourself & Jörn and get approval from Jörn
- Jörn starts a new parallel session with a new agent who reviews your work together with Jörn
- You may be told your work was accepted and handed off to another agent, or you may be told to return to the planning/implementation phase
- After hand-off (acceptance or final rejection) you will be asked for a post-mortem reflection so the knowledge base can be improved steadily
