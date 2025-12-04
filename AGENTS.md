# AGENTS.md
- Project: Jörn Stöhler's MSc Thesis at University of Augsburg.
- Topic: Probing Viterbo's Conjecture for convex polytopes using computational methods.
- Monorepo with 
  - `packages/latex_viterbo`: Thesis write-up. Source of truth that the other packages are based on.
  - `packages/rust_viterbo`: Rust library for geometric computations, with FFI bindings.
  - `packages/python_viterbo`: Python experiments for data science, ML, and visualization.
  - `.devcontainer/`: The single development environment used by all agents and project owner. The environment is provided ready-to-use.
- Developers: project owner, codex agents
- Project management: GitHub Issues and PRs, git worktrees for isolated environments.

## Onboarding
- We use progressive disclosure, agents can triage their own onboarding by reading files they find relevant to their task.
- Use `bash -lc scripts/hello.sh` to get started, it prints basic info and lists the repository structure.
- Most information as always can be learned from the repo files themselves. Extra explicit information about workflows, conventions, and context can be found in `AGENTS.md`, `agent_docs/`, `packages/*/AGENTS.md`, and `packages/*/agent_docs/`.
- Convience scripts are in `scripts/` and `packages/*/scripts/`. They support `--help` for extra info.

## Communication with Project Owner
- Jörn is available for questions, especially questions about ambiguous phrasings and missing context.
- Jörn appreciates pushback when he writes something unclear, makes mistakes or suggests something suboptimal.
- Be direct, literal, and optimize for Jörn's time when you write a turn's final message. Structure your message to allow skimming. Use numbered lists to make referencing easier.
- Make direct, explicit requests for permissions, clarifications, reviews, feedback and decisions when needed.
- Use Jörn's time wisely. Don't delegate work to him that you can do yourself.
- Leave long-term thesis project management to Jörn, you can help but he has more experience with long-running academic projects.