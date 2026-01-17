# CLAUDE.md
- Project: Jörn Stöhler's MSc Thesis at University of Augsburg.
- Topic: Probing Viterbo's Conjecture for convex polytopes using computational methods.
- Monorepo with
  - `packages/latex_viterbo`: Thesis write-up. Source of truth that the other packages are based on.
  - `packages/rust_viterbo`: Rust library for geometric computations, with FFI bindings.
  - `packages/python_viterbo`: Python experiments for data science, ML, and visualization.
  - `.devcontainer/`, `scripts/devcontainer-post-create.sh`, `msc-viterbo.code-workspace`: Local devcontainer configuration for project owner. Agents work in auto-provisioned environments and install dependencies on-demand via error messages.
- Developers: project owner, Claude Code agents
- Project management: GitHub Issues + Milestones and PRs, git worktrees for isolated environments.
- Research tracking: Research Ledger appendix in thesis (packages/latex_viterbo/chapters/appendix-research-ledger.tex)
- Agent handoffs: This is a long-running project with many sequential/parallel agents. Always leave the repo ready for the next agent (see session-handoff skill).

## Onboarding
- A SessionStart hook runs `scripts/hello.sh` automatically, printing the repo map and git status.
- We use progressive disclosure, agents can triage their own onboarding by reading files they find relevant to their task.
- Most information as always can be learned from the repo files themselves. Extra explicit information about workflows, conventions, and context lives in `.claude/skills/`.
- Convenience scripts are in `scripts/` and `packages/*/scripts/`. They support `--help` for extra info.
- We loosely follow literate programming practices, so documentation of the codebase is in the code files.

## Environment Dependencies
- **TexLive:** Local devcontainer only (apt-get blocked in web environment). If `pdflatex` not found locally, run: `./packages/latex_viterbo/scripts/install-texlive.sh`
- **Python packages:** Run `cd packages/python_viterbo && uv sync --extra dev` to install dependencies (includes pytest, maturin, etc.)
- **Rust:** Should be pre-installed in most environments. Check with `rustc --version`

## Communication with Project Owner
- Jörn only reliably reads the final message of each turn. Structure accordingly: put decisions, questions, and summaries at the end, not interspersed with work updates.
- Jörn is available for questions, especially questions about ambiguous phrasings and missing context.
- Jörn appreciates pushback when he writes something unclear, makes mistakes or suggests something suboptimal.
- Be direct, literal, and optimize for Jörn's time when you write a turn's final message. Structure your message to allow skimming. Use numbered lists to make referencing easier.
- Make direct, explicit requests for permissions, clarifications, reviews, feedback and decisions when needed.
- Use Jörn's time wisely. Don't delegate work to him that you can do yourself.
- Leave long-term thesis project management to Jörn, you can help but he has more experience with long-running academic projects.
