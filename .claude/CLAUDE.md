# CLAUDE.md
- Project: Jörn Stöhler's MSc Thesis at University of Augsburg.
- Topic: Probing Viterbo's Conjecture for convex polytopes using computational methods.
- Monorepo with
  - `packages/latex_viterbo`: Thesis write-up. Source of truth that the other packages are based on.
  - `packages/rust_viterbo`: Rust library for geometric computations, with FFI bindings.
  - `packages/python_viterbo`: Python experiments for data science, ML, and visualization.
  - `.devcontainer/`, `scripts/devcontainer-post-create.sh`, `msc-viterbo.code-workspace`: Local devcontainer configuration for project owner. Agents work in auto-provisioned environments; error messages explain what's available where.
- Developers: project owner, Claude Code agents
- Project management: GitHub Issues + Milestones and PRs, git worktrees for isolated environments.
- Research tracking: Research Ledger appendix in thesis (packages/latex_viterbo/chapters/appendix-research-ledger.tex)
- Agent handoffs: This is a long-running project with many sequential/parallel agents. Always leave the repo ready for the next agent (see session-handoff skill).

## Onboarding
- A SessionStart hook runs `scripts/hello.sh` automatically, printing the repo map and git status.
- We use progressive disclosure, agents can triage their own onboarding by reading files they find relevant to their task.
- Most information as always can be learned from the repo files themselves. Extra explicit information about workflows, conventions, and context lives in `.claude/skills/`.
- Convenience scripts are in `scripts/` and `packages/*/scripts/`. Many support `--help` for extra info.
- We loosely follow literate programming practices, so documentation of the codebase is in the code files.

## Agent Work Practices (CRITICAL)

### Read relevant skills BEFORE working
- If task involves Python/experiments → read `python-conventions/SKILL.md` and `experiment-workflow/SKILL.md`
- If task involves Rust → read `rust-conventions/SKILL.md`
- If task involves LaTeX → read `latex-conventions/SKILL.md`
- Do NOT make up conventions. Follow what's documented. If conventions are missing or unclear, note this and propose additions.

### Cite sources for all claims
- When stating facts about the codebase, cite file paths and line numbers.
- When stating facts from papers or docs, cite the source.
- When estimating (sizes, counts, complexity), state explicitly that it's an estimate and explain the basis.
- Do NOT make up numbers or claim things without sources.

### Do work instead of asking permission
- If you can answer a question by reading files or running commands, do that instead of asking Jörn.
- Do exploratory work BEFORE presenting options. Don't ask "should I look into X?" — just look into X.
- Only ask for permission/decisions when you genuinely cannot proceed without input.
- When presenting options, include your analysis and recommendation, not just "which do you prefer?"

### Be precise
- Use absolute file paths, not ambiguous references.
- Define terms before using them.
- If something is unclear in the codebase, note the ambiguity explicitly.

## Environment Dependencies
Two environments exist: **local devcontainer** (Jörn's machine) and **Claude Code web** (agents). Both support Rust and Python dev. See `.claude/skills/environment/SKILL.md` for details.

| Dependency | Local | Web |
|------------|-------|-----|
| Rust, Cargo | Yes | Yes |
| Python, uv | Yes | Yes |
| gh CLI | Yes | Auto-installed by SessionStart hook |
| TexLive (pdflatex) | Yes | No (apt-get blocked) |

**Python packages:** Run `cd packages/python_viterbo && uv sync --extra dev`

## Communication with Project Owner
- Jörn only reliably reads the final message of each turn. Structure accordingly: put decisions, questions, and summaries at the end, not interspersed with work updates.
- Jörn is available for questions, especially questions about ambiguous phrasings and missing context.
- Jörn appreciates pushback when he writes something unclear, makes mistakes or suggests something suboptimal.
- Be direct, literal, and optimize for Jörn's time when you write a turn's final message. Structure your message to allow skimming. Use numbered lists to make referencing easier.
- Make direct, explicit requests for permissions, clarifications, reviews, feedback and decisions when needed.
- Use Jörn's time wisely. Don't delegate work to him that you can do yourself.
- Leave long-term thesis project management to Jörn, you can help but he has more experience with long-running academic projects.
