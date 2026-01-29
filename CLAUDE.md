# CLAUDE.md

Jörn Stöhler's MSc Thesis at University of Augsburg.

**Topic:** Viterbo's Conjecture (systolic ratio ≤ 1) was disproved by HK-O 2024 with a 10-facet counterexample (sys ≈ 1.047). This thesis computationally probes the boundary cases to discover new conjectures.

## Context

- **Deadline:** End of March 2026
- **Priority:** Code correctness first, then experiments
- **Thesis as source of truth:** Code implements what thesis specifies

## Project Layout

```
packages/
  latex_viterbo/        Thesis (source of truth: code implements what thesis specifies)
    chapters/           .tex files; chapters/math/ has core definitions
    assets/             Figures, generated plots
  rust_viterbo/         Rust workspace for geometric computations
    geom/               Polytope representation, convexity, tolerances
    hk2017/             Haim-Kislev 2017 algorithm for EHZ capacity
    billiard/           Billiard trajectory algorithm (Clarke dual)
    tube/               Tube domain capacity computations
    ffi/                PyO3 bindings exposing Rust to Python
  python_viterbo/       Python package for experiments
    src/viterbo/        Package source with experiments/ subdirectory
    config/             JSON configs per experiment
    data/               Output artifacts per experiment
    tests/              pytest tests
scripts/                Repo-wide dev scripts
.devcontainer/          Environment configs (local/, codespace/, ccweb/)
.claude/skills/         Workflow docs (develop-*, plan-*, review-*, etc.)
docs/                   GitHub Pages site
```

## Quick Commands

```bash
# Rust
cd /workspaces/worktrees/<task>/packages/rust_viterbo
scripts/test.sh                     # Run all tests (debug + release modes)
scripts/test.sh --debug             # Debug tests only (with debug_assert!)
scripts/test.sh --release           # Release tests only (expensive ones)
cargo clippy --workspace            # Lint
cargo fmt --all                     # Format

# Python
cd /workspaces/worktrees/<task>/packages/python_viterbo
uv sync --extra dev                 # Install deps (first time)
uv run pytest                       # Run tests
uv run ruff check src tests         # Lint

# LaTeX
cd /workspaces/worktrees/<task>/packages/latex_viterbo
scripts/build.sh                    # Build PDF + HTML
scripts/lint.sh                     # Lint
scripts/serve.sh                    # Watch mode

# Exploration
cd /workspaces/worktrees/<task>/
scripts/repo-map.py                 # Detailed file tree
```

## Agent Protocol

Long-running project with sequential/parallel agents. Leave the repo clean for the next agent.

### When Assigned a Task

1. Work in the directory specified (default: `/workspaces/msc-viterbo`)
2. Read skills relevant to the work
3. Do the work

### After Completing Work

1. Ensure tests pass
2. Commit and push (reference issue via "fixes #X" if applicable)
3. Note any out-of-scope discoveries in PR description

### Working Directory

- **CRITICAL:** Always use `cd /workspaces/worktrees/<task> && command`
- See `develop-codespace` skill for troubleshooting

### Escalation

Escalate to Jörn when:
- Task is ambiguous
- Tests pass but behavior seems wrong
- Spec has a mistake or contradiction
- Any out-of-scope decision needed

A brief interruption beats running into a dead end.

### Task Management

Work tracked in GitHub Issues, Milestones, and Discussions.

- **Don't create issues** - note out-of-scope discoveries in PR description instead
- Issues are created by Jörn or PM agent
- Use `gh issue view/comment` to read and update existing issues
- Add footer for attribution: `---\n*Agent: worktree-name*`
- See `plan-experiments` skill for experiment workflows

### Cleanup & Standards

- Remove misleading content (outdated docs, stale comments, done TODOs)
- Preserve context where needed (explain "why" in code/thesis)
- Prefer standard patterns — agents know them well

### Approval Markers

- `[proposed]` = agent proposal awaiting Jörn's review
- Only Jörn removes these; ambiguous responses don't count

## Environment

The environment is provisioned for you, and everything should work out of the box.
See `develop-codespace` skill for troubleshooting.

## Communication

- Jörn only reliably reads the **final message** of each turn. Structure accordingly: put decisions, questions, and summaries at the end, not interspersed with work updates.
- Jörn is available for questions, especially questions about ambiguous phrasings and missing context.
- Jörn appreciates pushback when he writes something unclear, makes mistakes or suggests something suboptimal.
- Be direct, literal, and optimize for Jörn's time when you write a turn's final message. Structure your message to allow skimming. Use numbered lists to make referencing easier.
- Make direct, explicit requests for permissions, clarifications, reviews, feedback and decisions when needed.
- Use Jörn's time wisely. Don't delegate work to him that you can do yourself.
- Leave long-term thesis project management to Jörn, you can help but he has more experience with long-running academic projects.
- Be precise and concrete, not vague or metaphorical. Don't use pseudo-profound phrases that obscure meaning.
- After making a mistake: pause, think carefully, then state concretely what was done wrong. Don't rush to respond with unclear apologies.
- When explaining conventions or structures: describe the actual purpose and mechanics, not just formatting rules.
