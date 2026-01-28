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
TODO.md                 Task tracking and experiment queue
```

## Quick Commands

```bash
# Rust
cd packages/rust_viterbo
scripts/test.sh                     # Run all tests (debug + release modes)
scripts/test.sh --debug             # Debug tests only (with debug_assert!)
scripts/test.sh --release           # Release tests only (expensive ones)
cargo clippy --workspace            # Lint
cargo fmt --all                     # Format

# Python
cd packages/python_viterbo
uv sync --extra dev                 # Install deps (first time)
uv run pytest                       # Run tests
uv run ruff check src tests         # Lint

# LaTeX
cd packages/latex_viterbo
scripts/build.sh                    # Build PDF + HTML
scripts/lint.sh                     # Lint
scripts/serve.sh                    # Watch mode

# Exploration
scripts/repo-map.py                 # Detailed file tree
```

## Agent Protocol

Long-running project with sequential/parallel agents. Leave the repo clean for the next agent.

### When Assigned a Task

1. **IMPORTANT: Read TODO.md first** to understand context
2. If task isn't in TODO.md, add it before starting
3. Work on specified branch (create if needed)
4. For parallel work: set up git worktree (see `develop-codespace` skill)

### After Completing Work

1. **CRITICAL: Mark task [x] in TODO.md** — agents often forget this
2. Ensure tests pass, no broken code
3. Update docs/comments if behavior changed
4. Remove stale TODOs/comments
5. Commit and push
6. If using worktree: clean up after PR merge

### Parallel Workflows with Git Worktrees

- Multiple agents work simultaneously on different branches
- Each agent works in `/workspaces/worktrees/<task-name>`
- **CRITICAL:** Always use `cd /workspaces/worktrees/<task> && command`
- See `develop-codespace` skill for detailed setup

### Task Management

**IMPORTANT: Don't speculatively add tasks.** Jörn manages the backlog.

Only add tasks when:
- Work is discovered that can't be done now (blocked, out of scope)
- Jörn explicitly requests it
- Use `plan-tasks` skill for adding/reorganizing

### Cleanup & Standards

- Remove misleading content (outdated docs, stale comments, done TODOs)
- Preserve context where needed (explain "why" in code/thesis)
- Prefer standard patterns — agents know them well

### Approval Markers

- `[proposed]` = agent proposal awaiting Jörn's review
- Only Jörn removes these; ambiguous responses don't count

## Skills <!-- workaround: CC web doesn't auto-load skill descriptions -->

Skills in `.claude/skills/` document workflows. Read the relevant skill before starting work of that type.

| Skill | When to read |
|-------|--------------|
| `develop-rust` | Writing Rust code in `packages/rust_viterbo` |
| `develop-python` | Writing Python code in `packages/python_viterbo` |
| `develop-latex` | Editing thesis in `packages/latex_viterbo` |
| `develop-python-rust-interop` | Building/modifying Rust↔Python bindings |
| `develop-codespace` | Changing devcontainer, git worktrees, environment issues |
| `plan-experiments` | Planning or executing research experiments |
| `plan-tasks` | Adding or reorganizing tasks in TODO.md |
| `review-math-docs-code-correspondence` | Verifying code↔thesis mathematical correctness |
| `review-thesis-writing-style` | Reviewing thesis writing quality and style |
| `download-arxiv-papers` | Reading arXiv papers for thesis research |
| `skill-creator` | Creating or editing skills |

Scripts support `--help`.

## Environment

**Currently using:** GitHub Codespaces (primary), `.devcontainer/codespace/`

Three environments supported:

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| Rust/Python | Yes | Yes | Yes |
| TeX Live | Yes | Yes | No |
| Git worktrees | Scripts | Manual | No |
| Skills | Work | Work | Broken |

**Local:** Backup, full-featured with bind mounts
**Codespace:** Primary, has TexLive for thesis builds
**CC Web:** Emergency backup only, limited features

See `.devcontainer/README.md` and `develop-codespace` skill for details.

## Mathematical Context

- **HK-O 2024:** 10-facet counterexample (smallest known)
- **HK2017:** github.com/pazithaimkislev/EHZ-capacity (reference implementation)
- **Haim-Kislev MSc thesis:** Use `download-arxiv-papers` skill if needed

## Communication

- Jörn reads the **final message** of each turn
- Use numbered lists for easy reference
- Be direct and concrete
- Pushback welcome when unclear

