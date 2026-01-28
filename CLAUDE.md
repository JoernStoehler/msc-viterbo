# CLAUDE.md

Jörn Stöhler's MSc Thesis at University of Augsburg.

**Topic:** Viterbo's Conjecture states that the systolic ratio c(K)²/Vol(K) ≤ 1 for convex bodies, where c(K) is the EHZ capacity. HK-O 2024 disproved this with a 10-facet counterexample (pentagon × rotated pentagon, sys ≈ 1.047). This thesis computationally probes the boundary cases to find new conjectures.

## Timeline & Goals

- **Deadline:** End of March 2026 (project frozen, thesis printed, grade received)
- **Advisor:** Kai (pure mathematician). Last meeting: 2026-01-26.
- **Focus:** Code correctness first, then experiments to discover conjectures a mathematician may later prove (proving conjectures is out of scope).
- No intermediate milestones or defense talk currently planned.

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
scripts/test-rust.sh                # Run all tests (debug + release modes)
scripts/test-rust.sh --debug        # Debug tests only (with debug_assert!)
scripts/test-rust.sh --release      # Release tests only (expensive ones)
cargo clippy --workspace            # Lint
cargo fmt --all                     # Format

# Python
cd packages/python_viterbo
uv sync --extra dev                 # Install deps (first time)
uv run pytest                       # Run tests
uv run ruff check src tests         # Lint

# Exploration
scripts/repo-map.py                 # Detailed file tree
```

## Agent Protocol

Long-running project with sequential/parallel agents. Leave the repo clean for the next agent.

**When assigned a task:**
1. **Read `TODO.md`** to understand your task in context
2. If task isn't in TODO.md, add it before starting
3. Work on the branch specified in your assignment (create if needed)
4. **For parallel work**: Set up a git worktree (see `develop-codespace` skill)

**After completing work:**
1. **Mark task `[x]` in TODO.md** — don't forget this step
2. Ensure branch is PR-able (tests pass, no broken code)
3. Update docs/comments if you changed behavior
4. Remove stale TODOs or comments you created
5. Commit and push
6. **If using worktree**: Clean up after PR merge (see `develop-codespace` skill)

**Parallel agent workflows:**
- Multiple agents can work simultaneously using git worktrees
- Each agent works in `/workspaces/worktrees/<task-name>` on its own branch
- Use `cd /workspaces/worktrees/<task-name> && command` for all operations
- See `develop-codespace` skill for setup and patterns

**Task management:**
- **Don't speculatively add tasks.** Jörn manages the backlog.
- Only add new tasks when work is discovered that can't be done now (blocked, out of scope) or Jörn requests it
- Use `plan-tasks` skill when you need to add or reorganize tasks

**Cleanup principles:**
- Remove misleading content (outdated docs, stale comments, done TODOs)
- Preserve context where needed (explain "why" in code comments, thesis)
- Prefer standard patterns over custom solutions — agents know standard patterns well

**Approval markers:**
- `[proposed]` — agent proposal awaiting Jörn's review
- Only Jörn removes these markers; ambiguous responses ("sounds fine") don't count

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
| `download-arxiv-papers` | Need to read an arXiv paper's actual content |
| `official-claude-code-guides` | Questions about Claude Code itself |
| `create-skill` | Creating or editing skills |

Scripts support `--help`.

## Environment

**Currently using**: GitHub Codespaces (VSCode IDE extension in browser)

Three environments supported (see `.devcontainer/README.md` for details):

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| Rust, Cargo | Yes | Yes | Yes |
| Python, uv | Yes | Yes | Yes |
| gh CLI | Yes | Yes | Auto-installed |
| TeX Live | Yes | Yes | No |
| Git worktrees | Scripts | Manual | No |
| Skills | Work | Work | Broken |
| Parallel agents | Scripts | Worktrees + IDE | No |

**Local**: `.devcontainer/local/` - Full-featured, bind mounts (backup environment)
**Codespace**: `.devcontainer/codespace/` - Primary environment, has TexLive
**CC Web**: `.devcontainer/ccweb/` (docs only) - Emergency backup only

## Mathematical Sources

- **Haim-Kislev MSc thesis** (simplex capacity, sys ≤ 3/4 claim): Online access available. Agents should find and download if needed for citations.
- **HK-O 2024 counterexample:** 10 facets is the smallest known. Nobody has found counterexamples with fewer facets.
- **HK2017 reference implementation:** github.com/pazithaimkislev/EHZ-capacity (no QCQP solver there either).

## Communication with Jörn

- Jörn reads the **final message** of each turn. Put decisions, questions, summaries there.
- Use numbered lists for easy reference. Be direct and concrete.
- Pushback welcome when instructions are unclear or suboptimal.

