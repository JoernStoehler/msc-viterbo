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
.claude/skills/         Workflow docs (rust-conventions, python-conventions, experiment-workflow, ...)
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

**After completing work:**
1. **Mark task `[x]` in TODO.md** — don't forget this step
2. Ensure branch is PR-able (tests pass, no broken code)
3. Update docs/comments if you changed behavior
4. Remove stale TODOs or comments you created
5. Commit and push

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
| `rust-conventions` | Writing Rust code in `packages/rust_viterbo` |
| `rust-testing` | Writing Rust tests (proptest, fixtures, tolerances) |
| `python-conventions` | Writing Python code in `packages/python_viterbo` |
| `latex-conventions` | Editing thesis in `packages/latex_viterbo` |
| `experiment-workflow` | Planning or executing research experiments |
| `ffi-pyo3-maturin` | Building/modifying Rust↔Python bindings |
| `paper-reading` | Need to read an arXiv paper's actual content |
| `quality-improvement` | Refactoring or code quality work |
| `skill-authoring` | Creating or editing skills |
| `worktree-management` | Using git worktrees |
| `environment` | Troubleshooting or modifying dev environments |
| `devcontainer-maintenance` | Changing devcontainer specifically |
| `claude-code-guide` | Questions about Claude Code itself |

Scripts support `--help`.

## Environment

Three environments supported (see `.devcontainer/README.md` for details):

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| Rust, Cargo | Yes | Yes | Yes |
| Python, uv | Yes | Yes | Yes |
| gh CLI | Yes | Yes | Auto-installed |
| TeX Live | Yes | No | No |
| Git worktrees | Manual | Catnip | No |
| Skills | Work | Should work | Broken |

**Local**: `.devcontainer/local/` - Full-featured, bind mounts, TexLive
**Codespace**: `.devcontainer/codespace/` - Catnip for worktrees, no TexLive
**CC Web**: `.devcontainer/ccweb/` (docs only) - Lowest friction, limited features

## Mathematical Sources

- **Haim-Kislev MSc thesis** (simplex capacity, sys ≤ 3/4 claim): Online access available. Agents should find and download if needed for citations.
- **HK-O 2024 counterexample:** 10 facets is the smallest known. Nobody has found counterexamples with fewer facets.
- **HK2017 reference implementation:** github.com/pazithaimkislev/EHZ-capacity (no QCQP solver there either).

## Communication with Jörn

- Jörn reads the **final message** of each turn. Put decisions, questions, summaries there.
- Use numbered lists for easy reference. Be direct and concrete.
- Pushback welcome when instructions are unclear or suboptimal.

