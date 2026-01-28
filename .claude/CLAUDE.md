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
scripts/repo-map.sh                 # Detailed file tree
```

## Onboarding

- Skills in `.claude/skills/` document workflows. Key ones: `rust-conventions`, `python-conventions`, `experiment-workflow`
- Scripts support `--help`
- Research findings go in `packages/latex_viterbo/chapters/appendix-research-ledger.tex`

## Environment

| Dependency | Local devcontainer | Claude Code web |
|------------|-------------------|-----------------|
| Rust, Cargo | Yes | Yes |
| Python, uv | Yes | Yes |
| gh CLI | Yes | Auto-installed on startup |
| TeX Live | Yes | No |

## Mathematical Sources

- **Haim-Kislev MSc thesis** (simplex capacity, sys ≤ 3/4 claim): Online access available. Agents should find and download if needed for citations.
- **HK-O 2024 counterexample:** 10 facets is the smallest known. Nobody has found counterexamples with fewer facets.
- **HK2017 reference implementation:** github.com/pazithaimkislev/EHZ-capacity (no QCQP solver there either).

## Communication with Jörn

- Jörn reads the **final message** of each turn. Put decisions, questions, summaries there.
- Use numbered lists for easy reference. Be direct and concrete.
- Pushback welcome when instructions are unclear or suboptimal.

## Agent Handoffs

Long-running project with sequential/parallel agents. Before ending: clean up stale comments, update research ledger, leave clean git status. See `session-handoff` skill.
