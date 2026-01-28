# OLD SKILLS ARCHIVE

**Warning:** This file is a historical record only. The content here may be:
- Incomplete or missing important information
- Misleadingly worded or confusingly structured
- Verbose without being clear
- Outdated or possibly incorrect

This archive exists solely to preserve factual and procedural knowledge from the old skills while new, high-quality skills are written from scratch.

**Date archived:** 2026-01-28

---


# SKILL: develop-codespace

## FILE: develop-codespace/SKILL.md

---
name: develop-codespace
description: Maintain or change the devcontainer environments for this repo. Use when editing .devcontainer files, changing toolchains, or requesting environment rebuilds.
---

# Codespace Development Environment

**When to use this skill:**
- You're modifying or extending the environment setup
- You encounter environment-related errors and need deeper context
- You need to understand git worktrees for parallel agent workflows
- You're troubleshooting environment issues

---

## Environment Architecture

This project supports **three environments**:

| Environment | Config Location | Use Case |
|-------------|-----------------|----------|
| **Codespace** | `.devcontainer/codespace/` | **Primary** - GitHub Codespaces |
| Local | `.devcontainer/local/` | Jörn's Ubuntu desktop |
| CC Web | `.devcontainer/ccweb/` (docs only) | Claude Code Web |

### Codespace (Primary Environment)

- **Defined by**: `.devcontainer/codespace/devcontainer.json`, `.devcontainer/codespace/Dockerfile`
- **Post-create**: `.devcontainer/scripts/post-create.sh`
- **What it does**: Cloud dev environment
- **Special features**:
  - Full TexLive installation for PDF builds
  - LaTeXML for HTML conversion
  - Manual git worktrees via `git worktree` commands
  - Parallel agent workflows (worktrees + IDE extension)
- **Known limitations**:
  - Auto-stops after idle period
  - OAuth may not persist across rebuilds
  - Caches don't persist across rebuilds

### Local Devcontainer

- **Defined by**: `.devcontainer/local/devcontainer.json`, `.devcontainer/local/Dockerfile`
- **Post-create**: `.devcontainer/scripts/post-create.sh`
- **Host scripts**: `.devcontainer/local/host-*.sh`
- **Special features**:
  - Bind mounts for cache persistence (`/srv/devhome/*` → `/home/vscode/*`)
  - Manual git worktrees via `/workspaces/worktrees/`
  - Shared Rust build cache via `CARGO_TARGET_DIR=/workspaces/worktrees/shared/target`
  - Full TexLive installation for PDF builds
  - VS Code tunnel for remote access

### Claude Code Web

- **Defined by**: Ubuntu 24.04 base (no devcontainer)
- **Docs**: `.devcontainer/ccweb/README.md`
- **What's pre-installed**: Rust, Python (with uv), Node.js, Git, build-essential
- **What's NOT pre-installed**: TexLive, latexml, Playwright browsers

**Critical limitations (as of Jan 2026):**
- apt-get does NOT work (DNS blocked by proxy architecture)
- Skills are broken (names/descriptions not autoloaded)
- Playwright cannot install browsers
- No git worktrees support

---

## What's Available Where

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| TexLive (pdflatex, chktex) | Yes | Yes | No |
| latexml | Yes | Yes | No |
| Rust (cargo, rustc) | Yes | Yes | Yes |
| Python + uv | Yes | Yes | Yes |
| gh CLI | Yes | Yes | Auto-installed |
| Playwright | Yes | Yes | No |
| Git worktrees | Manual scripts | Manual | No |
| Parallel agents | Scripts | Worktrees + IDE | No |
| Cache persistence | Bind mounts | No | No |
| Skills | Work | Work | Broken |

---

## Environment Detection

```bash
# Devcontainer environment (local or codespace)
if [[ "${DEVCONTAINER_ENV:-}" == "local" ]]; then
  echo "Running in local devcontainer"
elif [[ "${DEVCONTAINER_ENV:-}" == "codespace" ]]; then
  echo "Running in GitHub Codespace"
elif [[ -n "${CODESPACES:-}" ]]; then
  echo "Running in Codespace (env var not set)"
elif [[ -n "${CLAUDE_CODE_REMOTE:-}" ]]; then
  echo "Running in Claude Code Web"
else
  echo "Unknown environment"
fi
```

---

## Modifying Environments

### Policy

- Environment changes must be approved by the project owner.
- Make changes in the devcontainer definition files (no ad-hoc local installs).
- Rebuild required after changes.
- No default devcontainer.json - explicit selection required.

### Shared Files

- `.devcontainer/scripts/post-create.sh` - Post-create script (env-aware)
- `.devcontainer/scripts/warmup-cache.sh` - Background cache warming
- `.devcontainer/README.md` - Overview documentation

### Adding Dependencies

**For Python packages** (works in all environments):
1. Add to `packages/python_viterbo/pyproject.toml`
2. Run `uv sync --extra dev`

**For Rust crates** (works in all environments):
1. Add to `packages/rust_viterbo/*/Cargo.toml`
2. Run `cargo build`

**For system dependencies** (local/codespace only):
1. Add to `.devcontainer/local/Dockerfile` and/or `.devcontainer/codespace/Dockerfile`
2. Update build scripts to fail gracefully in CC web

### Creating a Codespace

```bash
gh codespace create -r JoernStoehler/msc-viterbo \
    --devcontainer-path .devcontainer/codespace/devcontainer.json
```

### Running Local Devcontainer

```bash
# From host machine:
.devcontainer/local/host-devcontainer-rebuild.sh
.devcontainer/local/host-vscode-tunnel.sh
```

---

## Git Worktrees for Parallel Agents

### Purpose

Git worktrees enable multiple agents to work in parallel on different branches without interfering with each other. Each worktree is an isolated working directory with its own branch and files, while sharing the same Git history.

### Quick Start (Codespaces + IDE Extension)

#### Setup

```bash
# Create worktree for your task
git worktree add /workspaces/worktrees/<task-name> -b <branch-name>

# Example:
git worktree add /workspaces/worktrees/fix-billiard-bug -b fix-billiard-bug
```

#### Working Pattern

**CRITICAL**: The VSCode IDE extension uses `/workspaces/msc-viterbo` as the working directory. You **must** use `cd` in every bash command:

```bash
# Always cd before running commands
cd /workspaces/worktrees/fix-billiard-bug && packages/rust_viterbo/scripts/test.sh
cd /workspaces/worktrees/fix-billiard-bug && git status
cd /workspaces/worktrees/fix-billiard-bug && cargo test

# Chain multiple commands
cd /workspaces/worktrees/fix-billiard-bug && cargo fmt && cargo clippy && git add .
```

#### Common Operations

```bash
# Run Rust tests
cd /workspaces/worktrees/<task-name> && cargo test

# Run Python tests
cd /workspaces/worktrees/<task-name> && cd packages/python_viterbo && uv run pytest

# Format and lint Rust
cd /workspaces/worktrees/<task-name> && cargo fmt --all
cd /workspaces/worktrees/<task-name> && cargo clippy --workspace

# Git operations
cd /workspaces/worktrees/<task-name> && git status
cd /workspaces/worktrees/<task-name> && git add .
cd /workspaces/worktrees/<task-name> && git commit -m "Fix bug"
cd /workspaces/worktrees/<task-name> && git push -u origin <branch-name>
```

#### Cleanup

After your PR is merged:

```bash
# Remove the worktree (branch stays on GitHub as PR history)
git worktree remove /workspaces/worktrees/<task-name>

# Verify it's gone
git worktree list
```

### Key Limitations

#### 1. Skills and CLAUDE.md Read from Main Repo

The VSCode IDE extension operates from `/workspaces/msc-viterbo`, so:
- Skills in `.claude/skills/` are read from **main repo**, not your worktree
- `CLAUDE.md` is read from **main repo**, not your worktree
- Custom commands in `.claude/commands/` are from **main repo**

**Implication**: This workflow works best when worktrees don't diverge significantly from `main` in terms of workflow docs.

#### 2. Working Directory Behavior

The IDE extension sets its working directory to the **root folder** of the VSCode window (`/workspaces/msc-viterbo`). You cannot change this via `cd` commands in bash — you must explicitly `cd` in every bash command you run.

#### 3. No Shared Build Cache

Each worktree builds independently. Cold start takes ~60 seconds to build Rust crates. This is acceptable for parallel agent workflows.

#### 4. VSCode Multi-Root Workspace Bug

There's a [known bug](https://github.com/anthropics/claude-code/issues/8559) where the IDE extension always uses the first folder in multi-root workspaces. **Workaround**: Don't use multi-root workspaces — use separate browser tabs or the terminal CLI if you need true parallelism.

### Persistence Across Rebuilds

Worktrees under `/workspaces/` persist across Codespace container rebuilds. This is the **only** directory that survives rebuilds, so always use `/workspaces/worktrees/` for worktrees.

### Alternative: Terminal CLI for Parallelism

If the IDE extension's `cd` requirement becomes too high friction, fall back to the terminal CLI:

```bash
# Create worktree
git worktree add /workspaces/worktrees/task-a -b task-a

# Open new terminal tab/pane in VSCode
cd /workspaces/worktrees/task-a
claude  # Run CLI session here
```

Terminal CLI sessions:
- Have full feature parity with IDE extension
- Operate in the directory where you run `claude`
- Support tmux/screen for session management
- Lack the GUI's visual polish (diffs, nice rendering)

### Worktree Commands Reference

```bash
# List all worktrees
git worktree list

# Remove a worktree
git worktree remove <path>

# Remove a worktree with uncommitted changes (force)
git worktree remove <path> --force

# Prune stale worktree references
git worktree prune
```

### Workflow Example

```bash
# 1. Agent receives task: "Fix billiard trajectory bug"
git worktree add /workspaces/worktrees/fix-billiard -b fix-billiard

# 2. Work in the worktree (remember to cd!)
cd /workspaces/worktrees/fix-billiard && cargo test --package billiard
# ... fix the bug ...
cd /workspaces/worktrees/fix-billiard && cargo test --package billiard
cd /workspaces/worktrees/fix-billiard && git add .
cd /workspaces/worktrees/fix-billiard && git commit -m "Fix billiard trajectory calculation"
cd /workspaces/worktrees/fix-billiard && git push -u origin fix-billiard

# 3. Create PR (can run from anywhere since gh uses remote)
gh pr create --title "Fix billiard trajectory calculation" --body "..."

# 4. After PR merge, clean up
git worktree remove /workspaces/worktrees/fix-billiard
```

---

## Files to Read

- `.devcontainer/README.md` - Overview of all environments
- `.devcontainer/local/devcontainer.json` - Local config
- `.devcontainer/codespace/devcontainer.json` - Codespace config
- `.devcontainer/ccweb/README.md` - CC web limitations
- `.devcontainer/scripts/post-create.sh` - Shared post-create script

---


# SKILL: develop-latex

## FILE: develop-latex/SKILL.md

---
name: develop-latex
description: Work on the LaTeX thesis or LaTeXML HTML output. Use for build/lint/serve commands, LaTeX style rules, HTML pipeline notes, or assets conventions.
---

# LaTeX Conventions (thesis + HTML)

## Build and serve (packages/latex_viterbo)

**Note:** LaTeX builds require TexLive, which is available in local and codespace devcontainers (not in Claude Code Web environment).

- Lint: `scripts/lint.sh` (chktex + draft compile + latexml sanity)
- Build: `scripts/build.sh [--production] [--pdf-only] [--html-only]`
- Serve: `scripts/serve.sh [--production] [--watch] [--pdf-only] [--html-only]`
- Draft speedup: use `includeonly.tex` (copy from `includeonly.tex.example`).

## LaTeX style

- Use `\(...\)` inline, `\[...\]` display (avoid `$`).
- Proofs in `proof` environment; label theorems/lemmas consistently.
- arXiv-friendly packages only.

## Thesis writing style

- Audience: symplectic geometers; self-contained exposition.
- Separate mainline text from asides.
- Introduce notation once; note deviations from literature.
- Be explicit but skimmable; spoilers up front; headings guide the reader.
- Mark WIP text clearly (e.g., `\edit{}` or `%`).

## Assets

- LaTeX includes assets; Python generates them.
- Store under `packages/latex_viterbo/assets/<experiment>/...`.
- LaTeXML extras under `packages/latex_viterbo/assets/{html/,latexml/}`.
- Hand-crafted assets under `packages/latex_viterbo/assets/manual/`.

## References

- LaTeXML HTML pipeline notes: `references/ar5iv-pipeline-notes.md`
- LaTeXML troubleshooting: `references/latexml-troubleshooting.md`
- Clarke talk teardown checklist: `packages/latex_talk_clarke_duality/docs/teardown.md`

---

## FILE: develop-latex/references/ar5iv-pipeline-notes.md

# ar5iv / ar5ivist pipeline cheat‑sheet

Goal: understand the closest public analogue to arXiv’s HTML pipeline and how to mirror its look in our LaTeXML builds.

## Repos of interest
- `dginev/ar5iv` — Rocket/Redis service that serves pre‑converted LaTeXML HTML for arXiv papers; conversion still LaTeXML. https://github.com/dginev/ar5iv
- `dginev/ar5iv-css` — CSS/theme used by ar5iv and imported by arXiv HTML pages. https://github.com/dginev/ar5iv-css
- `dginev/ar5ivist` — Turnkey CLI (Docker) that runs LaTeXML with ar5iv bindings + CSS; shows flags/commits ar5iv uses. https://github.com/dginev/ar5ivist
- `arXiv/zzzArchived_arxiv-readability` — archived Engrafo fork from the early arXiv HTML pilot. https://github.com/arXiv/zzzArchived_arxiv-readability

## What we now do by default (local pipeline)
- We run `scripts/build.sh` with the ar5ivist flag set (preloads, token/time limits) and vendored ar5iv bindings cloned to `assets/latexml/ar5iv-bindings` (commit 847b4835…).
- HTML DOM is postprocessed to match arXiv: `<nav class="ltx_page_navbar"><nav class="ltx_TOC active">…</nav></nav><div class="ltx_page_main">…</div>`.
- CSS is the vendored arXiv/ar5iv bundle (`assets/html/css/*`) copied into the output; no CDN dependency.
- PDF builds are unchanged; no feedback/overlay JS is loaded.
- LaTeXML remains the system 0.8.8 for now (not pinned to the ar5ivist commit).

## ar5ivist (what arXiv-like conversion looks like)
- Docker image: `latexml/ar5ivist:2509.16`.
- Entry point (from `ar5ivist/Dockerfile`):
  - `latexmlc --preload=[nobibtex,rawstyles,nobreakuntex,magnify=1.3,zoomout=1.3,tokenlimit=249999999,iflimit=3999999,absorblimit=1299999,pushbacklimit=599999]latexml.sty`
  - `--preload=ar5iv.sty`
  - `--path=/opt/ar5iv-bindings/bindings --path=/opt/ar5iv-bindings/supported_originals`
  - `--format=html5 --pmml --mathtex --timeout=2700`
  - `--noinvisibletimes --nodefaultresources`
  - `--css=https://cdn.jsdelivr.net/gh/dginev/ar5iv-css@0.8.4/css/ar5iv.min.css`
  - `--css=https://cdn.jsdelivr.net/gh/dginev/ar5iv-css@0.8.4/css/ar5iv-fonts.min.css`
- Base image pins:
  - LaTeXML commit `25ec2b0e9070cc05cbb5e5e22bebf5ba98a0d86c`.
  - ar5iv-bindings commit `847b4835448d17065d612c04b52c4a373ec0fd15`.
  - Ubuntu 24.04 with full texlive.

## How to approximate locally (what we now do)
- Keep using `latexmlc` for conversion.
- Postprocess HTML to load the arXiv/​ar5iv CSS bundle (`arxiv-html-papers-20250916.css`, which imports `ar5iv.0.8.4.css` and a small theme file).
- Wrap the TOC in a `ltx_page_navbar` container to get the left-rail layout.
- Opt-out via `USE_HTML_SKIN=0` if pure LaTeXML output is desired.

### Quick contrast: us vs. ar5iv/arXiv
- **We do (default in scripts/build.sh):** plain `latexmlc` + post-injected ar5iv/​arXiv CSS + TOC-left wrapper; no special LaTeXML preloads, timeouts, or binding paths.
- **ar5ivist does:** `latexmlc` with ar5iv-specific preloads (`latexml.sty` options, `ar5iv.sty`), custom binding paths, high token/time limits, and remote CSS from ar5iv-css CDN.
- **arXiv production likely does:** LaTeXML 0.8.x with proprietary static assets/JS; not publicly published. Presentation layer matches ar5iv-css + arXiv theme we vendor here.

## How to reproduce ar5ivist exactly (if needed)
```bash
docker run -v \"$PWD\":/docdir -w /docdir --user \"$(id -u):$(id -g)\" \
  latexml/ar5ivist:2509.16 --source=main.tex --destination=html/main.html
```
Notes: Docker is confined to the working dir; no `../` paths. Logs land in `main.latexml.log`.

## What’s still private
- arXiv’s production converter container is not published; only static assets (CSS/JS) are public. The approach above matches presentation and LaTeXML version/flags closely without depending on private images.

---

## FILE: develop-latex/references/latexml-troubleshooting.md

# LaTeXML / latexmlc Troubleshooting Links (quick reference)

Curated links for diagnosing LaTeXML/latexmlc build issues, HTML output problems, and environment choices. Keep this link-heavy; minimal prose.

## Core resources
- Official repo (issues, releases, bindings): https://github.com/brucemiller/LaTeXML
- Official manual (0.8.8, Feb 26 2024): https://math.nist.gov/~BMiller/LaTeXML/manual/
- Release notes 0.8.8 (breaking changes, MathML tweaks): https://newreleases.io/project/github/brucemiller/LaTeXML/release/v0.8.8
- Contacts/support page (mailing list, issue tracker): https://math.nist.gov/~BMiller/LaTeXML/contact.html

## Docker images / environments
- kjarosh/latex-docker (Alpine TL2025 variants; easy `docker cp` for fresh latexml/tex binaries): https://github.com/kjarosh/latex-docker
- xu-cheng/latex-docker (TL latest + historic tags on Debian/Alpine): https://github.com/xu-cheng/latex-docker
- dante-ev/docker-texlive (full TL images with extras): https://github.com/dante-ev/docker-texlive
- maxkratz/docker_texlive (versioned TL 2016–2025 images): https://github.com/maxkratz/docker_texlive
- arXiv compiler/converter image (archived 2025-01-28; ECR-gated but documents layout): https://github.com/arXiv/arxiv-compiler

## HTML rendering stacks using LaTeXML
- arXiv Vanity / Engrafo Docker image (LaTeXML-based HTML renderer): https://github.com/arxiv-vanity/engrafo
- arXiv Vanity runner (uses engrafo image via docker-compose): https://github.com/arxiv-vanity/arxiv-vanity

## Common failure points & quick checks
- Class binding missing (e.g., `memoir`): verify binding list in manual’s Appendix B; consider `\iflatexml` class switch to `article` or ship a custom binding.
- Package not recognized: check for existing binding; if absent, add `--preload=<package>.ltxml` or create minimal binding in `local/`.
- Bibliography style unsupported: switch to `plain`/`alpha` for latexml, or pre-generate `.bbl` and call `latexmlc --bibtex --preload=... main.tex`.
- Stalls in post-processing: rerun with `--loglevel=info --debug`; add `--noparse` to isolate digestion vs postprocessing issues.
- Math layout regressions after 0.8.8: note `ltx:inline-para` renamed to `ltx:inline-logical-block` (see release notes above).

## Minimal reproduction templates
- Run inside fresh TL+LaTeXML container:
  ```bash
  docker run --rm -v "$PWD":/src -w /src kjarosh/latex:2025.1 latexmlc --destination=out.html main.tex
  ```
- If class binding missing, stub for HTML runs:
  ```tex
  \ifdefined\latexml
    \documentclass{article}
  \else
    \documentclass{memoir}
  \fi
  ```

## When to upgrade
- If latexmlc errors mention outdated LaTeX kernel: use a TL 2024+ image (above) or build LaTeXML from master; 0.8.8 release date 2024-02-29.
- For arXiv parity: target TL2023+; arXiv’s current toolchain is 2023-era according to their FAQ (see arXiv links above).

---


# SKILL: develop-python

## FILE: develop-python/SKILL.md

---
name: develop-python
description: Creating or modifying Python code in packages/python_viterbo. Covers directory layout, stage entrypoints, config files, data outputs, tests, lint commands.
---

# Python Conventions

## Example: example-pipeline

Study `src/viterbo/experiments/example_pipeline/` before creating experiments:

```
src/viterbo/experiments/example_pipeline/
├── SPEC.md           # Research question, method, success criteria
├── stage_build.py    # Stage 1: generate data
├── stage_analyze.py  # Stage 2: compute results
└── stage_plot.py     # Stage 3: create figures

config/example-pipeline/
└── default.json      # Parameters for reproducible runs

data/example-pipeline/
├── synthetic_data.json
└── results.json

tests/test_example_pipeline.py
```

Run stages:
```bash
uv run python -m viterbo.experiments.example_pipeline.stage_build
uv run python -m viterbo.experiments.example_pipeline.stage_analyze
uv run python -m viterbo.experiments.example_pipeline.stage_plot
```

## Directory Layout

All paths relative to `packages/python_viterbo/`:

| Artifact | Path |
|----------|------|
| Experiment code | `src/viterbo/experiments/<label>/` |
| Stage entrypoints | `src/viterbo/experiments/<label>/stage_<name>.py` |
| Spec | `src/viterbo/experiments/<label>/SPEC.md` |
| Configs | `config/<label>/<variant>.json` |
| Data artifacts | `data/<label>/` |
| Tests | `tests/test_<label>.py` |
| Thesis assets | `../latex_viterbo/assets/<label>/` |

## Commands

```bash
cd packages/python_viterbo
uv sync --extra dev          # Install dependencies
uv run ruff format .         # Format
uv run ruff check --fix .    # Lint
uv run pyright               # Type check
uv run pytest tests/         # Test
```

## Code Style

- Docstrings: inputs, outputs, shapes/dtypes
- Pure functions preferred
- Comments explain WHY, not WHAT

---


# SKILL: develop-python-rust-interop

## FILE: develop-python-rust-interop/SKILL.md

---
name: develop-python-rust-interop
description: Build or modify the Rust-Python FFI using PyO3+maturin. Use for binding builds, smoke tests, and boundary validation workflow.
---

# PyO3 + maturin FFI Workflow

## Build

```bash
cd packages/python_viterbo && uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml
```

## Test

```bash
cd packages/python_viterbo && uv run pytest tests/test_ffi_capacity_hrep.py -v
```

## API Overview

The FFI exposes:

- `hk2017_capacity_hrep(normals, heights, use_graph_pruning=False) -> Hk2017Result`: Compute EHZ capacity using the HK2017 combinatorial formula
- `symplectic_form_4d(a, b) -> float`: Compute the standard symplectic form in R^4

## Design Principles

1. **Keep wrappers thin**: Convert types at the boundary, delegate to library crates
2. **Validate at boundary**: Check inputs in FFI code, return structured errors
3. **Expose only working code**: No stubs or archived placeholders - if it's not implemented, don't expose it
4. **Match stubs to implementation**: `rust_viterbo_ffi.pyi` must accurately reflect the actual API

## Files

- Rust FFI: `packages/rust_viterbo/ffi/src/lib.rs`
- Python stubs: `packages/python_viterbo/src/rust_viterbo_ffi.pyi`
- Tests: `packages/python_viterbo/tests/test_ffi_capacity_hrep.py`

---


# SKILL: develop-rust

## FILE: develop-rust/SKILL.md

---
name: develop-rust
description: Writing and testing Rust code in packages/rust_viterbo. Covers crate layout, testing conventions, property-based testing, and coding standards.
---

# Rust Development (rust_viterbo)

## Crates

- `geom` — shared geometry library (symplectic + euclidean, 2D + 4D)
- `hk2017` — HK2017 permutation enumeration algorithm
- `tube` — tube algorithm (branch-and-bound)
- `billiard` — billiard algorithm (Lagrangian products)
- `ffi` — PyO3/Maturin bindings for Python

## The geom Crate and Customization

`geom` provides **clean reference implementations** of fundamental geometry. Algorithm crates should:

- **Use geom** when the standard implementation fits
- **Copy and customize** when algorithm-specific needs diverge (e.g., different tolerances, extra fields)

Duplication is acceptable when purposeful. The value of `geom` is providing clean code to orient against — making deviations obvious and intentional. Don't force algorithms to use `geom` when a customized version serves them better.

## Commands

```bash
# Format
cargo fmt --all

# Lint
cargo clippy --workspace --all-targets

# Test (all modes)
scripts/test.sh

# Test (debug mode only - with debug_assert!)
scripts/test.sh --debug
cargo test --workspace

# Test (release mode only - expensive tests)
scripts/test.sh --release
cargo test --release --workspace

# Benchmark
cargo bench
```

## Conventions

- Favor pure functions with immutable types.
- Follow best practices for mathematically correct Rust code.
- Use `nalgebra` for linear algebra operations.
- Cover happy paths, edge cases, error paths.
- Document why changes are made (e.g., performance impact).

## Caching

**Local environment only:** Shared target dir at `/workspaces/worktrees/shared/target` (set via `CARGO_TARGET_DIR` in `.devcontainer/local/devcontainer.json`). Multiple worktrees share Rust build artifacts.

**Codespace environment:** Each worktree builds independently. See `develop-codespace` skill for details.

---

# Testing Conventions

Guidelines for testing Rust code in this project, with emphasis on property-based testing and mathematical correctness.

## Philosophy: Tests as Propositions

Tests should verify mathematical propositions, not just "does it run without crashing".

**Good**: `prop_scaling_law` - "∀K, ∀λ>0: c(λK) = λ²c(K)"
**Bad**: `test_random_stuff` - "call function, check no panic"

### Structure

```rust
/// Proposition: For all valid polytopes K, c(K) > 0.
///
/// Tested on: cross-polytope, 24-cell, asymmetric variants.
#[test]
fn prop_capacity_positive() {
    for (name, k) in test_polytopes() {
        let c = tube_capacity(&k).expect(&format!("{} should succeed", name));
        assert!(c.capacity > 0.0, "{}: c(K) = {} violates c(K) > 0", name, c.capacity);
    }
}
```

## Testing Levels

### 1. Debug Assertions (`debug_assert!`)

Use for internal invariants that are expensive to check in production:

```rust
fn reeb_vector(n: &Vector4<f64>, h: f64) -> Vector4<f64> {
    debug_assert!(h > 0.0, "Height must be positive");
    debug_assert!((n.norm() - 1.0).abs() < 1e-10, "Normal must be unit");
    apply_quat_i(n) * (2.0 / h)
}
```

### 2. Runtime Assertions (`assert!`)

Use for conditions that must always hold, even in release:

```rust
pub fn new(normals: Vec<Vector4<f64>>, heights: Vec<f64>) -> Self {
    assert_eq!(normals.len(), heights.len(), "Must have same number of normals and heights");
    // ...
}
```

### 3. Unit Tests (`#[test]`)

Test individual functions and invariants:

```rust
#[test]
fn test_quat_i_squared_is_minus_identity() {
    let i = quat_i();
    let i_squared = i * i;
    assert_relative_eq!(i_squared, -Matrix4::identity(), epsilon = EPS);
}
```

### 4. Property-Based Tests (proptest)

For properties that should hold across many random inputs:

```rust
use proptest::prelude::*;

proptest! {
    #[test]
    fn prop_symplectic_form_antisymmetric(
        x in uniform_vector4(),
        y in uniform_vector4()
    ) {
        let omega_xy = symplectic_form(&x, &y);
        let omega_yx = symplectic_form(&y, &x);
        prop_assert!((omega_xy + omega_yx).abs() < 1e-10);
    }
}
```

### 5. Integration Tests (`tests/`)

Test the full algorithm on realistic inputs:

```rust
#[test]
fn test_cross_polytope_capacity() {
    let hrep = fixtures::unit_cross_polytope();
    let result = tube_capacity(&hrep).expect("should compute");
    assert_relative_eq!(result.capacity, 1.0, epsilon = 0.01);
}
```

## Fixtures and Test Data

### Named Constants

For standard mathematical objects:

```rust
pub fn unit_cross_polytope() -> PolytopeHRep { ... }
pub fn unit_24_cell() -> PolytopeHRep { ... }
```

### Parameterized Families

```rust
pub fn scaled_cross_polytope(lambda: f64) -> PolytopeHRep { ... }
pub fn asymmetric_cross_polytope(seed: u64) -> PolytopeHRep { ... }
```

### Random Generators

Must be deterministic (seeded) and document:
- Distribution (NOT "uniform on S³" unless using Gaussian normalization)
- Rejection criteria and rates

```rust
/// Generate random H-rep. Returns None on rejection.
///
/// # Success rates (empirical, 10k seeds)
/// - n=6: ~31%
/// - n=8: ~32%
/// - n=10: ~12%
pub fn random_hrep(n_facets: usize, min_omega: f64, max_coord: f64, seed: u64) -> Option<PolytopeHRep>
```

### Diagnostics

When a generator has low success rate, add a diagnostic version:

```rust
pub enum RejectionReason {
    NearLagrangian,
    Unbounded,
    TooFewVertices,
    // ...
}

pub fn random_hrep_diagnostic(...) -> Result<PolytopeHRep, RejectionReason>
```

## proptest Setup

Add to `Cargo.toml`:

```toml
[dev-dependencies]
proptest = "1.4"
```

Define strategies for your domain types:

```rust
use proptest::prelude::*;

fn uniform_vector4() -> impl Strategy<Value = Vector4<f64>> {
    (any::<f64>(), any::<f64>(), any::<f64>(), any::<f64>())
        .prop_map(|(a, b, c, d)| Vector4::new(a, b, c, d))
}

fn valid_polytope() -> impl Strategy<Value = PolytopeHRep> {
    // Use fixtures or filtered generation
    prop_oneof![
        Just(fixtures::unit_cross_polytope()),
        Just(fixtures::unit_24_cell()),
        (0u64..1000).prop_filter_map("asymmetric", |seed| {
            fixtures::random_hrep(8, 0.01, 100.0, seed)
        }),
    ]
}
```

## Numerical Tolerances

Use `approx` crate for floating-point comparisons:

```rust
use approx::assert_relative_eq;

assert_relative_eq!(actual, expected, epsilon = 1e-10);
assert_relative_eq!(actual, expected, max_relative = 0.01); // 1% relative error
```

Define project-wide constants:

```rust
// constants.rs
pub const EPS: f64 = 1e-10;           // General tolerance
pub const EPS_LAGRANGIAN: f64 = 1e-8; // For detecting Lagrangian 2-faces
pub const EPS_CLOSURE: f64 = 1e-6;    // For orbit closure (accumulated error)
```

## Test Organization

```
tube/
├── src/
│   ├── lib.rs           # Doctests for public API
│   ├── algorithm.rs     # Unit tests in `mod tests { ... }`
│   └── fixtures.rs      # Fixture tests
└── tests/
    ├── integration.rs   # Full algorithm tests
    ├── orbit_invariants.rs  # Mathematical invariant tests
    └── flow_map_tests.rs    # Robustness tests
```

## Debug vs Release Mode Tests

Tests can self-document their mode requirements using `cfg_attr`:

```rust
// Runs ONLY in release mode (skipped in debug)
// Use for expensive tests that only verify output correctness
#[cfg_attr(debug_assertions, ignore)]
#[test]
fn expensive_output_verification_test() { ... }

// Runs ONLY in debug mode (skipped in release)
// Use for tests that specifically need debug_assert! checks
#[cfg_attr(not(debug_assertions), ignore)]
#[test]
fn test_needs_debug_assertions() { ... }
```

### When to use each mode

**Debug mode** (default `cargo test`):
- Tests that exercise code paths with `debug_assert!()` checks
- Tests that verify internal invariants
- Most unit tests

**Release mode** (`cargo test --release`):
- Expensive tests that only verify output correctness
- Property tests running many iterations
- Tests where computation speed matters (e.g., tube integration tests: 92s debug → 1.3s release)

### Current test organization

| Package | File | Mode | Rationale |
|---------|------|------|-----------|
| tube | tests/integration.rs | release | 11 capacity tests, ~50 computations |
| hk2017 | integration_tests module | release | 4 expensive pipeline tests |
| hk2017 | algorithm.rs expensive tests | release | 5 tesseract capacity tests |
| all | unit tests, flow_map, orbit_invariants | debug | Exercise internal invariants |

## Per-Test Timing

```bash
# Using nightly (lightweight)
cargo +nightly test -p tube -- -Z unstable-options --report-time

# Using cargo-nextest (better output, shows SLOW tests)
cargo nextest run -p tube

# Sequential execution for clean timing
RUST_TEST_THREADS=1 cargo nextest run -p tube
```

---

# Code Quality Notes

TODO: Document quality improvement principles specific to Rust development.

Key topics to cover:
- When to refactor vs leave code as-is
- Mathematical correctness despite type system limitations (no dependent types)
- Documentation standards for geometric algorithms
- When to consolidate vs duplicate code across algorithm crates

See the former `quality-improvement` skill for potential content to integrate.

---


# SKILL: download-arxiv-papers

## FILE: download-arxiv-papers/SKILL.md

---
name: download-arxiv-papers
description: Add arXiv papers to the repo for agent access. Use when you need to read a paper's formulas/proofs, or when web search gives you an arXiv ID you want to examine closely.
---

# Paper Reading (arXiv sources)

## When to use this skill

- You found an arXiv paper via web search and need to read its actual content
- You need to verify formulas, definitions, or proofs from a paper
- A paper is repeatedly needed across sessions and should be cached locally

**Do NOT use** for papers you only need to cite without reading deeply. In that case, just add a BibTeX entry to `packages/latex_viterbo/references.bib` and cite it normally in your LaTeX source.

**Delegation tip**: If you're doing implementation work and need to understand a paper, consider spawning a subagent to read and summarize the relevant sections. This keeps your main context clean for code.

## Location

Papers live in `docs/papers/`. Check existing folders first:
```bash
ls -la docs/papers/
```

## Download workflow

**Use the download script:**
```bash
.claude/skills/download-arxiv-papers/download-arxiv.sh <arxiv-id> <folder-name>
# Example:
.claude/skills/download-arxiv-papers/download-arxiv.sh 2203.02043 Rudolf2022-worm-problem
```

**Folder naming convention:**
- Single author: `Surname + Year + description` (e.g., `Rudolf2022-worm-problem`, `Irie2019-loop-spaces`)
- Multiple authors: `Initials + Year + description` (e.g., `HK2024-counterexample`, `AK2019-SH-clarke`)

The script handles format detection (tar.gz vs gzip'd single file) automatically.

### After downloading checklist

1. **Update `docs/papers/README.md`** - add row to the table
2. **Add BibTeX to `packages/latex_viterbo/references.bib`** - websearch `arXiv <id>` for title/authors:
   ```bibtex
   @article{Rudolf2022,
     title        = {Viterbo's conjecture as a worm problem},
     author       = {Rudolf, Daniel},
     year         = {2022},
     journal      = {arXiv preprint},
     eprint       = {2203.02043},
     archivePrefix= {arXiv},
     primaryClass = {math.SG},
     note         = {Brief description of key results.}
   }
   ```
3. **Verify extraction** - `ls -la docs/papers/<folder>/` to see files

## Reading papers

**Read the .tex files directly.** They are plain text and more reliable than PDF parsing.

**Watch for custom macros:** Some papers define shortcuts like `\bthm` instead of `\begin{theorem}`. If standard searches return nothing, check the preamble for `\def\bthm` or similar. Search for both patterns:

```bash
# Standard LaTeX theorem environments
grep -n "begin{theorem}\|begin{definition}\|begin{lemma}" docs/papers/FOLDER/*.tex

# Custom macros (common in some papers)
grep -n "\\\\bthm\|\\\\blem\|\\\\bprop\|\\\\bdefi" docs/papers/FOLDER/*.tex

# Find all labels
grep -n "\\\\label{" docs/papers/FOLDER/*.tex
```

## Labels vs Numbers (TeX vs PDF)

TeX files use **labels** (e.g., `\label{thm:main}`), while PDFs show **numbers** (e.g., "Theorem 3.2"). This matters when:
- A human asks about "Theorem 3.2" but you're reading TeX
- You find `\ref{thm:capacity}` and need to locate its definition

**How to navigate**:

1. **Find where a label is defined** - the theorem text is right there:
   ```bash
   grep -B2 -A10 "\\\\label{thm:main}" docs/papers/FOLDER/*.tex
   ```

2. **Find all label definitions** to build a mental map:
   ```bash
   grep -n "\\\\label{" docs/papers/FOLDER/*.tex | head -30
   ```

3. **Labels often hint at content**: `thm:capacity`, `lem:rotation-bound`, `def:ehz` are more descriptive than numbers.

4. **When humans reference by number**: Ask them for the label or section name, or look for context clues ("the main theorem in section 3" → grep for `\section{` to find section 3, then look for theorems there).

**Do not rely on PDF for math content** - PDF parsing mangles formulas (missing signs, broken fractions, extra symbols). Use PDF only to verify theorem numbering if absolutely necessary.

## Folder naming rationale

The scheme `CITATIONKEY-description/` with original filenames inside enables:
- **Discoverability**: Find papers by author, year, or topic via folder names
- **Citation linking**: Folder prefix matches `references.bib` entries
- **Intact references**: Internal `\input{section1}` still works
- **Easy browsing**: `ls -la` shows all paper files

## Why TeX over PDF

- TeX files are plain text, easy to grep and read
- PDF parsing in agents is unreliable for math notation
- Formulas appear exactly as the author wrote them
- Labels are searchable; following `\ref{}` is straightforward
- Smaller file size, faster to process

## Downloading PDFs from non-arXiv sources

### Direct PDF URLs

If you have a direct URL to a PDF file (e.g., `https://example.com/thesis.pdf` or a Google Drive link), download with curl:

```bash
mkdir -p docs/references
curl -L "<url>" -o docs/references/<descriptive-name>.pdf
```

For Google Drive links like `https://drive.google.com/file/d/<FILE_ID>/view?usp=sharing`:
```bash
curl -L "https://drive.google.com/uc?export=download&id=<FILE_ID>" -o docs/references/<name>.pdf
```

### JavaScript-rendered pages (institutional repositories)

Some library systems (TAU Primo, ExLibris Alma, etc.) require JavaScript to render the page and reveal PDF links. **WebFetch cannot execute JavaScript** - it only retrieves raw HTML.

**Current limitation:** Playwright/headless browsers require downloading Chromium binaries, which may be blocked by network restrictions in sandboxed environments. As of 2026-01, this does not work reliably in Claude Code.

**Workaround:** Ask the user to:
1. Open the library URL in their browser
2. Find the PDF download link
3. Provide the direct PDF URL to you

If the user provides a direct PDF URL, download with curl as shown above.

### Common institutional repositories

| Source | URL Pattern | Notes |
|--------|-------------|-------|
| TAU Library | `tau.primo.exlibrisgroup.com` | Requires JS; ask user for direct link |
| Google Drive | `drive.google.com/file/d/ID/view` | Use curl with export URL |
| arXiv | `arxiv.org/pdf/ID.pdf` | Direct download works |
| Semantic Scholar | Links to publisher PDFs | Follow redirect chain |

### When all else fails

1. Document the URL and why programmatic access failed
2. Ask the user to download manually and provide the file
3. Note any authentication requirements (university login, etc.)

---

## FILE: download-arxiv-papers/download-arxiv.sh

#!/usr/bin/env bash
# Download arXiv paper TeX sources for agent reading
#
# Usage: .claude/skills/download-arxiv-papers/download-arxiv.sh <arxiv-id> <folder-name>
# Example: .claude/skills/download-arxiv-papers/download-arxiv.sh 2203.02043 Rudolf2022-worm-problem
#
# Folder naming convention:
#   Single author:  Surname + Year + description  (e.g., Rudolf2022-worm-problem)
#   Multi author:   Initials + Year + description (e.g., HK2024-counterexample)
#
# After running, remember to:
#   1. Update docs/papers/README.md with the new entry
#   2. Add BibTeX entry to packages/latex_viterbo/references.bib

set -euo pipefail

if [[ $# -lt 2 ]]; then
    echo "Usage: $0 <arxiv-id> <folder-name>"
    echo "Example: $0 2203.02043 Rudolf2022-worm-problem"
    exit 1
fi

ARXIV_ID="$1"
FOLDER_NAME="$2"
PAPERS_DIR="docs/papers"
TARGET_DIR="${PAPERS_DIR}/${FOLDER_NAME}"

# Check if folder already exists
if [[ -d "$TARGET_DIR" ]]; then
    echo "Error: $TARGET_DIR already exists"
    exit 1
fi

# Create folder and download
mkdir -p "$TARGET_DIR"
cd "$TARGET_DIR"

echo "Downloading arXiv:${ARXIV_ID}..."
wget -q "https://arxiv.org/e-print/${ARXIV_ID}" -O source

# Detect format and extract
if tar -tzf source >/dev/null 2>&1; then
    echo "Extracting tar.gz archive..."
    tar -xzf source
    rm source
else
    # Single gzip'd .tex file
    echo "Extracting gzip'd .tex file..."
    gunzip -c source > paper.tex
    rm source
fi

echo ""
echo "Downloaded to: $TARGET_DIR"
ls -la
echo ""
echo "Next steps:"
echo "  1. Update docs/papers/README.md"
echo "  2. Add BibTeX to packages/latex_viterbo/references.bib"
echo "  3. Websearch 'arXiv ${ARXIV_ID}' for title/authors if needed"

---


# SKILL: official-claude-code-guides

## FILE: official-claude-code-guides/SKILL.md

---
name: official-claude-code-guides
description: Use this agent when the user asks questions ("Can Claude...", "Does Claude...", "How do I...") about Claude Code (the CLI tool) - features, hooks, slash commands, MCP servers, settings, IDE integrations, keyboard shortcuts, or the Claude API (formerly Anthropic API) - API usage, tool use, Anthropic SDK usage.
---

# Claude Code Guide

This skill provides quick reference to authoritative Claude Code resources. When questions arise about Claude Code capabilities, workflows, or best practices, consult these resources rather than guessing.

## Important Note on Currency

Claude Code and its models evolve rapidly. Advice predating Claude 4.5 Opus/Sonnet (late 2024/early 2025) is likely outdated. Always prefer official Anthropic documentation and recent 2026 resources.

## Local References (Downloaded for Offline Access)

These key documents have been downloaded and converted to markdown for faster access:

1. **[best-practices.md](references/best-practices.md)** - Comprehensive best practices guide from Anthropic
   - When to read: For optimizing workflows, learning about CLAUDE.md files, MCP integration, custom commands, multi-agent patterns
   - Key topics: CLAUDE.md files, tool allowlists, test-driven development, headless mode, git worktrees

2. **[common-workflows.md](references/common-workflows.md)** - Official workflow documentation
   - When to read: For specific how-to guides on common tasks
   - Key topics: Codebase exploration, bug fixing, refactoring, plan mode, subagents, testing, PR creation, image handling, custom slash commands

3. **[overview.md](references/overview.md)** - What Claude Code is and basic capabilities
   - When to read: For onboarding or explaining Claude Code to others
   - Key topics: Installation, core capabilities, philosophy, quick start

## Official Online Documentation

4. **[Claude Code Docs](https://code.claude.com/docs/en/overview)** - Main documentation portal
   - When to read: For comprehensive, up-to-date official documentation
   - Covers: Setup, configuration, all features, troubleshooting

5. **[VS Code Integration](https://code.claude.com/docs/en/vs-code)** - VS Code extension guide
   - When to read: For IDE-specific features and keyboard shortcuts
   - Covers: Native graphical interface, IDE integration, extension features

6. **[Claude API/Platform Docs](https://docs.anthropic.com/en/release-notes/overview)** - Developer platform documentation
   - When to read: For API usage, model details, SDK information
   - Covers: API endpoints, authentication, rate limits, model capabilities

## Community Resources (2026)

7. **[Anthropic Engineering: Best Practices](https://www.anthropic.com/engineering/claude-code-best-practices)** - Official engineering blog post
   - When to read: Same as local best-practices.md (this is the source)
   - Why listed: Direct link to check for updates

8. **[How Anthropic Teams Use Claude Code (PDF)](https://www-cdn.anthropic.com/58284b19e702b49db9302d5b6f135ad8871e7658.pdf)** - Internal workflows from Anthropic
   - When to read: For real-world examples from the creators
   - Covers: Production usage patterns, team workflows

9. **[GitHub: anthropics/claude-code](https://github.com/anthropics/claude-code)** - Official GitHub repository
   - When to read: For issue tracking, changelog, source code
   - Covers: Latest releases, known issues, feature requests

10. **[GitHub: awesome-claude-code](https://github.com/hesreallyhim/awesome-claude-code)** - Community curated resources
    - When to read: For plugins, skills, hooks, and community tools
    - Covers: Extensions, integrations, third-party tools

11. **[Claude Code Creator's Workflow (VentureBeat)](https://venturebeat.com/technology/the-creator-of-claude-code-just-revealed-his-workflow-and-developers-are)** - Boris Cherny's workflow
    - When to read: For insights from the creator's actual usage patterns
    - Covers: Real-world workflows, 259 PRs in 30 days example

12. **[Shipyard Claude Code Cheatsheet](https://shipyard.build/blog/claude-code-cheat-sheet/)** - Quick reference guide
    - When to read: For quick command lookups and configuration reference
    - Covers: Commands, config files, prompts, best practices

## Practical Guide Articles (2026)

13. **[Builder.io: How I Use Claude Code](https://www.builder.io/blog/claude-code)** - Personal tips and workflow
    - When to read: For practical tips from experienced users
    - Key tip: Use /clear often, dedicate time to CLAUDE.md documentation

14. **[Blog: How I Use Every Claude Code Feature](https://blog.sshh.io/p/how-i-use-every-claude-code-feature)** - Feature-by-feature guide
    - When to read: For comprehensive feature coverage with examples
    - Covers: Deep dive into each feature with use cases

15. **[Professional Guide for Senior Devs (2026)](https://wmedia.es/en/writing/claude-code-professional-guide-frontend-ai)** - Advanced usage
    - When to read: For advanced patterns and professional workflows
    - Covers: Frontend, AI integration, senior developer practices

16. **[20+ Most Important CLI Tricks (2026)](https://mlearning.substack.com/p/20-most-important-claude-code-tricks-2025-2026-cli-january-update)** - Tips and tricks compilation
    - When to read: For quick wins and productivity hacks
    - Covers: CLI shortcuts, hidden features, efficiency tips

17. **[F22 Labs: 10 Productivity Tips](https://www.f22labs.com/blogs/10-claude-code-productivity-tips-for-every-developer/)** - Productivity focused
    - When to read: For developer productivity optimization
    - Covers: Workflow optimization, time-saving techniques

18. **[GitHub: claude-code-tips](https://github.com/ykdojo/claude-code-tips)** - 40+ tips collection
    - When to read: For comprehensive tips including advanced topics
    - Covers: Basics to advanced, custom status line, Gemini CLI integration, container usage

## Creator Insights (Boris Cherny)

19. **[InfoQ: Inside the Development Workflow](https://www.infoq.com/news/2026/01/claude-code-creator-workflow/)** - Creator workflow analysis
    - When to read: For understanding the creator's development process
    - Covers: Plan mode emphasis, verification loops, CLAUDE.md evolution

20. **[Medium: 22 Tips from Boris Cherny](https://medium.com/@joe.njenga/boris-cherny-claude-code-creator-shares-these-22-tips-youre-probably-using-it-wrong-1b570aedefbe)** - Direct tips from creator
    - When to read: For avoiding common mistakes
    - Covers: What not to do, optimization tips

21. **[Dev Genius: 13 Practical Moves](https://blog.devgenius.io/how-the-creator-of-claude-code-actually-uses-it-13-practical-moves-2bf02eec032a)** - Creator's practical techniques
    - When to read: For actionable techniques from Boris Cherny
    - Covers: Real usage patterns, practical moves

## Advanced Workflows

22. **[Medium: 17 Best Workflows](https://medium.com/@joe.njenga/17-best-claude-code-workflows-that-separate-amateurs-from-pros-instantly-level-up-5075680d4c49)** - Amateur vs Pro patterns
    - When to read: For leveling up your workflow game
    - Covers: Professional workflow patterns, advanced techniques

23. **[Medium: Two Simple Tricks (Julien Simon)](https://julsimon.medium.com/two-simple-tricks-that-will-dramatically-improve-your-productivity-with-claude-db90ce784931)** - High-impact productivity tips
    - When to read: For maximum ROI productivity improvements
    - Covers: Simple but powerful techniques

## Release Notes and Updates

24. **[Claude Code Changelog](https://docs.anthropic.com/en/release-notes/claude-code)** - Official release notes
    - When to read: For latest features, bug fixes, breaking changes
    - Covers: Version history, new features, deprecations

25. **[VentureBeat: Claude Code 2.1.0](https://venturebeat.com/orchestration/claude-code-2-1-0-arrives-with-smoother-workflows-and-smarter-agents)** - Major release coverage
    - When to read: For understanding major version updates
    - Covers: v2.1.0 features, agent lifecycle control, session portability

## Quick Reference Key Insights

### Essential Commands
- `/clear` - Reset context (use often!)
- `/permissions` - Manage tool allowlists
- `/agents` - Access specialized subagents
- `Escape` - Stop Claude (not Ctrl+C)
- `Shift+Tab` - Cycle permission modes (Normal → Auto-Accept → Plan)
- `Option/Alt+T` - Toggle thinking mode
- `Ctrl+O` - Toggle verbose mode

### Core Patterns
1. **CLAUDE.md files** - Document project conventions, checked into git
2. **Plan before code** - Use plan mode for complex features
3. **Verification loops** - Give Claude ways to verify work (tests, builds, visual checks)
4. **Custom slash commands** - Store in `.claude/commands/` or `~/.claude/commands/`
5. **MCP servers** - Extend Claude with custom tools
6. **Git worktrees** - Run parallel Claude sessions on different branches

### Performance Tips
- Keep CLAUDE.md concise and structured
- Use /clear between unrelated tasks
- Provide specific, actionable instructions
- Include visual references (screenshots, mockups)
- Set up feedback loops (tests, linters, builds)
- Use headless mode (`-p`) for automation

## When to Consult This Skill

Use this skill when questions arise about:
- "Can Claude Code do X?"
- "How do I configure Y?"
- "What's the best way to Z?"
- Keyboard shortcuts or CLI flags
- MCP servers, hooks, or settings
- IDE integration features
- API usage or SDK questions
- Troubleshooting Claude Code issues

Rather than guessing or providing outdated information, direct users to the appropriate resource above based on their specific question.

---

## FILE: official-claude-code-guides/references/best-practices.md

# Claude Code: Best Practices Guide

Source: https://www.anthropic.com/engineering/claude-code-best-practices

## Overview
This comprehensive guide outlines effective patterns for using Claude Code, an agentic coding tool developed by Anthropic. As noted in the article, "Claude Code is intentionally low-level and unopinionated, providing close to raw model access without forcing specific workflows."

## 1. Customize Your Setup

### Create CLAUDE.md Files
Special files that Claude automatically integrates into context when starting conversations. Ideal content includes:
- Common bash commands with descriptions
- Core files and utility functions
- Code style guidelines
- Testing instructions
- Repository conventions (branching, merge strategies)
- Developer environment setup requirements
- Project-specific warnings or unexpected behaviors

The guide recommends keeping these files "concise and human-readable" and suggests checking them into version control to share across teams.

### Placement Options
- Root directory (checked in for team sharing, or `.local.md` for personal use)
- Parent directories (useful for monorepos)
- Child directories (Claude pulls in on demand)
- Home folder (`~/.claude/CLAUDE.md`) for all sessions

### Tuning CLAUDE.md Files
Files should be refined iteratively like production prompts. The document notes that teams at Anthropic sometimes "run CLAUDE.md files through the prompt improver" and use emphasis techniques like "IMPORTANT" or "YOU MUST" to improve model adherence.

### Tool Allowlists
Manage which actions Claude can perform by:
- Selecting "Always allow" during sessions
- Using the `/permissions` command
- Manually editing `.claude/settings.json` or `~/.claude.json`
- Adding CLI flags like `--allowedTools` for session-specific permissions

### GitHub Integration
Installing the `gh` CLI enables Claude to manage issues, pull requests, and comments more effectively than API-only approaches.

## 2. Give Claude More Tools

### Bash Tools
Claude inherits your shell environment, accessing custom scripts and utilities. Recommend documenting tool usage with examples and directing Claude to use `--help` flags for documentation.

### MCP (Model Context Protocol)
Claude Code functions as both MCP client and server, supporting:
- Project-specific configurations
- Global configurations
- Checked-in `.mcp.json` files for team-wide availability

Use the `--mcp-debug` flag when troubleshooting configuration issues.

### Custom Slash Commands
Store prompt templates in `.claude/commands` folder as Markdown files. These become available through the slash menu and support the `$ARGUMENTS` keyword for parameterized workflows.

Example use case: Creating `/project:fix-github-issue 1234` commands for automated issue resolution.

## 3. Common Workflows

### Explore, Plan, Code, Commit
1. Request Claude read relevant files without coding initially
2. Ask for a plan using thinking mode ("think" through "ultrathink" for progressively more computation)
3. Implement the solution with verification steps
4. Commit changes and update documentation

The guide emphasizes that "steps #1-#2 are crucial" for problems requiring deeper analysis.

### Test-Driven Development Workflow
1. Write tests based on expected input/output pairs
2. Verify tests fail (without implementation)
3. Commit tests
4. Implement code iteratively until all tests pass
5. Verify implementation doesn't overfit using subagents

### Visual Iteration Workflow
1. Provide screenshot capabilities (Puppeteer MCP, iOS simulator, or manual screenshots)
2. Share design mocks via paste or file paths
3. Iterate until Claude's output matches the reference

### Safe YOLO Mode
Use `--dangerously-skip-permissions` to bypass permission checks. Recommended practice: run in containers without internet access to minimize security risks from prompt injection or data exfiltration.

### Codebase Q&A
Use Claude for onboarding questions like:
- "How does logging work?"
- "What edge cases does this component handle?"
- "Why was this API designed this way?"

### Git Interactions
Claude effectively handles:
- Searching history to answer context questions
- Writing context-aware commit messages
- Complex operations (rebasing, conflict resolution, patch comparisons)

### GitHub Interactions
Claude can manage:
- Pull request creation with appropriate messages
- Code review comment implementation
- Build failure fixes
- Issue categorization and triage

### Jupyter Notebooks
Researchers can use Claude to read, write, and improve notebooks, with results including image interpretation for data exploration.

## 4. Optimize Your Workflow

### Specific Instructions
The guide contrasts poor instructions ("add tests for foo.py") with better ones ("write a new test case covering the edge case where the user is logged out, avoiding mocks").

### Visual References
Claude excels with:
- Screenshots (macOS: `cmd+ctrl+shift+4` to clipboard, then `ctrl+v` to paste)
- Drag-and-drop image uploads
- File path references
- Design mocks for UI development

### File References
Use tab-completion to quickly mention files or folders anywhere in your repository, helping Claude identify correct resources.

### URL Integration
Paste URLs alongside prompts for Claude to fetch and read. Use `/permissions` to allowlist domains and avoid repeated permission prompts.

### Course Correction Techniques
- Ask Claude to make plans before coding
- Press Escape to interrupt without losing context
- Double-tap Escape to edit previous prompts and explore alternatives
- Request Claude to undo changes

### Context Management
Use `/clear` between tasks to reset the context window and maintain focus on current objectives.

### Checklists for Complex Tasks
For migrations or bulk fixes, have Claude:
- Create a Markdown checklist of all tasks
- Work through items systematically
- Check off completed items

### Data Input Methods
- Copy and paste directly
- Pipe into Claude Code (e.g., `cat log.txt | claude`)
- Request Claude pull data via bash or tools
- Ask Claude to read files or fetch URLs

## 5. Headless Mode for Infrastructure

Use the `-p` flag with `--output-format stream-json` for non-interactive contexts like CI, pre-commit hooks, and build scripts.

### Use Cases
- **Issue triage**: Automatically label new GitHub issues
- **Linting**: Provide subjective code reviews beyond traditional linters, identifying typos, stale comments, and misleading names

## 6. Multi-Claude Workflows

### Parallel Verification
Have one Claude write code while another reviews or tests it, leveraging separate contexts for better results than single-instance approaches.

### Multiple Repository Checkouts
Create 3-4 separate git checkouts in different folders, opening each in separate terminal tabs for simultaneous parallel work.

### Git Worktrees
Lighter alternative to multiple checkouts: Use `git worktree add ../project-feature-a feature-a` to isolate multiple tasks without merge conflicts.

### Custom Harness with Headless Mode
Two patterns emerge:

**Fanning out**: Generate task lists, then loop through items calling Claude programmatically for each task (useful for large migrations or analyses).

**Pipelining**: Integrate Claude into data processing pipelines using `claude -p "<prompt>" --json | your_command`.

---

## Key Takeaways

The guide emphasizes that Claude Code's flexibility requires experimentation to develop effective personal workflows. Core principles include thorough planning before coding, providing clear iteration targets (tests, visuals, or specifications), and leveraging Claude's ability to integrate with existing development ecosystems through bash, MCP tools, and git workflows.

---

## FILE: official-claude-code-guides/references/common-workflows.md

# Common Workflows - Claude Code Documentation

Source: https://code.claude.com/docs/en/common-workflows

This page provides comprehensive guidance on common workflows with Claude Code. Here are the main sections:

## Understand New Codebases

### Get a Quick Codebase Overview
```bash
cd /path/to/project
claude
> give me an overview of this codebase
> explain the main architecture patterns used here
> what are the key data models?
> how is authentication handled?
```

**Tips:**
- Start with broad questions, then narrow down to specific areas
- Ask about coding conventions and patterns used in the project
- Request a glossary of project-specific terms

### Find Relevant Code
```bash
> find the files that handle user authentication
> how do these authentication files work together?
> trace the login process from front-end to database
```

## Fix Bugs Efficiently

```bash
> I'm seeing an error when I run npm test
> suggest a few ways to fix the @ts-ignore in user.ts
> update user.ts to add the null check you suggested
```

**Tips:**
- Tell Claude the command to reproduce the issue and get a stack trace
- Mention any steps to reproduce the error
- Let Claude know if the error is intermittent or consistent

## Refactor Code

```bash
> find deprecated API usage in our codebase
> suggest how to refactor utils.js to use modern JavaScript features
> refactor utils.js to use ES2024 features while maintaining the same behavior
> run tests for the refactored code
```

## Use Specialized Subagents

```bash
> /agents  # View available subagents
> review my recent code changes for security issues
> use the code-reviewer subagent to check the auth module
> have the debugger subagent investigate why users can't log in
```

**Creating custom subagents:**
```bash
> /agents
```
Then select "Create New subagent" and define:
- A unique identifier (e.g., `code-reviewer`, `api-designer`)
- When Claude should use this agent
- Which tools it can access
- A system prompt describing the agent's role

## Use Plan Mode for Safe Code Analysis

Plan Mode instructs Claude to create a plan by analyzing the codebase with read-only operations before making changes.

### When to use Plan Mode
- **Multi-step implementation**: When your feature requires edits to many files
- **Code exploration**: When you want to research the codebase thoroughly before changing anything
- **Interactive development**: When you want to iterate on the direction with Claude

### How to use Plan Mode

**Turn on Plan Mode during a session:**
- Press **Shift+Tab** to cycle through permission modes
- **Shift+Tab** twice: Normal Mode → Auto-Accept Mode → Plan Mode (`⏸ plan mode on`)

**Start a new session in Plan Mode:**
```bash
claude --permission-mode plan
```

**Run headless queries in Plan Mode:**
```bash
claude --permission-mode plan -p "Analyze the authentication system and suggest improvements"
```

### Example: Planning a Complex Refactor

```bash
claude --permission-mode plan
> I need to refactor our authentication system to use OAuth2. Create a detailed migration plan.

> What about backward compatibility?
> How should we handle database migration?
```

### Configure Plan Mode as Default

```json
// .claude/settings.json
{
  "permissions": {
    "defaultMode": "plan"
  }
}
```

## Let Claude Interview You

For large features, let Claude gather requirements through questions:

```bash
> Interview me about this feature before you start: user notification system
> Help me think through the requirements for authentication by asking questions
> Ask me clarifying questions to build out this spec: payment processing
```

Claude uses the `AskUserQuestion` tool to ask multiple-choice questions for gathering requirements and clarifying ambiguity before writing any code.

## Work with Tests

```bash
> find functions in NotificationsService.swift that are not covered by tests
> add tests for the notification service
> add test cases for edge conditions in the notification service
> run the new tests and fix any failures
```

Claude generates tests matching your project's existing patterns and conventions.

## Create Pull Requests

```bash
> summarize the changes I've made to the authentication module
> create a pr
> enhance the PR description with more context about the security improvements
> add information about how these changes were tested
```

## Handle Documentation

```bash
> find functions without proper JSDoc comments in the auth module
> add JSDoc comments to the undocumented functions in auth.js
> improve the generated documentation with more context and examples
> check if the documentation follows our project standards
```

## Work with Images

You can include images in conversations by:
1. Dragging and dropping into the Claude Code window
2. Copying and pasting with **Ctrl+V** (not Cmd+V)
3. Providing an image path

```bash
> What does this image show?
> Describe the UI elements in this screenshot
> Are there any problematic elements in this diagram?
> Here's a screenshot of the error. What's causing it?
> Generate CSS to match this design mockup
```

## Reference Files and Directories

Use `@` to quickly include files or directories:

```bash
> Explain the logic in @src/utils/auth.js
> What's the structure of @src/components?
> Show me the data from @github:repos/owner/repo/issues
```

## Use Extended Thinking (Thinking Mode)

Extended thinking is enabled by default, reserving up to 31,999 tokens for Claude to reason through complex problems step-by-step.

### Configure Thinking Mode

| Scope | How to Configure | Details |
|-------|-----------------|---------|
| **Toggle shortcut** | Press `Option+T` (macOS) or `Alt+T` (Windows/Linux) | Toggle for current session |
| **Global default** | Use `/config` | Sets default across all projects |
| **Limit token budget** | Set `MAX_THINKING_TOKENS` environment variable | Example: `export MAX_THINKING_TOKENS=10000` |

**View thinking process:**
Press `Ctrl+O` to toggle verbose mode and see internal reasoning as gray italic text.

### How Extended Thinking Token Budgets Work

- When **enabled**: Claude can use up to **31,999 tokens** from your output budget for thinking
- When **disabled**: Claude uses **0 tokens** for thinking
- You're charged for all thinking tokens used

## Resume Previous Conversations

```bash
claude --continue                    # Continue most recent conversation
claude --resume                      # Open conversation picker
claude --resume auth-refactor        # Resume by name
```

### Name Your Sessions

```bash
> /rename auth-refactor              # During a session
> /resume auth-refactor              # Resume by name later
```

### Use the Session Picker

```bash
/resume
```

**Keyboard shortcuts in picker:**

| Shortcut | Action |
|----------|--------|
| `↑` / `↓` | Navigate between sessions |
| `→` / `←` | Expand or collapse grouped sessions |
| `Enter` | Select and resume session |
| `P` | Preview session content |
| `R` | Rename session |
| `/` | Search to filter sessions |
| `A` | Toggle all projects view |
| `B` | Filter to current git branch |
| `Esc` | Exit picker |

## Run Parallel Claude Code Sessions with Git Worktrees

```bash
# Create a new worktree with a new branch
git worktree add ../project-feature-a -b feature-a

# Or create a worktree with an existing branch
git worktree add ../project-bugfix bugfix-123

# Navigate to your worktree
cd ../project-feature-a
claude

# List all worktrees
git worktree list

# Remove a worktree when done
git worktree remove ../project-feature-a
```

## Use Claude as a Unix-style Utility

### Add Claude to Your Verification Process

```json
// package.json
{
  "scripts": {
    "lint:claude": "claude -p 'you are a linter. please look at the changes vs. main and report any issues related to typos. report the filename and line number on one line, and a description of the issue on the second line. do not return any other text.'"
  }
}
```

### Pipe In, Pipe Out

```bash
cat build-error.txt | claude -p 'concisely explain the root cause of this build error' > output.txt
```

### Control Output Format

```bash
# Text format (default)
cat data.txt | claude -p 'summarize this data' --output-format text > summary.txt

# JSON format
cat code.py | claude -p 'analyze this code for bugs' --output-format json > analysis.json

# Streaming JSON format
cat log.txt | claude -p 'parse this log file for errors' --output-format stream-json
```

## Create Custom Slash Commands

### Create Project-Specific Commands

```bash
mkdir -p .claude/commands
echo "Analyze the performance of this code and suggest three specific optimizations:" > .claude/commands/optimize.md
```

Then in Claude Code:
```bash
> /optimize
```

### Add Command Arguments with $ARGUMENTS

```bash
echo 'Find and fix issue #$ARGUMENTS. Follow these steps: 1. Understand the issue described in the ticket 2. Locate the relevant code in our codebase 3. Implement a solution that addresses the root cause 4. Add appropriate tests 5. Prepare a concise PR description' > .claude/commands/fix-issue.md
```

Usage:
```bash
> /fix-issue 123
```

### Create Personal Slash Commands

```bash
mkdir -p ~/.claude/commands
echo "Review this code for security vulnerabilities, focusing on:" > ~/.claude/commands/security-review.md
```

Then use across all projects:
```bash
> /security-review
```

## Ask Claude About Its Capabilities

Claude has built-in access to its documentation:

```bash
> can Claude Code create pull requests?
> how does Claude Code handle permissions?
> what slash commands are available?
> how do I use MCP with Claude Code?
> how do I configure Claude Code for Amazon Bedrock?
> what are the limitations of Claude Code?
```

---

## FILE: official-claude-code-guides/references/overview.md

# Claude Code Overview

Source: https://code.claude.com/docs/en/overview

## What is Claude Code?

Claude Code is **Anthropic's agentic coding tool that lives in your terminal** and helps developers turn ideas into code faster than ever before. It's designed to meet developers where they already work—in their existing tools and workflows.

## Key Capabilities

Claude Code enables you to:

1. **Build features from descriptions** - Tell Claude what you want to build in plain English. It makes a plan, writes the code, and ensures it works.

2. **Debug and fix issues** - Describe a bug or paste an error message. Claude Code analyzes your codebase, identifies the problem, and implements fixes.

3. **Navigate any codebase** - Ask anything about your team's codebase and get thoughtful answers. It maintains awareness of your entire project structure and can find up-to-date information from the web.

4. **Automate tedious tasks** - Fix lint issues, resolve merge conflicts, write release notes—all from a single command.

## Why Developers Love It

- **Works in your terminal** - Not another chat window or IDE, but integrated into your existing workflow
- **Takes action** - Can directly edit files, run commands, and create commits
- **Unix philosophy** - Composable and scriptable (e.g., `tail -f app.log | claude -p "Slack me if you see any anomalies"`)
- **Enterprise-ready** - Use the Claude API or host on AWS/GCP with built-in security, privacy, and compliance

## Quick Start

**Installation** (macOS/Linux/WSL):
```bash
curl -fsSL https://claude.ai/install.sh | bash
```

**Windows PowerShell:**
```bash
irm https://claude.ai/install.ps1 | iex
```

**Start using it:**
```bash
cd your-project
claude
```

## Requirements

- A Claude subscription (Pro, Max, Teams, or Enterprise) or Claude Console account

Claude Code automatically updates in the background to keep you on the latest version.

---


# SKILL: plan-experiments

## FILE: plan-experiments/SKILL.md

---
name: plan-experiments
description: Planning or executing thesis experiments. Covers the lifecycle from ideation through polishing, tracking table, SPEC.md format, stage structure.
---

# Experiment Workflow

## Philosophy

**TODO.md tracks experiments** alongside other tasks. The "Research Experiments" section in the checklist area provides a quick scan; the "Details" section at the bottom preserves full context. [proposed]

**The checklist is an index; the detailed sections are the documentation.** Each experiment should have a `## <label>` section in the Details area that contains the actual content:
- The research question and any sub-questions it breaks into
- How this experiment connects to other experiments (dependencies, shared data, sequential logic)
- What the outcome implies for next steps (e.g., "if sys > 1 is rare, we need targeted search methods")
- Open questions and blockers
- Where the idea came from (conversation, paper, advisor discussion)

**Don't compress ideas.** When capturing a research idea, preserve the intellectual labor that went into articulating it. A one-line note in the table loses the nuance, connections, and decision points. Write the detailed section.

**One experiment can have multiple variants.** If an experiment explores multiple families or parameter settings (e.g., comparing "convex hull of random points" vs "intersection of random halfplanes"), keep it as one experiment entry. Each variant gets its own config file in `config/<label>/` (e.g., `convex-hull.json`, `halfplane-intersection.json`).

**Reproduction must be obvious:** Looking at the repo structure should make it clear what to run—no mental recall or documentation lookup required.

Good: `for cfg in config/polytope-families/*.json; do uv run python -m viterbo.experiments.polytope_families.stage_build "$cfg"; done` (pattern is self-evident)

Bad: "Run with configs A, B, and C" (which configs? where?)

Local iteration (one stage, one config) may use CLI args. Don't create separate table rows for each variant.

**Ideas have broader context.** An experiment idea doesn't exist only in experiments.md. It connects to:
- Conversations where the idea emerged
- Thesis chapters it might inform
- GitHub issues and roadmap
- Algorithm development (what's computable)
- Prior work (papers, theses)
- Follow-up questions that will emerge from results

## Example: example-pipeline

Study `src/viterbo/experiments/example_pipeline/` for a complete teaching example:
- SPEC.md with research question, method, success criteria
- Multiple stages: `stage_build.py` → `stage_analyze.py` → `stage_plot.py`
- Config file at `config/example-pipeline/default.json`
- Tests at `tests/test_example_pipeline.py`

## Terminology

- **label**: Short identifier (e.g., `polytope-database`). Used consistently in folder names, tracking table, config, data, assets.

## Workflow Stages

1. **Ideation** — Turn vague idea into clear research question
2. **Specification** — Write SPEC.md with success criteria
3. **Execution** — Implement and run
4. **Polishing** — Clean up for thesis publication

## Where Things Live

| Artifact | Location |
|----------|----------|
| Tracking | `TODO.md` (checklist + Details section) [proposed] |
| Experiment code | `packages/python_viterbo/src/viterbo/experiments/<label>/` |
| SPEC.md | `packages/python_viterbo/src/viterbo/experiments/<label>/SPEC.md` |
| Configs | `packages/python_viterbo/config/<label>/` |
| Data | `packages/python_viterbo/data/<label>/` |
| Thesis assets | `packages/latex_viterbo/assets/<label>/` |
| Polished writeups | `packages/latex_viterbo/chapters/appendix-detailed-experiments.tex` |

## SPEC.md Template

```markdown
# <label> Experiment

**Status:** Ideation / Specified / In Progress / Complete

## Research Question

What are we trying to learn?

## Method

How will we answer the question?

## Success Criteria

What outcome means "it worked"?

## Expected Outputs

- data/<label>/...
- assets/<label>/...
```

## Stage Details

### Ideation [proposed]

1. Add a checklist item to the "Research Experiments" section in `TODO.md` with: label, blocked status, brief note.
2. Add a `## <label>` section in the Details area at the bottom of TODO.md. This section should include:
   - The research question, stated clearly, plus any sub-questions
   - Proposed approach or methods
   - What patterns or answers you're looking for
   - How this experiment connects to others (dependencies, what it enables)
   - Blockers and dependencies
   - Where the idea came from (conversation, paper, advisor)
3. If agent-created, mark the section with `[proposed]`. No code folder yet at this stage.

### Specification

Create experiment folder with SPEC.md. Update tracking table to "Specified".

### Execution

Implement stages, run, produce data. See `develop-python` skill for code structure.

### Polishing

Clean up code, generate publication-quality figures, write thesis section.

## Approval Markers

See the `create-skill` skill for guidance on using `[proposed]` markers when editing experiments or other onboarding materials.

## Handoff [proposed]

When finishing work:
1. Update TODO.md (checklist status + Details section if needed)
2. Ensure SPEC.md reflects current state
3. Commit with message referencing label

---


# SKILL: plan-tasks

## FILE: plan-tasks/SKILL.md

---
name: plan-tasks
description: How to properly add and flesh out tasks in TODO.md. Most agents just mark tasks done; use this skill when creating or reorganizing tasks.
---

# Task Planning

**When to use this skill:**
- You need to add new tasks to TODO.md (because work is discovered that can't be done now)
- You need to restructure or reorganize TODO.md for clarity
- Jörn explicitly asks you to add tasks

**When NOT to use this skill:**
- Just marking tasks `[x]` as done (that's in CLAUDE.md Agent Protocol, always-on)
- Normal thesis work (build, test, commit)

---

## TODO

This skill needs to be fleshed out with actual content about how to structure tasks.

Key topics to cover:
- TODO.md file structure (checklist sections vs details sections)
- Status markers (`[ ]`, `[x]`, `[-]`)
- When to add simple one-liners vs detailed sections
- How to write good task descriptions
- When to add tasks vs when to just do the work

**Current guidance (from project-management skill):**

### File Structure

`TODO.md` at repo root:
- **Checklist sections** at top for quick scanning
- **Details section** at bottom for items needing context

### Status Markers

- `[ ]` — pending
- `[x]` — done
- `[-]` — blocked or deferred (with note)

### Adding Items

**Simple items:** One line in the appropriate checklist section.
```markdown
- [ ] Fix FFI facet limit
```

**Items with context:** Add sub-bullets or a `## label` section in Details.

### When to Add Tasks

Only add new tasks when:
- Work is discovered that can't be done now (blocked, out of scope)
- Jörn requests it

**Don't speculatively add tasks.** Jörn manages the backlog.

---


# SKILL: review-math-docs-code-correspondence

## FILE: review-math-docs-code-correspondence/SKILL.md

---
name: review-math-docs-code-correspondence
description: Ensure mathematical correctness and verify that code implements what the thesis specifies. Check correspondence between formulas, documentation, and implementation.
---

# Math-Docs-Code Correspondence Review

**When to use this skill:**
- Verifying that Rust code correctly implements mathematical formulas from the thesis
- Checking that code comments and documentation match actual implementation
- Ensuring numerical algorithms match their theoretical descriptions
- Reviewing whether code assumptions are documented and justified

---

## TODO

This skill needs to be fleshed out with actual content about how to review correspondence.

Key topics to potentially cover:
- How to trace from thesis formula to code implementation
- Verifying that tolerances match mathematical requirements
- Checking that algorithm invariants are documented and tested
- Ensuring geometric constructions match formal definitions
- When to add mathematical comments vs when code is self-documenting
- How to verify numerical correctness despite Rust's type system limitations (no dependent types)
- Standards for documenting mathematical derivations in code

**Note:** Some content from the former `quality-improvement` skill about mathematical correctness might belong here.

---


# SKILL: review-thesis-writing-style

## FILE: review-thesis-writing-style/SKILL.md

---
name: review-thesis-writing-style
description: Review and improve thesis writing quality. Use for style checks, exposition clarity, audience appropriateness, and LaTeX formatting conventions.
---

# Thesis Writing Style Review

**When to use this skill:**
- Reviewing thesis chapters for clarity and style
- Ensuring exposition is appropriate for symplectic geometers
- Checking LaTeX formatting conventions
- Improving readability and organization of mathematical writing

---

## TODO

This skill needs to be fleshed out with actual content about thesis writing standards.

Key topics to potentially cover:
- Audience expectations (symplectic geometers, self-contained exposition)
- How to separate mainline text from asides
- Notation introduction and consistency
- Proof structure and formatting
- Use of headings and signposting
- When to add spoilers/previews
- Handling work-in-progress sections
- Citation and reference style

**Current guidance (from latex-conventions skill):**

### Thesis writing style

- Audience: symplectic geometers; self-contained exposition.
- Separate mainline text from asides.
- Introduce notation once; note deviations from literature.
- Be explicit but skimmable; spoilers up front; headings guide the reader.
- Mark WIP text clearly (e.g., `\edit{}` or `%`).

---

