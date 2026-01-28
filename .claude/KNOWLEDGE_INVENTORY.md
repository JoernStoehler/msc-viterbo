# Knowledge Inventory for MSc Viterbo Project

**Purpose:** Comprehensive catalog of procedural and factual knowledge agents need when working on this thesis project. This inventory will inform the design of CLAUDE.md and skills.

**Status:** Draft - awaiting review and refinement

**Date:** 2026-01-28

---

## 1. Project Context & Goals

### Core Thesis Topic
- **Viterbo's Conjecture**: systolic ratio c(K)²/Vol(K) ≤ 1 for convex bodies
- **HK-O 2024 counterexample**: 10-facet polytope (pentagon × rotated pentagon), sys ≈ 1.047
- **Thesis goal**: Computationally probe boundary cases to discover new conjectures (proving is out of scope)

### Timeline & Constraints
- **Deadline**: End of March 2026 (project frozen, thesis printed, graded)
- **Advisor**: Kai (pure mathematician), last meeting 2026-01-26
- **Priority**: Code correctness first, then experiments
- No intermediate milestones or defense talk planned

### Source of Truth Hierarchy
- **Thesis**: Authoritative mathematical specification
- **Code**: Implements what thesis specifies
- **Docs/specs**: Explain implementation details, reference thesis for math

---

## 2. Repository Structure

### Package Layout
```
packages/
  rust_viterbo/          # Geometric computations
    geom/                # Polytope types, symplectic/euclidean geometry
    hk2017/              # HK2017 permutation enumeration algorithm
    billiard/            # Billiard trajectory algorithm (Clarke dual)
    tube/                # Tube domain branch-and-bound
    ffi/                 # PyO3 bindings to Python
  python_viterbo/        # Experiments and analysis
    src/viterbo/
      experiments/       # One folder per experiment
    config/              # JSON configs per experiment
    data/                # Output artifacts
    tests/               # pytest tests
  latex_viterbo/         # Thesis document
    chapters/            # .tex files; chapters/math/ = core definitions
    assets/              # Figures, generated plots
```

### Key Files
- `TODO.md` - Task tracking and experiment queue
- `CLAUDE.md` - Agent onboarding and protocols
- `scripts/repo-map.py` - Detailed file tree visualization
- `.devcontainer/` - Three environment configs (local/codespace/ccweb)
- `.claude/skills/` - Workflow documentation

### Data Flow Patterns
- Python generates figures → `latex_viterbo/assets/<experiment>/`
- Experiment outputs → `python_viterbo/data/<experiment>/`
- Rust crates expose to Python via FFI

---

## 3. Development Environments

### Three Supported Environments

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| Status | Backup | **Primary** | Emergency backup |
| TexLive | Yes | Yes | No |
| LaTeXML | Yes | Yes | No |
| Rust, Cargo | Yes | Yes | Yes |
| Python, uv | Yes | Yes | Yes |
| gh CLI | Yes | Yes | Auto-installed |
| Cache persistence | Bind mounts | No | No |
| Git worktrees | Scripts | Manual | No |
| Skills | Work | Work | Broken |
| Parallel agents | Scripts | Worktrees + IDE | No |

### Environment Detection
- `DEVCONTAINER_ENV` env var: "local" or "codespace"
- `CODESPACES` env var: present in Codespaces
- `CLAUDE_CODE_REMOTE` env var: present in CC Web

### Codespace-Specific Knowledge (Primary Environment)
- **Currently using**: GitHub Codespaces with VSCode IDE extension in browser
- Auto-stops after idle period
- OAuth may not persist across rebuilds
- Caches don't persist across rebuilds
- `/workspaces/` persists across rebuilds (use for worktrees)

### Creating Codespace
```bash
gh codespace create -r JoernStoehler/msc-viterbo \
    --devcontainer-path .devcontainer/codespace/devcontainer.json
```

### CC Web Limitations (Emergency Backup Only)
- apt-get does NOT work (DNS blocked by proxy)
- Skills are broken (not auto-loaded)
- No Playwright browsers
- No git worktrees support

---

## 4. Rust Development

### Crate Organization
- **geom**: Clean reference implementations (symplectic + euclidean geometry, 2D + 4D)
- **hk2017**: HK2017 algorithm (works on any polytope)
- **billiard**: Billiard algorithm (Lagrangian products only)
- **tube**: Tube algorithm (non-Lagrangian polytopes)
- **ffi**: PyO3/Maturin bindings

### Philosophy: geom as Reference
- Algorithms should use geom when it fits
- Copy and customize when algorithm-specific needs diverge
- Duplication is acceptable when purposeful
- Value of geom: clean code to orient against, making deviations obvious

### Common Commands
```bash
cd packages/rust_viterbo

# Test (all modes)
scripts/test.sh                  # Debug + release
scripts/test.sh --debug          # Debug only (with debug_assert!)
scripts/test.sh --release        # Release only (expensive tests)

# Standard tooling
cargo test --workspace           # Debug tests
cargo test --release --workspace # Release tests
cargo clippy --workspace         # Lint
cargo fmt --all                  # Format
cargo bench                      # Benchmarks
```

### Test Organization

**Debug mode** (default):
- Tests exercising `debug_assert!()` checks
- Tests verifying internal invariants
- Most unit tests

**Release mode**:
- Expensive tests (only verify output correctness)
- Property tests with many iterations
- Tests where computation speed matters

**Markers**:
```rust
#[cfg_attr(debug_assertions, ignore)]  // Release only
#[cfg_attr(not(debug_assertions), ignore)]  // Debug only
```

### Testing Philosophy: Tests as Propositions
- Good: `prop_scaling_law` - "∀K, ∀λ>0: c(λK) = λ²c(K)"
- Bad: `test_random_stuff` - "call function, check no panic"

### Testing Levels
1. **Debug assertions**: Expensive internal invariants
2. **Runtime assertions**: Always-checked conditions
3. **Unit tests**: Individual functions
4. **Property tests** (proptest): Random inputs
5. **Integration tests** (`tests/`): Full algorithm

### Numerical Tolerances
- Use `approx` crate: `assert_relative_eq!(actual, expected, epsilon = 1e-10)`
- Define project-wide constants (EPS, EPS_LAGRANGIAN, EPS_CLOSURE)

### Fixtures and Test Data
- Named constants for standard objects (unit_cross_polytope, unit_24_cell)
- Parameterized families (scaled, asymmetric variants)
- Random generators must be deterministic (seeded) with documented distributions

### Cache Behavior
- **Local**: Shared target dir at `/workspaces/worktrees/shared/target` via `CARGO_TARGET_DIR`
- **Codespace**: Each worktree builds independently (~60s cold start)

---

## 5. Python Development

### Package Structure
- Package: `viterbo`
- Experiments: `src/viterbo/experiments/<label>/`
- Each experiment: SPEC.md + stage_*.py files

### Common Commands
```bash
cd packages/python_viterbo

# Setup
uv sync --extra dev              # Install dependencies (first time)

# Testing
uv run pytest                    # All tests
uv run pytest tests/test_foo.py  # Specific test

# Linting
uv run ruff format .             # Format
uv run ruff check --fix .        # Lint
uv run pyright                   # Type check
```

### Experiment Structure (Use example_pipeline as Template)

**Standard layout**:
```
src/viterbo/experiments/<label>/
├── SPEC.md              # Research question, method, success criteria
├── stage_build.py       # Generate data
├── stage_analyze.py     # Compute results
└── stage_plot.py        # Create figures

config/<label>/
├── default.json         # Parameters
└── variant.json         # Alternative parameters

data/<label>/            # Output artifacts

tests/test_<label>.py    # Tests
```

**Running stages**:
```bash
uv run python -m viterbo.experiments.<label>.stage_build
uv run python -m viterbo.experiments.<label>.stage_analyze
uv run python -m viterbo.experiments.<label>.stage_plot
```

### Code Style
- Docstrings: inputs, outputs, shapes/dtypes
- Pure functions preferred
- Comments explain WHY, not WHAT

---

## 6. LaTeX/Thesis Development

### Build and Serve
```bash
cd packages/latex_viterbo

scripts/lint.sh           # chktex + draft compile + latexml sanity
scripts/build.sh          # Full build
scripts/build.sh --pdf-only
scripts/build.sh --html-only
scripts/serve.sh          # Watch mode
```

### Draft Speedup
- Use `includeonly.tex` (copy from `includeonly.tex.example`)

### LaTeX Style Conventions
- Inline math: `\(...\)` not `$...$`
- Display math: `\[...\]` not `$$...$$`
- Proofs: use `proof` environment
- Label theorems/lemmas consistently
- arXiv-friendly packages only

### Thesis Writing Style
- **Audience**: Symplectic geometers
- **Self-contained**: Expose assumptions and notation
- **Separate mainline from asides**
- **Introduce notation once**, note deviations from literature
- **Explicit but skimmable**: spoilers up front, headings guide reader
- **Mark WIP text**: use `\edit{}` or `%`

### Assets
- LaTeX includes assets from `packages/latex_viterbo/assets/<experiment>/`
- Python generates assets there
- LaTeXML extras: `assets/{html/,latexml/}`
- Hand-crafted: `assets/manual/`

### HTML Pipeline (ar5iv-like)
- Uses LaTeXML with ar5iv bindings (vendored at `assets/latexml/ar5iv-bindings`)
- CSS bundle vendored at `assets/html/css/`
- Postprocessed DOM for left-rail TOC layout

---

## 7. FFI / Rust-Python Interop

### Build FFI
```bash
cd packages/python_viterbo
uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml
```

### Test FFI
```bash
cd packages/python_viterbo
uv run pytest tests/test_ffi_capacity_hrep.py -v
```

### API Exposed
- `hk2017_capacity_hrep(normals, heights, use_graph_pruning=False) -> Hk2017Result`
- `symplectic_form_4d(a, b) -> float`

### Design Principles
1. **Keep wrappers thin**: Convert types at boundary, delegate to library crates
2. **Validate at boundary**: Check inputs in FFI, return structured errors
3. **Expose only working code**: No stubs or archived placeholders
4. **Match stubs to implementation**: `rust_viterbo_ffi.pyi` must be accurate

### Key Files
- Rust FFI: `packages/rust_viterbo/ffi/src/lib.rs`
- Python stubs: `packages/python_viterbo/src/rust_viterbo_ffi.pyi`
- Tests: `packages/python_viterbo/tests/test_ffi_capacity_hrep.py`

---

## 8. Git Workflows

### Parallel Work via Worktrees (Codespace)

**Setup**:
```bash
git worktree add /workspaces/worktrees/<task-name> -b <branch-name>
```

**Working pattern** (IDE extension uses main repo as cwd):
```bash
# CRITICAL: Always cd before commands
cd /workspaces/worktrees/<task-name> && cargo test
cd /workspaces/worktrees/<task-name> && git status
cd /workspaces/worktrees/<task-name> && git add .
```

**Cleanup**:
```bash
# After PR merge
git worktree remove /workspaces/worktrees/<task-name>
git worktree list  # Verify
```

**Key limitations**:
- Skills and CLAUDE.md read from main repo, not worktree
- Working directory is always `/workspaces/msc-viterbo` (IDE behavior)
- No shared build cache (each worktree builds independently)
- `/workspaces/` persists across Codespace rebuilds

**Alternative**: Terminal CLI for true parallelism (cd into worktree, run `claude`)

### Commit Workflow

**When to commit**:
- Only when explicitly requested by user
- Never proactively commit unless asked

**Safety protocol**:
- NEVER update git config
- NEVER run destructive commands (push --force, reset --hard, checkout ., restore ., clean -f, branch -D) unless explicitly requested
- NEVER skip hooks (--no-verify, --no-gpg-sign) unless requested
- NEVER force push to main/master
- CRITICAL: Create NEW commits, not amend (unless requested)
- Prefer staging specific files by name over `git add -A` or `git add .`

**Commit message format**:
```bash
git commit -m "$(cat <<'EOF'
Brief summary here.

Co-Authored-By: Claude Sonnet 4.5 <noreply@anthropic.com>
EOF
)"
```

**Pre-commit hook failures**:
- Fix issue and create NEW commit (not --amend)
- Hook failure means commit did NOT happen

### Pull Request Workflow

**When requested**:
1. Run `git status`, `git diff`, `git log`, `git diff [base-branch]...HEAD` in parallel
2. Analyze ALL commits (not just latest) for PR description
3. Draft PR title (< 70 characters) and body
4. Create new branch if needed, push with `-u` if needed
5. Use `gh pr create` with HEREDOC for body formatting

**Do not**:
- Use TodoWrite or Task tools during PR creation
- Run additional commands to explore code
- Return PR URL when done

---

## 9. Task Management

### TODO.md Structure
- **Checklist sections** at top for quick scanning
- **Details section** at bottom for items needing context
- **Status markers**: `[ ]` pending, `[x]` done, `[-]` blocked/deferred

### When to Add Tasks
- Only when work is discovered that can't be done now (blocked, out of scope)
- Only when Jörn requests it
- **Don't speculatively add tasks** - Jörn manages the backlog

### Simple vs Detailed Items
- **Simple**: One line in checklist
- **With context**: Add sub-bullets or `## label` section in Details

### Marking Tasks Done
- **Always mark `[x]` in TODO.md after completing work**
- Don't forget this step

---

## 10. Experiment Workflow

### Philosophy
- **TODO.md tracks experiments** alongside other tasks
- **Checklist is an index; Details sections are documentation**
- **Don't compress ideas** - preserve intellectual labor when capturing research ideas
- **One experiment, multiple variants** - use separate config files, not separate experiment entries
- **Reproduction must be obvious** - pattern should be self-evident from repo structure

### Terminology
- **label**: Short identifier (e.g., `polytope-database`), used consistently across folders

### Workflow Stages
1. **Ideation** - Turn vague idea into clear research question
2. **Specification** - Write SPEC.md with success criteria
3. **Execution** - Implement and run
4. **Polishing** - Clean up for thesis publication

### File Locations

| Artifact | Location |
|----------|----------|
| Tracking | `TODO.md` (checklist + Details section) |
| Code | `packages/python_viterbo/src/viterbo/experiments/<label>/` |
| SPEC.md | `packages/python_viterbo/src/viterbo/experiments/<label>/SPEC.md` |
| Configs | `packages/python_viterbo/config/<label>/` |
| Data | `packages/python_viterbo/data/<label>/` |
| Thesis assets | `packages/latex_viterbo/assets/<label>/` |
| Writeups | `packages/latex_viterbo/chapters/appendix-detailed-experiments.tex` |

### SPEC.md Template
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

### Study Before Creating
- Always study `src/viterbo/experiments/example_pipeline/` first
- It's a complete teaching example with all conventions

---

## 11. Agent Protocol

### When Assigned a Task
1. **Read TODO.md** to understand task in context
2. If task isn't in TODO.md, add it before starting
3. Work on branch specified in assignment (create if needed)
4. **For parallel work**: Set up git worktree

### After Completing Work
1. **Mark task `[x]` in TODO.md** - don't forget
2. Ensure branch is PR-able (tests pass, no broken code)
3. Update docs/comments if behavior changed
4. Remove stale TODOs or comments you created
5. Commit and push
6. **If using worktree**: Clean up after PR merge

### Cleanup Principles
- Remove misleading content (outdated docs, stale comments, done TODOs)
- Preserve context where needed (explain "why" in code comments, thesis)
- Prefer standard patterns over custom solutions

### Approval Markers
- `[proposed]` - agent proposal awaiting Jörn's review
- Only Jörn removes these; ambiguous responses don't count

---

## 12. Mathematical Context

### Key Sources
- **Haim-Kislev MSc thesis**: Simplex capacity, sys ≤ 3/4 claim - online access available, agents should find and download if needed
- **HK-O 2024 counterexample**: 10 facets is smallest known; nobody has found fewer
- **HK2017 reference implementation**: github.com/pazithaimkislev/EHZ-capacity (no QCQP solver)

### Paper Management
- Papers stored in `docs/papers/<CitationKey-description>/`
- TeX sources preferred over PDFs (more reliable for agents to read)
- Download script: `.claude/skills/download-arxiv-papers/download-arxiv.sh`
- Always update `docs/papers/README.md` and `packages/latex_viterbo/references.bib` after downloading

### Reading Papers
- Read .tex files directly (plain text, formulas intact)
- Labels (e.g., `\label{thm:main}`) are more descriptive than numbers
- Watch for custom macros (e.g., `\bthm` instead of `\begin{theorem}`)
- PDF parsing mangles math notation - avoid for formulas

---

## 13. Communication with Jörn

### Message Structure
- Jörn reads **final message** of each turn
- Put decisions, questions, summaries there
- Use numbered lists for easy reference
- Be direct and concrete
- Pushback welcome when instructions unclear or suboptimal

---

## 14. Skills System

### Skills Location
- `.claude/skills/` contains workflow documentation
- Each skill: `SKILL.md` with YAML frontmatter

### Available Skills (When to Read)

| Skill | When to read |
|-------|--------------|
| `develop-rust` | Writing Rust code |
| `develop-python` | Writing Python code |
| `develop-latex` | Editing thesis |
| `develop-python-rust-interop` | Building/modifying FFI bindings |
| `develop-codespace` | Changing devcontainer, git worktrees, env issues |
| `plan-experiments` | Planning or executing research experiments |
| `plan-tasks` | Adding or reorganizing tasks in TODO.md |
| `review-math-docs-code-correspondence` | Verifying code↔thesis correctness |
| `review-thesis-writing-style` | Reviewing thesis writing |
| `download-arxiv-papers` | Need to read arXiv paper content |
| `official-claude-code-guides` | Questions about Claude Code |
| `skill-creator` | Creating or editing skills |

### CC Web Workaround
- Skills broken in CC Web (not auto-loaded as of Jan 2026)
- Workaround: Manual skill index in CLAUDE.md
- Remove workaround when CC fixes this

---

## 15. Quick Command Reference

### Exploration
```bash
scripts/repo-map.py              # Detailed file tree
```

### Rust
```bash
cd packages/rust_viterbo
scripts/test.sh                  # All tests
scripts/test.sh --debug          # Debug tests only
scripts/test.sh --release        # Release tests only
cargo clippy --workspace         # Lint
cargo fmt --all                  # Format
```

### Python
```bash
cd packages/python_viterbo
uv sync --extra dev              # Install deps
uv run pytest                    # Test
uv run ruff check src tests      # Lint
```

### LaTeX
```bash
cd packages/latex_viterbo
scripts/lint.sh                  # Lint
scripts/build.sh                 # Build
scripts/serve.sh                 # Serve with watch
```

### Git Worktrees (Codespace)
```bash
# Create
git worktree add /workspaces/worktrees/<task> -b <branch>

# Work (always cd!)
cd /workspaces/worktrees/<task> && <command>

# Cleanup
git worktree remove /workspaces/worktrees/<task>
git worktree list
```

---

## Notes for Future Refinement

### Items to Potentially Prune
- Details that are obvious to all agents (standard cargo/pytest usage)
- Information better located in code comments
- Redundant information already in tool descriptions

### Items to Potentially Expand
- When to use which test mode (debug vs release)
- How to verify mathematical correctness
- When to break down tasks vs tackle directly

### Items to Move Elsewhere
- Mathematical proofs/derivations → thesis or rust_viterbo/docs/
- Detailed API specs → code documentation
- Historical notes → separate archive file

### Open Questions
1. Should we document the actual mathematical definitions (EHZ capacity, systolic ratio, etc.) or assume agents can read the thesis?
2. How much detail on proptest strategies and fixtures?
3. Should we include examples of common agent tasks as patterns?
4. What level of detail on numerical tolerances and convergence criteria?

---

**Next Steps**:
1. Review this inventory for correctness and completeness
2. Identify what belongs in CLAUDE.md (always-on) vs skills (on-demand)
3. Identify what should move to code comments or other files
4. Write new CLAUDE.md from scratch using progressive disclosure
5. Refactor skills to use proper structure and be concise
