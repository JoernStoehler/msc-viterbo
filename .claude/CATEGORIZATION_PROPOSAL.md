# Knowledge Categorization Proposal

**Purpose:** Proposed split of knowledge inventory into CLAUDE.md, skills, code comments, and deletions.

**Status:** Draft for Jörn's review

**Date:** 2026-01-28

---

## Principles

### CLAUDE.md (Always-On Context, ~150 lines)
- Essential context for 80%+ of tasks
- Quick orientation: what is this project, what's the structure
- Quick command references (patterns agents can adapt)
- Agent protocol: how to work in this repo
- **Not**: Detailed procedures, domain-specific deep dives

### Skills (On-Demand, ~50-300 lines each)
- Deep dives into specific workflows
- Read when doing that type of work
- Can be more detailed since agents read them only when needed
- **Trigger via description field**, not body

### Code Comments/READMEs
- Implementation-specific details
- Mathematical derivations for specific algorithms
- API documentation

### Delete
- Information agents already know from training
- Redundant/obvious content
- Outdated or incorrect information

---

## Proposed CLAUDE.md Structure (~150 lines)

```markdown
# CLAUDE.md

Jörn Stöhler's MSc Thesis at University of Augsburg.

**Topic:** Viterbo's Conjecture - computational exploration of systolic ratio boundary cases. HK-O 2024 found a 10-facet counterexample (sys ≈ 1.047). This thesis probes for new conjectures.

## Timeline & Goals
- **Deadline:** End of March 2026
- **Priority:** Code correctness first, then experiments
- **Source of truth:** Thesis specifies math, code implements it

## Project Layout
[Tree diagram showing packages structure - keep as-is from current CLAUDE.md]

## Quick Commands
[Current quick commands section - keep as-is]
- Rust: cd packages/rust_viterbo && scripts/test.sh
- Python: cd packages/python_viterbo && uv run pytest
- LaTeX: cd packages/latex_viterbo && scripts/build.sh
- Exploration: scripts/repo-map.py

## Agent Protocol

**When assigned a task:**
1. Read TODO.md to understand context
2. Work on specified branch (or create it)
3. For parallel work: use git worktree (see develop-codespace skill)

**After completing work:**
1. **Mark task [x] in TODO.md** - don't forget
2. Ensure branch is PR-able (tests pass)
3. Update docs/comments if behavior changed
4. Remove stale TODOs/comments you created
5. Commit and push
6. If using worktree: clean up after PR merge

**Task management:**
- Don't speculatively add tasks - Jörn manages backlog
- Only add when work is blocked/out-of-scope or Jörn requests it
- Use plan-tasks skill when adding/reorganizing tasks

**Cleanup principles:**
- Remove misleading content (outdated docs, stale comments)
- Preserve context where needed (explain "why")
- Prefer standard patterns - agents know them well

**Approval markers:**
- [proposed] - awaiting Jörn's review
- Only Jörn removes these markers

## Skills

[Current skills table - keep as-is]

## Environment

**Currently using:** GitHub Codespaces (primary)

[Environment comparison table - simplified version]

## Communication with Jörn
- Jörn reads **final message** of each turn
- Use numbered lists for easy reference
- Be direct and concrete
- Pushback welcome
```

**Rationale:**
- Keeps orientation, quick commands, agent protocol (high-frequency needs)
- Removes detailed workflows (move to skills)
- Removes environment setup details (move to develop-codespace skill)
- ~150 lines, scannable, practical

---

## Proposed Skill: develop-rust

**When to use:** Writing or testing Rust code in packages/rust_viterbo

**Content (~200 lines):**

```markdown
# Rust Development

## Crate Organization
- **geom**: Clean reference implementations (symplectic + euclidean)
- **hk2017**: HK2017 algorithm (any polytope)
- **billiard**: Billiard algorithm (Lagrangian products only)
- **tube**: Tube algorithm (non-Lagrangian polytopes)
- **ffi**: PyO3/Maturin bindings

## Philosophy: geom as Reference
Algorithms should use geom when it fits, but copy and customize when needs diverge. Duplication is acceptable when purposeful. Value of geom: clean code to orient against, making deviations obvious.

## Commands

Test all modes:
```bash
cd packages/rust_viterbo
scripts/test.sh                  # Debug + release
scripts/test.sh --debug          # Debug only (with debug_assert!)
scripts/test.sh --release        # Release only (expensive tests)
```

Standard tooling:
```bash
cargo test --workspace           # Debug tests
cargo test --release --workspace # Release tests
cargo clippy --workspace         # Lint
cargo fmt --all                  # Format
```

## Testing Philosophy: Tests as Propositions

Write tests that verify mathematical propositions:
- Good: `prop_scaling_law` - "∀K, ∀λ>0: c(λK) = λ²c(K)"
- Bad: `test_random_stuff` - "call function, check no panic"

## Test Modes

**Debug mode** (default):
- Tests exercising `debug_assert!()` checks
- Tests verifying internal invariants
- Most unit tests

**Release mode:**
- Expensive tests (only verify output correctness)
- Property tests with many iterations
- Tests where computation speed matters

Mark tests with:
```rust
#[cfg_attr(debug_assertions, ignore)]  // Release only
#[cfg_attr(not(debug_assertions), ignore)]  // Debug only
```

## Testing Levels
1. **Debug assertions** (`debug_assert!`): Expensive internal invariants
2. **Runtime assertions** (`assert!`): Always-checked conditions
3. **Unit tests** (`#[test]`): Individual functions
4. **Property tests** (proptest): Random inputs
5. **Integration tests** (`tests/`): Full algorithm

## Numerical Tolerances

Use `approx` crate:
```rust
use approx::assert_relative_eq;
assert_relative_eq!(actual, expected, epsilon = 1e-10);
```

Define project-wide constants:
```rust
pub const EPS: f64 = 1e-10;           // General tolerance
pub const EPS_LAGRANGIAN: f64 = 1e-8; // Lagrangian 2-faces
pub const EPS_CLOSURE: f64 = 1e-6;    // Orbit closure
```

## Fixtures and Test Data

**Named constants** for standard objects:
```rust
pub fn unit_cross_polytope() -> PolytopeHRep { ... }
pub fn unit_24_cell() -> PolytopeHRep { ... }
```

**Parameterized families:**
```rust
pub fn scaled_cross_polytope(lambda: f64) -> PolytopeHRep { ... }
```

**Random generators:**
- Must be deterministic (seeded)
- Document distribution and rejection criteria
- Document success rates empirically

## Code Style
- Favor pure functions with immutable types
- Use nalgebra for linear algebra
- Document "why" in comments, not "what"
- Cover happy paths, edge cases, error paths

## Cache Behavior
- **Local env**: Shared target dir at `/workspaces/worktrees/shared/target`
- **Codespace**: Each worktree builds independently (~60s cold start)
```

**Rationale:**
- Focused on Rust-specific workflows
- Includes testing philosophy (important for mathematical code)
- Commands are patterns agents can adapt
- ~200 lines, on-demand when doing Rust work

---

## Proposed Skill: develop-python

**When to use:** Writing or testing Python code in packages/python_viterbo

**Content (~150 lines):**

```markdown
# Python Development

## Package Structure
- Package: `viterbo`
- Experiments: `src/viterbo/experiments/<label>/`
- Each experiment: SPEC.md + stage_*.py files

## Commands

```bash
cd packages/python_viterbo

# Setup (first time)
uv sync --extra dev

# Testing
uv run pytest                    # All tests
uv run pytest tests/test_foo.py  # Specific file

# Linting
uv run ruff format .             # Format
uv run ruff check --fix .        # Lint
uv run pyright                   # Type check
```

## Experiment Structure

**Always study example_pipeline first:**
`src/viterbo/experiments/example_pipeline/` is a complete teaching example.

**Standard layout:**
```
src/viterbo/experiments/<label>/
├── SPEC.md              # Research question, method, success criteria
├── stage_build.py       # Generate data
├── stage_analyze.py     # Compute results
└── stage_plot.py        # Create figures

config/<label>/
├── default.json         # Parameters
└── variant.json         # Alternative configs

data/<label>/            # Output artifacts
tests/test_<label>.py    # Tests
```

**Running stages:**
```bash
uv run python -m viterbo.experiments.<label>.stage_build
uv run python -m viterbo.experiments.<label>.stage_analyze
uv run python -m viterbo.experiments.<label>.stage_plot
```

**Reproduction must be obvious:**
Good: `for cfg in config/polytope-families/*.json; do uv run python -m viterbo.experiments.polytope_families.stage_build "$cfg"; done`
Bad: "Run with configs A, B, and C" (which configs? where?)

## Code Style
- Docstrings: inputs, outputs, shapes/dtypes
- Pure functions preferred
- Comments explain WHY, not WHAT
```

**Rationale:**
- Python-specific commands and conventions
- Emphasizes example_pipeline as template
- Shorter than Rust skill (Python experiments are simpler)

---

## Proposed Skill: develop-latex

**When to use:** Editing thesis or building PDFs/HTML

**Content (~100 lines):**

```markdown
# LaTeX/Thesis Development

## Commands

```bash
cd packages/latex_viterbo

scripts/lint.sh           # chktex + draft compile + latexml sanity
scripts/build.sh          # Full build (PDF + HTML)
scripts/build.sh --pdf-only
scripts/serve.sh          # Watch mode
```

**Draft speedup:** Use `includeonly.tex` (copy from `includeonly.tex.example`)

## LaTeX Style
- Inline: `\(...\)` not `$...$`
- Display: `\[...\]` not `$$...$$`
- Proofs: use `proof` environment
- arXiv-friendly packages only

## Thesis Writing Style
- **Audience**: Symplectic geometers, self-contained
- Separate mainline from asides
- Introduce notation once, note deviations from literature
- Explicit but skimmable: spoilers up front, headings guide reader
- Mark WIP: `\edit{}` or `%`

## Assets
- Python generates figures → `assets/<experiment>/`
- LaTeXML extras → `assets/{html/,latexml/}`
- Hand-crafted → `assets/manual/`
```

**Rationale:**
- LaTeX-specific commands and style conventions
- Writing style guidelines for thesis quality
- Asset management patterns

---

## Proposed Skill: develop-python-rust-interop

**When to use:** Building or modifying FFI bindings

**Content (~80 lines):**

```markdown
# Rust-Python FFI (PyO3 + maturin)

## Build

```bash
cd packages/python_viterbo
uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml
```

## Test

```bash
cd packages/python_viterbo
uv run pytest tests/test_ffi_capacity_hrep.py -v
```

## Design Principles
1. **Keep wrappers thin**: Convert types at boundary, delegate to library crates
2. **Validate at boundary**: Check inputs in FFI, return structured errors
3. **Expose only working code**: No stubs or archived placeholders
4. **Match stubs to implementation**: `rust_viterbo_ffi.pyi` must be accurate

## Key Files
- Rust FFI: `packages/rust_viterbo/ffi/src/lib.rs`
- Python stubs: `packages/python_viterbo/src/rust_viterbo_ffi.pyi`
- Tests: `packages/python_viterbo/tests/test_ffi_capacity_hrep.py`
```

**Rationale:**
- FFI work is infrequent but important
- Concise, focused on the workflow
- Design principles help maintain quality

---

## Proposed Skill: develop-codespace

**When to use:** Environment issues, git worktrees, devcontainer changes

**Content (~250 lines):**

```markdown
# Development Environments

## Three Environments

| Feature | Local | Codespace | CC Web |
|---------|-------|-----------|--------|
| Status | Backup | **Primary** | Emergency backup |
| TexLive | Yes | Yes | No |
| Rust/Python | Yes | Yes | Yes |
| Git worktrees | Scripts | Manual | No |
| Skills | Work | Work | Broken |
| Cache persistence | Bind mounts | No | No |

**Currently using:** GitHub Codespaces

## Environment Detection
```bash
if [[ "${DEVCONTAINER_ENV:-}" == "codespace" ]]; then
  echo "Codespace"
elif [[ -n "${CODESPACES:-}" ]]; then
  echo "Codespace (env var not set)"
elif [[ -n "${CLAUDE_CODE_REMOTE:-}" ]]; then
  echo "CC Web"
fi
```

## Codespace-Specific Notes
- Auto-stops after idle
- OAuth may not persist across rebuilds
- Caches don't persist
- `/workspaces/` persists (use for worktrees)

## Creating Codespace
```bash
gh codespace create -r JoernStoehler/msc-viterbo \
    --devcontainer-path .devcontainer/codespace/devcontainer.json
```

## Git Worktrees for Parallel Agents

### Setup
```bash
git worktree add /workspaces/worktrees/<task-name> -b <branch-name>
```

### Working Pattern

**CRITICAL:** VSCode IDE extension uses `/workspaces/msc-viterbo` as cwd. You **must** use `cd` in every bash command:

```bash
# Always cd before running commands
cd /workspaces/worktrees/<task> && cargo test
cd /workspaces/worktrees/<task> && git status
cd /workspaces/worktrees/<task> && uv run pytest

# Chain multiple commands
cd /workspaces/worktrees/<task> && cargo fmt && git add .
```

### Common Operations
```bash
# Rust tests
cd /workspaces/worktrees/<task> && cargo test

# Python tests
cd /workspaces/worktrees/<task> && cd packages/python_viterbo && uv run pytest

# Git operations
cd /workspaces/worktrees/<task> && git status
cd /workspaces/worktrees/<task> && git add .
cd /workspaces/worktrees/<task> && git commit -m "..."
cd /workspaces/worktrees/<task> && git push -u origin <branch>
```

### Cleanup
```bash
# After PR merge
git worktree remove /workspaces/worktrees/<task>
git worktree list  # Verify
```

### Key Limitations
1. **Skills/CLAUDE.md read from main repo**, not worktree
2. **Working directory is always main repo** (IDE behavior)
3. **No shared build cache** (each worktree builds independently)
4. **/workspaces/ persists** across Codespace rebuilds

### Alternative: Terminal CLI
For true parallelism without cd friction:
```bash
git worktree add /workspaces/worktrees/<task> -b <branch>
cd /workspaces/worktrees/<task>
claude  # Run CLI in worktree
```

## Modifying Environments

### Policy
- Environment changes require approval
- Make changes in devcontainer definition files
- Rebuild required after changes
- No default devcontainer.json (explicit selection required)

### Adding Dependencies

**Python packages:**
1. Add to `packages/python_viterbo/pyproject.toml`
2. Run `uv sync --extra dev`

**Rust crates:**
1. Add to `packages/rust_viterbo/*/Cargo.toml`
2. Run `cargo build`

**System dependencies (local/codespace only):**
1. Add to `.devcontainer/{local,codespace}/Dockerfile`
2. Update scripts to fail gracefully in CC web

## CC Web Limitations (Emergency Backup Only)
- apt-get does NOT work (DNS blocked)
- Skills are broken (not auto-loaded)
- No Playwright browsers
- No git worktrees
```

**Rationale:**
- Git worktrees are the most complex workflow here
- Environment-specific knowledge all in one place
- Only read when doing environment work or parallel agents

---

## Proposed Skill: plan-experiments

**When to use:** Planning or executing research experiments

**Content (~200 lines):**

```markdown
# Experiment Workflow

## Philosophy
- **TODO.md tracks experiments** alongside other tasks
- **Checklist is index; Details sections are documentation**
- **Don't compress ideas** - preserve intellectual labor
- **One experiment, multiple variants** - use separate config files
- **Reproduction must be obvious** - pattern self-evident from repo structure

## Study Before Creating
Always study `src/viterbo/experiments/example_pipeline/` first - it's a complete teaching example with all conventions.

## Terminology
- **label**: Short identifier (e.g., `polytope-database`), used consistently across folders

## Workflow Stages
1. **Ideation** - Turn vague idea into clear research question
2. **Specification** - Write SPEC.md with success criteria
3. **Execution** - Implement and run
4. **Polishing** - Clean up for thesis publication

## File Locations

| Artifact | Location |
|----------|----------|
| Tracking | TODO.md (checklist + Details section) |
| Code | `packages/python_viterbo/src/viterbo/experiments/<label>/` |
| SPEC.md | `packages/python_viterbo/src/viterbo/experiments/<label>/SPEC.md` |
| Configs | `packages/python_viterbo/config/<label>/` |
| Data | `packages/python_viterbo/data/<label>/` |
| Thesis assets | `packages/latex_viterbo/assets/<label>/` |

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

## Ideation Stage
1. Add checklist item to "Research Experiments" section in TODO.md
2. Add `## <label>` section in Details area with:
   - Research question (clearly stated)
   - Proposed approach
   - What patterns you're looking for
   - How this connects to other experiments
   - Blockers and dependencies
   - Where the idea came from
3. If agent-created, mark with `[proposed]`

## Specification Stage
Create experiment folder with SPEC.md. Update TODO.md to "Specified".

## Execution Stage
Implement stages, run, produce data. See develop-python skill.

## Polishing Stage
Clean up code, generate publication-quality figures, write thesis section.

## Handoff
When finishing:
1. Update TODO.md (checklist + Details if needed)
2. Ensure SPEC.md reflects current state
3. Commit with message referencing label
```

**Rationale:**
- Experiment workflow is specific enough to merit its own skill
- Philosophy section helps agents understand why things are structured this way
- Template provides concrete starting point

---

## Proposed Skill: plan-tasks

**When to use:** Adding or reorganizing tasks in TODO.md

**Content (~100 lines):**

```markdown
# Task Planning

**When to use this skill:**
- You need to add new tasks to TODO.md (work discovered that can't be done now)
- You need to restructure/reorganize TODO.md
- Jörn explicitly asks you to add tasks

**When NOT to use:**
- Just marking tasks [x] as done (that's in CLAUDE.md, always-on)
- Normal work (build, test, commit)

## TODO.md Structure
- **Checklist sections** at top for quick scanning
- **Details section** at bottom for items needing context
- **Status markers**: `[ ]` pending, `[x]` done, `[-]` blocked/deferred

## When to Add Tasks
Only when:
- Work is discovered that can't be done now (blocked, out of scope)
- Jörn requests it

**Don't speculatively add tasks** - Jörn manages the backlog.

## Simple vs Detailed Items

**Simple items:** One line in checklist
```markdown
- [ ] Fix FFI facet limit
```

**Items with context:** Add sub-bullets or `## label` section in Details
```markdown
## fix-ffi-facet-limit

Current FFI limits to 10 facets due to timeout concerns. Need to:
1. Profile HK2017 on 11-12 facet polytopes
2. Adjust timeout if performance acceptable
3. Update FFI validation
```

## How to Write Good Task Descriptions
- Action-oriented: "Fix X", "Implement Y", "Verify Z"
- Include acceptance criteria if not obvious
- Reference related issues/experiments/code locations
- Note blockers explicitly with `[-]` marker
```

**Rationale:**
- Task management is specific enough for a skill
- Agents don't need this often (Jörn manages backlog)
- When they do need it, they need clear guidelines

---

## Proposed Skill: review-math-docs-code-correspondence

**When to use:** Verifying code implements thesis specifications correctly

**Content (~150 lines):**

```markdown
# Math-Docs-Code Correspondence Review

**When to use:**
- Verifying Rust code implements thesis formulas correctly
- Checking code comments match implementation
- Ensuring numerical algorithms match theoretical descriptions
- Reviewing whether assumptions are documented

## Review Checklist

### 1. Formula Correspondence
- [ ] Locate formula in thesis (chapter, section, equation number)
- [ ] Locate implementation in code (file, function, line)
- [ ] Verify variable names match or are documented
- [ ] Check sign conventions match
- [ ] Verify order of operations matches

### 2. Numerical Tolerances
- [ ] Tolerances are defined as constants, not magic numbers
- [ ] Tolerance values match thesis specifications
- [ ] Accumulated error is considered for iterative algorithms

### 3. Assumptions and Preconditions
- [ ] Algorithm preconditions documented (e.g., "K must be star-shaped")
- [ ] Preconditions checked in code (assert! or runtime validation)
- [ ] Edge cases documented (what happens at boundaries?)

### 4. Test Coverage
- [ ] Tests verify mathematical properties (e.g., scaling laws)
- [ ] Known ground truth cases tested (e.g., cross-polytope, 24-cell)
- [ ] Edge cases have tests

## Common Pitfalls

**Sign errors:**
- Symplectic form is antisymmetric: ω(x,y) = -ω(y,x)
- Check matrix transpose conventions

**Coordinate conventions:**
- Thesis uses (q,p) split, code uses (x,y,z,w) or vice versa?
- Document mapping clearly

**Tolerance mismatches:**
- Code uses 1e-10 but thesis assumes exact arithmetic?
- Document where approximations occur

## Documentation Standards

**Mathematical derivations in code:**
Use comments for short derivations:
```rust
// Reeb vector: R(n,h) = 2·J·n / h
// where J is the standard complex structure on R⁴
// See thesis chapter 3, section 2.1
```

**For longer derivations:**
Reference thesis or separate doc:
```rust
// Trivialization formula derived in docs/trivialization-derivation.md
// See also thesis chapter 4, theorem 4.2
```

## When Code and Thesis Diverge

**If code is correct and thesis is wrong:**
1. Fix thesis first
2. Then verify code matches updated thesis

**If they're both correct but differ:**
- Document why they differ
- Example: "Thesis uses exact arithmetic, code uses floating point"

## Verification Process

1. **Read thesis section** that specifies the algorithm
2. **Read code implementation**
3. **Check correspondence** systematically
4. **Run tests** to verify mathematical properties hold
5. **Document findings** (code comments or thesis updates)
```

**Rationale:**
- Mathematical correctness is critical for this thesis
- Provides systematic review process
- Only read when doing verification work

---

## Proposed Skill: review-thesis-writing-style

**When to use:** Reviewing thesis writing quality and style

**Content (~100 lines):**

```markdown
# Thesis Writing Style Review

**When to use:**
- Reviewing thesis chapters for clarity
- Ensuring exposition is appropriate for audience
- Checking LaTeX formatting conventions
- Improving readability and organization

## Audience and Goals
- **Audience**: Symplectic geometers
- **Self-contained**: Expose assumptions, define notation
- **Skimmable**: Headings and structure guide reader

## Style Guidelines

### Exposition Structure
- **Spoilers up front**: State main results before proofs
- **Mainline vs asides**: Keep main argument clear, use remarks/footnotes for tangents
- **Progressive refinement**: Start intuitive, add rigor incrementally

### Notation
- **Introduce once**: Define notation when first used
- **Note deviations**: Call out when notation differs from literature
- **Consistency**: Don't switch notation mid-chapter

### Proofs
- **Use proof environment**: `\begin{proof}...\end{proof}`
- **Signpost structure**: "First we show X. Then we use X to prove Y."
- **Label key steps**: Equations that are referenced later need \label{}

### Work-in-Progress
- **Mark clearly**: Use `\edit{...}` or `% TODO: ...`
- **Remove before final**: WIP markers should not be in submitted thesis

## Common Issues to Check

**Passive voice overuse:**
- Bad: "It was shown that..."
- Good: "We show that..." or "Theorem 3.2 states that..."

**Undefined notation:**
- Check that every symbol is defined before use
- Exception: Standard notation (R, Z, etc.)

**Proof without roadmap:**
- Long proofs need structure
- Add "Proof strategy" paragraph or outline steps

**Missing citations:**
- Every non-obvious statement needs a citation or proof
- Standard results can cite textbooks

## LaTeX Quality Checks

**Math mode:**
- Inline: `\(...\)` not `$...$`
- Display: `\[...\]` not `$$...$$`

**Cross-references:**
- Use `\ref{}` not hardcoded numbers
- Use `\eqref{}` for equations

**Consistent macros:**
- Define custom commands in preamble, not inline
- Example: `\newcommand{\Sp}{\operatorname{Sp}}` for symplectic group
```

**Rationale:**
- Thesis quality is important for final grade
- Style review is infrequent but valuable
- Concrete guidelines help agents provide useful feedback

---

## Proposed Skill: download-arxiv-papers

**When to use:** Need to read arXiv paper's actual content

**Content (~150 lines):**
[Keep most of the current skill - it's already well-structured]

Key sections to retain:
- When to use (reading formulas/proofs vs just citing)
- Location (docs/papers/)
- Download workflow (script usage)
- Reading TeX files (labels vs numbers, custom macros)
- Folder naming convention

**Rationale:**
- Current skill is already good
- Paper management is infrequent but important
- TeX reading tips are valuable

---

## Items to Move to Code Comments

### 1. Mathematical Derivations
**From inventory section 4 (Rust Development):**
- Detailed explanations of specific formulas → inline comments in geom crate
- Trivialization formulas → already in `docs/trivialization-derivation.md` (good)

**Example:**
Instead of documenting symplectic form formula in skill, put it in code:
```rust
// packages/rust_viterbo/geom/src/symplectic.rs

/// Symplectic form ω: R⁴ × R⁴ → R
///
/// ω((q₁,p₁), (q₂,p₂)) = q₁·p₂ - q₂·p₁
///
/// Properties:
/// - Antisymmetric: ω(x,y) = -ω(y,x)
/// - Bilinear
/// - Non-degenerate
///
/// See thesis chapter 2, section 2.1 for mathematical background.
pub fn symplectic_form(a: &Vector4<f64>, b: &Vector4<f64>) -> f64 {
    // Split into (q,p) coordinates
    let (q1, p1) = (a.xy(), a.zw());
    let (q2, p2) = (b.xy(), b.zw());
    q1.dot(&p2) - q2.dot(&p1)
}
```

### 2. API Documentation
**From inventory section 7 (FFI):**
- Detailed API specs → docstrings in ffi/src/lib.rs
- Type conversion details → implementation comments

### 3. Build Script Documentation
**From inventory section 6 (LaTeX):**
- HTML pipeline details → comments in scripts/build.sh
- ar5iv integration notes → keep in OLD_SKILLS_ARCHIVE but reference from script

---

## Items to Move to Package READMEs

### 1. Rust Package Status
**From inventory section 4:**
Keep/expand `packages/rust_viterbo/docs/README.md` with:
- Crate status table (already there - good)
- Links to detailed specs
- Quick start example

### 2. Python Data Layout
**From inventory section 5:**
Keep `packages/python_viterbo/data/README.md` (already minimal - good)

### 3. Devcontainer Overview
**Keep `.devcontainer/README.md`** (already good)

---

## Items to Delete (Obvious or Redundant)

### 1. Standard Tool Usage
**From inventory sections 4, 5:**
- Agents know how to run `cargo test`, `pytest`, `ruff`
- Keep quick commands as patterns, delete detailed flag explanations

**Delete:**
- Full pytest flag documentation
- Detailed cargo command options
- Standard linter configuration

**Keep (as patterns):**
```bash
cd packages/rust_viterbo && scripts/test.sh --debug
cd packages/python_viterbo && uv run pytest tests/test_foo.py
```

### 2. Git Basics
**From inventory section 8:**
- Agents know `git add`, `git commit`, `git push`
- Keep safety protocol (what NOT to do)
- Keep worktree workflow (non-standard)

**Delete:**
- How to stage files (obvious)
- How to write commit messages (keep Co-Authored-By format)

### 3. File System Basics
**From inventory section 2:**
- Agents can read directory trees
- Keep high-level layout diagram
- Delete obvious file path explanations

---

## Open Questions for Discussion

### 1. Mathematical Definitions
Should CLAUDE.md include brief definitions of key terms (EHZ capacity, systolic ratio, symplectic form)?
- **Pro**: Quick orientation for agents
- **Con**: Agents can read thesis; adds to always-on context

**Recommendation**: No - just reference thesis chapters. Add one-line descriptions in CLAUDE.md topic section.

### 2. Proptest Strategies
Should develop-rust skill include proptest strategy examples?
- **Pro**: Helps agents write property tests correctly
- **Con**: Adds length; agents can read existing tests as examples

**Recommendation**: Include brief proptest section (~20 lines) with link to existing examples.

### 3. Common Agent Task Patterns
Should we add a skill with common task patterns (e.g., "add a new algorithm", "fix a numerical bug")?
- **Pro**: Accelerates common workflows
- **Con**: Adds maintenance burden; patterns evolve

**Recommendation**: Defer - if patterns emerge, add later.

### 4. Numerical Algorithms Details
Should we document convergence criteria, iteration limits, etc. in skills or thesis?
- **Pro**: Implementation details belong in code docs
- **Con**: Mathematical justification belongs in thesis

**Recommendation**: Split - math justification in thesis, implementation parameters in code comments.

---

## Summary of Changes

### CLAUDE.md
- **Keep**: Project context, structure, quick commands, agent protocol, skills table, communication guidelines
- **Remove**: Detailed workflows (→ skills), environment setup details (→ develop-codespace), mathematical background (→ thesis/code)
- **Target length**: ~150 lines
- **Current length**: ~150 lines (already good!)

### Skills
- **Keep/improve**: All current skills (develop-*, plan-*, review-*, download-arxiv-papers)
- **Remove from each**: Redundant/obvious info, move detailed math to code comments
- **Add**: More structure, clearer when-to-use, concrete examples
- **Target length**: 50-300 lines each depending on complexity

### Code Comments
- **Add**: Mathematical derivations, formula explanations, API documentation
- **Standard**: Reference thesis chapters for background

### Package READMEs
- **Keep**: Current status/overview docs (already minimal and good)

### Delete
- Standard tool usage details
- Git basics (keep safety protocol)
- Obvious file system navigation

---

## Next Steps

1. **Jörn reviews this proposal** - adjust categorization
2. **Write new CLAUDE.md** from scratch using this structure
3. **Refactor each skill** using this as guide
4. **Add code comments** for mathematical content
5. **Create PR** with all changes
