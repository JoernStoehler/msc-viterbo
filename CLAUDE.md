# CLAUDE.md

Jörn Stöhler's MSc Thesis at University of Augsburg.

**Topic:** Viterbo's Conjecture (systolic ratio ≤ 1) was disproved by HK-O 2024 with a 10-facet counterexample (sys ≈ 1.047). This thesis computationally probes the boundary cases to discover new conjectures.

## Context

- **Deadline:** End of March 2026
- **Priority:** Code correctness first, then experiments
- **Thesis as source of truth:** Code implements what thesis specifies. Correctness chain: thesis (math) → SPEC.md (design) → tests (verify spec) → code (must pass tests). When a test fails:
  1. Check: does test match spec?
  2. Check: does spec encode math correctly?
  3. If both yes → code is wrong
  4. If spec/test wrong → escalate to Jörn

## File Index

A file index is printed at session startup (via `.claude/hooks/session-start.sh`).
Use it to orient yourself.

Filenames are verbose to aid discoverability (e.g., `rust-algorithms.md` not `algorithms.md`).

### Key Locations

| Path | Purpose |
|------|---------|
| `packages/rust_viterbo/` | Rust workspace: `geom/` (primitives), `hk2017/` (EHZ capacity), `tube/` (tube domain), `ffi/` (PyO3) |
| `packages/python_viterbo/` | Python experiments in `src/viterbo/experiments/<label>/` |
| `packages/latex_viterbo/chapters/` | Thesis source; `chapters/math/` has core definitions |
| `docs/conventions/` | Development conventions, workflows, and checklists |
| `docs/papers/README.md` | Index of downloaded literature with key theorem locations |
| `.claude/commands/` | Agent role prompts (planner, developer, reviewer, etc.) |

### Project Structure

```
/workspaces/msc-viterbo/        Main worktree
/workspaces/worktrees/<task>/   Task-specific worktree
```

SPEC.md files define frozen requirements; found in experiment dirs and some crates.

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

# CI (mirrors remote)
cd /workspaces/worktrees/<task>/
scripts/ci.sh                       # Run all CI checks locally
scripts/ci.sh --rust                # Rust only
scripts/ci.sh --python              # Python + FFI only

# GitHub CLI (note: plain `gh issue view` is broken due to GraphQL deprecation)
gh issue view <N> --json title,body,labels --jq '.title, .body'  # Read issue
gh pr view <N>                      # Read PR
gh pr diff <N>                      # PR diff
gh pr checks <N> --watch            # Wait for CI
```

## Agent Protocol

Long-running project with sequential/parallel agents. Leave the repo clean for the next agent.

### When Assigned a Task

1. Work in the directory specified (default: `/workspaces/msc-viterbo`)
2. Consult `docs/conventions/` for relevant workflows and conventions
3. Do the work

### After Completing Work

1. Ensure tests pass
2. Commit and push (reference issue via "fixes #X" if applicable)
3. Note any out-of-scope discoveries in PR description

### Working Directory

- **CRITICAL:** Always use `cd /workspaces/worktrees/<task> && command`
- IDE always uses main repo cwd; commands need explicit `cd /workspaces/worktrees/<task> &&`
- See `docs/conventions/environments.md` for troubleshooting

### Escalation

Escalate to Jörn when:
- Task is ambiguous, contradictory, non-sensical or contains errors
- Any out-of-scope actions or decisions are needed
- Required context is unavailable (issue, spec, PR won't load)
- You are not confident enough in some step you executed to proceed further

A brief interruption beats running into a dead end. State blockers clearly in your final message.

### Task Management

Work tracked in GitHub Issues and Milestones. GH CLI is available.
Don't bother with task management unless explicitly assigned.

### Cleanup & Standards

- Remove any misleading content you find (outdated docs, stale comments, done TODOs)
- Preserve context where useful for future agents (explain the "why" in code comments, but delete legacy commentary since it is not useful)
- Prefer standard patterns — agents know them well
- Mark uncertainties clearly so that unverified false claims don't propagate

### Approval Markers

- `[proposed]` = agent proposal in a sensitive document awaiting Jörn's review
- Only Jörn removes these; ambiguous responses don't count

## Environment

The environment is provisioned for you, and everything should work out of the box.
See `docs/conventions/environments.md` for troubleshooting.

## Communication

- Jörn only reliably reads the **final message** of each turn. Structure accordingly: put decisions, questions, and summaries at the end, not interspersed with work updates.
- Jörn is available for questions, especially questions about ambiguous phrasings and missing context.
- Jörn appreciates pushback when he writes something unclear, makes mistakes or suggests something suboptimal or against best practices.
- Be direct, literal, and optimize for Jörn's time when you write a turn's final message. Structure your message to allow skimming. Use numbered lists to make referencing easier.
- Omit superfluous politeness and focus on information transfer and object-level progress.
- Make direct, explicit requests for permissions, clarifications, reviews, feedback and decisions when needed.
- Use Jörn's time wisely. Don't delegate work to him that you can do yourself.
- Leave long-term thesis project management to Jörn, you can help but he has more experience with long-running academic projects.
- Be precise and concrete, not vague or metaphorical. Don't use pseudo-profound phrases that obscure meaning.
- After making a mistake: pause, think carefully, and only then state concretely what was done wrong. Don't rush to respond with unclear apologies or preliminary diagnoses.
- When explaining conventions or structures: describe the actual purpose and mechanics, not just formatting rules.
