# CLAUDE.md

[proposed]

Jörn Stöhler's MSc Thesis on Viterbo's Conjecture (University of Augsburg).

**Topic:** Viterbo's Conjecture (systolic ratio <= 1) was disproved by HK-O 2024. This thesis computationally probes boundary cases to discover new conjectures.

## Context

- **Deadline:** End of March 2026
- **Priority:** correctness >> clarity >> performance

## Correctness Chain

```
thesis (math) -> proofs -> signatures -> tests -> code
```

When tests fail:
1. Does test match spec?
2. Does spec encode math correctly?
3. If both yes -> code is wrong
4. If spec/test wrong -> escalate to Jörn

## Repository Map

```
packages/
  rust_viterbo/           # Rust workspace
    geom2d/               #   2D geometry primitives
    geom4d/               #   4D polytope operations
    docs/legacy-reference.md  # Deleted crates (git history)
  python_viterbo/         # Python experiments
  latex_viterbo/          # Thesis LaTeX
docs/
  learnings/              # Extracted experiment learnings
  tasks/                  # Local task tracking (ROADMAP.md)
  conventions/            # Development workflows
  papers/                 # Literature with key theorem locations
.claude/
  commands/               # Agent role prompts
  hooks/                  # Session automation
```

## Quick Commands

```bash
# Rust (from packages/rust_viterbo/)
scripts/test.sh              # All tests (debug + release)
scripts/test.sh --debug      # Debug only (with debug_assert!)
cargo clippy --workspace     # Lint
cargo fmt --all              # Format

# Python (from packages/python_viterbo/)
uv run pytest                # Run tests
uv run ruff check src tests  # Lint

# CI (from repo root)
scripts/ci.sh                # All CI checks locally
scripts/ci.sh --rust         # Rust only

# GitHub
gh issue view <N> --json title,body,labels --jq '.title, .body'
gh pr view <N>
```

## Agent Protocol

### Task Execution

1. Work in assigned directory (default: `/workspaces/msc-viterbo`)
2. Consult `docs/conventions/` for workflows
3. Ensure tests pass before completing
4. Commit with "fixes #X" if applicable

### Escalation

Escalate to Jörn when:
- Task is ambiguous or contradictory
- Out-of-scope decisions needed
- Required context unavailable
- Not confident to proceed

### Cleanup

- Remove misleading content (outdated docs, stale comments)
- Mark uncertainties clearly
- Update docs when discovering process gaps

## Communication

- Jörn reads only the **final message**. Put decisions/questions/summaries there.
- **Explicit approval only.** Status updates are not instructions. Partial responses are not confirmation.
- `[proposed]` markers await Jörn's review. Only Jörn removes them.
- Be direct and concrete. Avoid filler phrases.
- Don't delegate work to Jörn that you can do yourself.

## Environment

Environment is provisioned. See `docs/conventions/environments.md` for troubleshooting.

Working directory note: Use `cd /workspaces/worktrees/<task> && command` when working in task worktrees.
