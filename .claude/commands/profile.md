[proposed]

# Profiler Agent

You profile performance of CI, tests, or specific code paths and produce actionable findings.

## Assignment

$ARGUMENTS

## Working Directory

```bash
cd /workspaces/worktrees/<task>
```

## What To Profile

Common profiling targets:
- **CI performance**: Overall workflow timing, step breakdown
- **Test performance**: Individual test timing, hot spots
- **Algorithm performance**: Specific code path timing
- **Build performance**: Compilation time, cache effectiveness

## Information Gathering

### CI Timing

```bash
# List recent CI runs
gh run list --limit 10 --json status,conclusion,databaseId,displayTitle

# Get job-level timing
gh run view <run-id> --json jobs --jq '.jobs[] | "\(.name): \(.startedAt) - \(.completedAt)"'

# Get step-level details (shows individual step durations)
gh run view --job=<job-id>

# Get full logs with timestamps
gh run view --job=<job-id> --log 2>&1 | head -500

# Extract test results from logs
gh run view --job=<job-id> --log 2>&1 | grep -E "(PASSED|FAILED|finished in)"
```

### Python Test Timing

```bash
cd packages/python_viterbo

# Full timing report (all tests)
uv run pytest --durations=0 -v

# Top N slowest tests
uv run pytest --durations=20 -v

# Time a specific test file
uv run pytest tests/test_specific.py --durations=0 -v

# Collect without running (list tests)
uv run pytest --collect-only
```

### Rust Test Timing

```bash
cd packages/rust_viterbo

# Run with timing (parallel by default)
cargo test --workspace

# Single-threaded for accurate per-test timing
cargo test --workspace -- --test-threads=1

# Run specific crate
cargo test --package geom2d
cargo test --package geom4d

# Run with release optimizations (for comparison)
cargo test --release --workspace

# List tests without running
cargo test --workspace -- --list
```

### Build Timing

```bash
# Clean build timing
cargo clean && time cargo build --workspace

# Incremental build after change
touch packages/rust_viterbo/tube/src/lib.rs && time cargo build --workspace

# Check what's being rebuilt
cargo build --workspace 2>&1 | grep Compiling
```

## Known Hotspots

**Note:** Legacy crates (tube, hk2017, ffi) were deleted in the proof-first redesign (2026-02-02).
Historical hotspot data from commit 955a527 available in git history.

Current crates (geom2d, geom4d) have minimal test suites—update this section as tests are added.

### NOT Hotspots (ruled out)

| Component | Duration | Notes |
|-----------|----------|-------|
| Python lint (ruff) | <1s | Very fast |
| Rust format check | <1s | Very fast |

## Questions We Care About

When profiling, focus on:

1. **What's on the critical path?** (Jobs run in parallel; only the slowest matters)
2. **What's the actual bottleneck?** (Not assumptions - measure it)
3. **Is it the algorithm or the test structure?** (Redundant computation vs. inherent cost)
4. **Is there platform variance?** (CI vs. local can differ significantly)
5. **Is the cost justified by test value?** (Don't optimize tests that catch real bugs)

Questions we typically DON'T care about:

- Sub-second optimizations (unless they multiply)
- One-time costs that are cached (like QHull compilation)
- Parallelizable steps that aren't on the critical path

## Output Format

Write findings to `docs/notes/<topic>-profiling-findings.md` with:

1. **Timestamp and commit hash** (for reproducibility)
2. **Timing tables** (local vs CI, per-test breakdown)
3. **Root cause analysis** (why is it slow?)
4. **Recommendations** (if any, with effort/impact estimates)
5. **What's NOT the problem** (to prevent future re-investigation)

Example structure:

```markdown
# <Topic> Profiling Findings

**Timestamp**: YYYY-MM-DDTHH:MM UTC
**Commit**: `abc1234`
**CI Run**: [link]

## Timing Tables
...

## Key Observations
...

## Recommendations
...

## Conclusion
...
```

## Escalation

Ask Jörn when:
- You need to add benchmarking infrastructure
- You're considering test restructuring that changes coverage
- The hotspot is in algorithm code (not test code)
- Trade-offs between CI time and test value
