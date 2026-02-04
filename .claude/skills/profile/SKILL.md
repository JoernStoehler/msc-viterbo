---
name: profile
description: Performance profiler for CI, tests, and code paths. Produces actionable timing analysis. Use when investigating slow builds, tests, or algorithms. Invoke with /profile or ask about "performance", "slow", "timing".
---

# Profiler

You profile performance of CI, tests, or specific code paths and produce actionable findings.

## Assignment

$ARGUMENTS

## What To Profile

- **CI performance**: Overall workflow timing, step breakdown
- **Test performance**: Individual test timing, hot spots
- **Algorithm performance**: Specific code path timing
- **Build performance**: Compilation time, cache effectiveness

## Gather Information

### CI Timing

```bash
gh run list --limit 10 --json status,conclusion,databaseId,displayTitle
gh run view <run-id> --json jobs --jq '.jobs[] | "\(.name): \(.startedAt) - \(.completedAt)"'
gh run view --job=<job-id>
```

### Python Test Timing

```bash
cd experiments
uv run pytest --durations=0 -v
uv run pytest --durations=20 -v
```

### Rust Test Timing

```bash
cd crates
cargo test --workspace
cargo test --workspace -- --test-threads=1
cargo test --package geom2d
cargo test --package geom4d
```

## Questions We Care About

1. **What's on the critical path?** (only the slowest matters)
2. **What's the actual bottleneck?** (measure, don't assume)
3. **Is it the algorithm or the test structure?**
4. **Is there platform variance?** (CI vs. local)
5. **Is the cost justified by test value?**

Questions we DON'T care about:
- Sub-second optimizations (unless they multiply)
- One-time cached costs
- Parallelizable non-critical-path steps

## Output Format

Report findings directly to Jörn:

1. Timestamp and commit hash
2. Timing tables (local vs CI)
3. Root cause analysis
4. Recommendations
5. What's NOT the problem

## Escalation Rules

Ask Jörn when:
- Need benchmarking infrastructure
- Considering test restructuring
- Hotspot is in algorithm code
- Trade-offs between CI time and test value
