# CI Speedup Analysis

**Issue**: #141
**Date**: 2026-02-01
**Recommendation**: Close #98 and #109 as wontfix

## Executive Summary

CI time of ~2 minutes is acceptable for this thesis project. Further optimization would add complexity for minimal benefit. The low-hanging fruit (test restructuring) was already harvested in PR#149.

## Current Metrics

| Metric | Value |
|--------|-------|
| Wall clock time | ~2 min |
| Rust job | 1m57s |
| FFI job | 1m10s (parallel) |
| Developer wait | 2 min per push |
| Cost | Free (GitHub Actions public repo) |

## Options Evaluated

### 1. pytest-xdist (parallel Python tests)

**Status**: Already evaluated in [ci-profiling-findings.md](ci-profiling-findings.md), not recommended.

- Tests already ~40s after restructuring
- Slow parts are sequential HK2017 computations
- Would complicate debugging (multi-process, interleaved output)
- Limited benefit: module-scoped fixtures run sequentially anyway

### 2. sccache / Build Caching Improvements

**Potential savings**: 10-30s on cache miss

**Complexity cost**:
- External dependency (sccache)
- Cache invalidation debugging
- GHA cache size limits

**Assessment**: Not worth it. Current cargo cache already works well with fallback keys.

### 3. Selective Test Runs (Only Changed Crates)

**Potential savings**: Variable (0-60s depending on what changed)

**Complexity cost**:
- Path filtering logic in CI
- Risk of missing cross-crate issues
- Harder to reason about what ran

**Assessment**: Error-prone for marginal benefit. Full test runs are cheap at 2 minutes.

### 4. Job Splitting (More Parallelism)

**Potential savings**: Maybe 20-30s

**Complexity cost**:
- More jobs to maintain
- Increased setup overhead per job
- More complex failure diagnosis

**Assessment**: Jobs already run in parallel. Splitting further adds overhead that may offset savings.

### 5. Pre-built Dependencies

**Status**: Not applicable. Rust compilation dominates, but `cargo cache` action already handles this well.

## Thesis Project Impact Analysis

### Developer Experience

- 2 min wait is not painful for a single-developer thesis project
- Fast enough to stay in flow (grab coffee, check phone, switch context briefly)
- Not slow enough to context-switch to another task

### Development Velocity

With ~20 commits in recent history and ~2 min CI per push:
- Total CI wait per day: ~10-20 minutes (assuming 5-10 pushes)
- This is negligible compared to time spent writing/thinking/debugging

### Opportunity Cost

Time spent on CI optimization is time not spent on:
- Thesis content
- Algorithm implementation
- Experiment design
- Paper writing

For a thesis project with a fixed deadline (March 2026), thesis content has far higher priority than shaving 30 seconds off CI.

## Recommendation

**Close #98 and #109 as wontfix** with the following rationale:

1. **Current CI time is acceptable**: 2 minutes is not a bottleneck for thesis progress
2. **Low-hanging fruit already picked**: Test restructuring in PR#149 saved ~40s
3. **Further optimization has poor ROI**: Complexity cost exceeds time savings
4. **Thesis deadline context**: Developer time is better spent on thesis content

## When to Reconsider

Reopen this analysis if:
- CI time exceeds 5 minutes
- Test suite doubles in size
- Multiple collaborators join the project
- CI costs become non-trivial

## Closing Notes for Issues

### For #98 (Profile CI performance after PR#90)
Profiling complete. Findings documented in `docs/notes/ci-profiling-findings.md`. Test restructuring implemented in PR#149, saving ~40s. No further action needed.

### For #109 (Optimize CI time when suite grows)
Analysis complete. Current ~2 min CI is acceptable for thesis scope. Further optimization not cost-effective. Will reconsider if CI time exceeds 5 minutes or thesis requirements change.
