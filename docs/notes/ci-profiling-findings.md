# CI Performance Profiling Findings

Investigation for issue #98: Profile CI performance after PR#90 (QHull integration).

## Summary

Current CI runtime is ~2 minutes, driven by two parallel jobs:
- **Rust job**: 1m29s
- **FFI job**: 1m53s (critical path)

**Key finding**: QHull compilation is NOT the bottleneck. The HK2017 capacity algorithm (O(n!)) running in both Rust and Python tests is the primary contributor.

## Detailed Timing Analysis

### CI Run 21562389530 Step-by-Step

**Rust Job (1m29s total)**
| Step | Duration | Notes |
|------|----------|-------|
| Cache cargo | 5s | Cache hit |
| Clippy | 9s | Linting |
| Test (debug) | 60s | Main bottleneck |
| Test (release) | 8s | Fast with optimizations |

**FFI Job (1m53s total)**
| Step | Duration | Notes |
|------|----------|-------|
| Install dependencies | 10s | uv sync, etc. |
| Pyright | 6s | Type checking |
| maturin develop | 10s | Includes QHull compilation |
| pytest | 77s | Main bottleneck |

### Debug Test Breakdown (Rust)

| Test Suite | Duration | Description |
|------------|----------|-------------|
| tube (69 tests) | 21s | Tube algorithm unit tests |
| hk2017 doc-tests | 12s | HK2017 doctests run algorithm |
| hk2017 (44+9 tests) | 8s | Unit tests |
| flow_map_tests | 4s | Flow map integration |
| hk2017_comparison | 4s | Cross-algorithm comparison |
| orbit_invariants | 4s | Invariant checks |

### Python Test Breakdown

| Test Category | Duration | Description |
|---------------|----------|-------------|
| test_hk2017_* (3 tests) | 34s | Each runs HK2017 via FFI |
| test_polytope_database capacity (6 tests) | 48s | Each runs full capacity pipeline |
| Other tests | 3s | Fast unit tests |

## Root Cause Analysis

### 1. HK2017 Algorithm Complexity

The HK2017 algorithm has O(n!) complexity where n = number of facets:
- 8 facets → 40,320 permutations
- Each Python `test_hk2017_*` test runs this algorithm once
- The `test_polytope_database::TestStageCapacity` tests run it multiple times

### 2. Redundant Capacity Computations

The polytope_database tests share fixture data but recompute capacities:
```
test_adds_capacity_fields     → runs add_capacities(polytopes)
test_systolic_ratio_formula   → runs add_capacities(polytopes) again
test_tesseract_capacity       → runs add_capacities(polytopes) again
test_pipeline_produces_complete_data → runs add_capacities(polytopes) again
test_json_serializable        → runs add_capacities(polytopes) again
test_orbit_invariants         → runs add_capacities(polytopes) again
```

Each call to `add_capacities()` computes capacity for 12 polytopes.

### 3. QHull is NOT the Bottleneck

- QHull compilation: 10s (one-time, during maturin develop)
- Volume tests: <0.2s total
- Already cached between runs

### 4. Platform-Dependent Performance Variance

The `test_hk2017_vs_tube_random_8_facet` test shows significant variance:
- CI: 4s
- Local (dev container): 116s

This appears related to random polytope generation success rates, not the algorithm itself.

## Recommendations

### Quick Wins (Low effort, immediate impact)

#### 1. Cache capacity results in Python tests
**Impact**: ~40s reduction in pytest (48s → 8s)

```python
# In conftest.py or test_polytope_database.py
@pytest.fixture(scope="module")
def polytopes_with_capacity():
    polytopes = generate_polytopes()
    polytopes = add_volumes(polytopes)
    polytopes = add_capacities(polytopes)
    return polytopes
```

#### 2. Run pytest in parallel
**Impact**: ~30s reduction (77s → ~45s)

```yaml
# In ci.yml
- name: Run tests
  run: uv run pytest -v -n auto  # Requires pytest-xdist
```

Add to pyproject.toml:
```toml
[project.optional-dependencies]
dev = ["pytest-xdist", ...]
```

### Medium Effort

#### 3. Mark expensive Rust comparison tests as ignored in debug mode
**Impact**: Reduces debug test variance

The `test_hk2017_vs_tube_random_8_facet` test has high variance. Consider:
```rust
#[test]
#[cfg_attr(debug_assertions, ignore)]
fn test_hk2017_vs_tube_random_8_facet() { ... }
```

#### 4. Reduce HK2017 FFI test iterations
**Impact**: ~20s reduction

The `test_hk2017_graph_pruning` test runs HK2017 twice. Could combine with `test_hk2017_tesseract_capacity`.

### Architectural Changes (Higher effort)

#### 5. Shared artifact caching between jobs

Currently, both `rust` and `ffi` jobs compile the Rust workspace independently. Could use GitHub Actions artifacts to share compiled FFI:

```yaml
ffi:
  needs: rust  # Wait for rust job
  steps:
    - uses: actions/download-artifact@v4
      with:
        name: rust-target
```

This would eliminate the 10s maturin develop in the FFI job but adds complexity.

## Acceptance Criteria Met

- [x] Identified bottlenecks: HK2017 algorithm in tests (not QHull)
- [x] Measured baseline timing: ~2min CI, breakdown per step
- [x] Recommendations provided with impact estimates

## Not Recommended

- **Test parallelism with --test-threads=N for Rust**: Already parallel by default
- **Skipping release tests**: These catch real bugs (debug_assertions-gated tests)
- **Reducing test coverage**: Tests are valuable for correctness

## Expected Impact

If recommendations 1+2 are implemented:
- Current FFI job: 1m53s
- Expected: ~1m10s (40s from caching + 30s from parallelism, with overlap)

This would bring total CI time to ~1m30s (Rust job becomes critical path).
