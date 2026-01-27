# Test Documentation

> **⚠️ ARCHIVED** — This document describes tests from the v0.1.0 implementation which was deleted.
> Current tests are in each crate's source files. Run `cargo test --workspace` to see current tests.

**Purpose:** Consolidated reference for all testing in the rust_viterbo crate.

For mathematical claims and their verification status, see `mathematical-claims.md`.

---

## 1. Test Organization

Tests are organized by **topic** in `algorithm/src/tests/`:

| File | Topic | Tests |
|------|-------|-------|
| `capacity_known_values.rs` | Literature-verifiable capacity values | Tesseract=4, rectangle |
| `capacity_scaling_axiom.rs` | c(lambda K) = lambda^2 c(K) | Proptests |
| `capacity_monotonicity.rs` | K subset L implies c(K) <= c(L) | Proptests |
| `capacity_symplectomorphism.rs` | c(AK) = c(K) for A in Sp(4) | Block rotations |
| `algorithm_agreement.rs` | Billiard vs HK2019 cross-validation | Proptests |
| `algorithm_metadata.rs` | Algorithm traits, input validation | |
| `billiard_witness.rs` | Witness orbit geometry | Breakpoints, facets |
| `lagrangian_product.rs` | Product detection/structure | |
| `polygon_2d.rs` | 2D polygon operations | |
| `tube_algorithm.rs` | Tube (CH2021) algorithm | |
| `polytope_preprocessing.rs` | PolytopeData construction | |
| `fixtures.rs` | Test polytopes, random generation | |

Plus unit tests in each module file (`billiard.rs`, `tube.rs`, `polygon.rs`, etc.)

---

## 2. Test Status Summary

As of 2026-01-20:
- **Total tests:** 186+ (153 algorithm + 33 geom + optim)
- **Ignored:** 13 (documented known issues)

### Ignored Tests

| Test | Reason | Category |
|------|--------|----------|
| `pentagon_counterexample_capacity` | BUG: returns 2.127, expected 3.441 | Pentagon |
| `pentagon_systolic_ratio_exceeds_one` | Depends on pentagon capacity | Pentagon |
| `witness_satisfies_reeb_flow` | max_flow_error approx 2.36 | Witness |
| `witness_action_matches_capacity` | segment_times not implemented | Witness |
| `billiard_witness_positive_segment_times` | segment_times not implemented | Witness |
| `billiard_witness_closes` | closure won't be exact | Witness |
| `tesseract_hk2019_capacity` | 8! = 40320 permutations too slow | HK2019 |
| `invariance_*_hk2019` (3 tests) | HK2019 too slow | HK2019 |
| `scaling_all_algorithms` | needs valid capacities | Scaling |
| `scaling_compute_capacity` | needs valid capacities | Scaling |
| `invariance_shear` | breaks Lagrangian product | Symplectic |

---

## 3. Test Polytopes (Fixtures)

### 3.1 Tesseract [-1,1]^4

```rust
fn tesseract() -> PolytopeHRep {
    // 8 facets: +-x_i for i=1,2,3,4
    // Capacity = 4.0 (verified)
    // Lagrangian product: [-1,1]^2 x [-1,1]^2
}
```

**Properties:**
- 8 facets, 20 Lagrangian 2-faces, 8 non-Lagrangian 2-faces
- Algorithms: Billiard works, HK2019 works, Tube fails (has Lagrangian 2-faces)

---

### 3.2 Equilateral Triangle x Triangle

```rust
fn triangle_times_triangle() -> PolytopeHRep {
    // 6 facets (3 q-facets, 3 p-facets)
    // Capacity = 1.5 (verified)
    // Circumradius = 1
}
```

**Critical:** Optimal is at t=1/3, NOT edge midpoints (t=0.5).

---

### 3.3 Pentagon x Rotated Pentagon (HK-O Counterexample)

```rust
fn pentagon_counterexample() -> PolytopeHRep {
    // 10 facets (5 q-facets, 5 p-facets)
    // Expected capacity = 3.441
    // KNOWN BUG: returns 2.127 = expected/phi
}
```

**Data:** `packages/python_viterbo/data/counterexamples/hk-o-2024/`

---

### 3.4 Random Lagrangian Products

```rust
fn random_lagrangian_product(rng, n1, n2) -> PolytopeHRep
```

Used for property testing. See `fixtures.rs`.

---

## 4. Test Properties

### 4.1 Capacity Axioms

**Scaling:** c(lambda K) = lambda^2 c(K)
- Tested with lambda in [0.3, 3.0]
- `capacity_scaling_axiom.rs`

**Monotonicity:** K subset L implies c(K) <= c(L)
- Tested by expanding heights
- `capacity_monotonicity.rs`

**Symplectomorphism Invariance:** c(AK) = c(K) for A in Sp(4)
- Tested for block rotations R(theta) + R(phi)
- `capacity_symplectomorphism.rs`
- [INCOMPLETE] Full Sp(4) not covered

---

### 4.2 Algorithm Agreement

For Lagrangian products, Billiard and HK2019 should agree:
```
|c_billiard - c_HK2019| / c_billiard < 0.01
```

Tested via proptest with random Lagrangian products.

---

### 4.3 Witness Verification

For each returned witness orbit, verify:

| Check | Condition | Status |
|-------|-----------|--------|
| Breakpoints on boundary | <n_i, p> = h_i | Tested |
| Breakpoints feasible | <n_j, p> <= h_j for all j | Tested |
| Facet transitions valid | Adjacent facets share 2-face | Tested |
| Reeb flow direction | velocity proportional to Jn | **INCOMPLETE** |
| Orbit closes | first = last breakpoint | **INCOMPLETE** |
| Action matches | sum(times) = capacity | **NOT IMPLEMENTED** |

---

## 5. Running Tests

```bash
# All tests
cargo test -p rust_viterbo_algorithm

# Including ignored (slow/broken)
cargo test -p rust_viterbo_algorithm -- --ignored

# Specific test file
cargo test -p rust_viterbo_algorithm capacity_scaling

# With output
cargo test -p rust_viterbo_algorithm -- --nocapture
```

---

## 6. Algorithm Limits

| Algorithm | Max Facets | Notes |
|-----------|------------|-------|
| HK2019 | 8 practical, 10 max | O(F!) complexity, 60s timeout |
| Billiard | unlimited | O(n^3) for Lagrangian products only |
| Tube | N/A | Often fails (no valid orbits found) |

---

## 7. Known Issues

### 7.1 HK2019 QP Solver (INCOMPLETE)

The QP solver uses vertex + edge enumeration, which is incomplete for indefinite quadratics. Maximum can be on 2D+ faces.

**Status:** Tests pass by luck. Blocked on `optim` crate.

### 7.2 Witness Segment Times (NOT IMPLEMENTED)

The `segment_times` field is placeholder zeros. Capacity is correct but witness times are missing.

**Status:** Previous bogus formulas removed. Need to derive from Reeb flow equations.

### 7.3 Pentagon Capacity Bug

Billiard returns 2.127 instead of 3.441 (= expected/phi).

**Status:** Under investigation. See `next-actions.md`.

### 7.4 Tube Algorithm

Returns `NoValidOrbits` for all tested polytopes including non-Lagrangian ones.

**Status:** May be working correctly (these polytopes may not have short orbits of required type). Needs more investigation.

---

## 8. Adding New Tests

1. **Find the right file:** Tests organized by topic, not mechanism
2. **Add fixture if needed:** Put reusable polytopes in `fixtures.rs`
3. **Document expected values:** Add to `test-cases.md` with citations
4. **Mark blocked tests:** Use `#[ignore = "reason"]` with clear explanation

### Template for Ignored Test

```rust
#[ignore = "pentagon capacity bug: returns 2.127, expected 3.441"]
#[test]
fn pentagon_counterexample_capacity() {
    // Bug description:
    // - Expected: 3.441 (HK-O 2024 Proposition 1)
    // - Actual: 2.127 = expected/phi
    // - Investigation: see next-actions.md
    todo!("fix pentagon capacity bug first")
}
```

---

## 9. Cross-References

- **Mathematical claims:** `mathematical-claims.md`
- **Test case catalog:** `test-cases.md`
- **Current status:** `code-audit-tracker.md`
- **Archived working notes:** `archive/test-improvement-plan.md`
