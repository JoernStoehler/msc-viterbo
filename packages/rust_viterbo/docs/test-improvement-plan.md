# Test Improvement Plan

**Goal:** Arrive at a properly tested algorithm codebase where trust claims are backed by empirical evidence.

---

## Principles

1. **If you can't implement it, write a TODO.** An `#[ignore]` test stub is better than prose in a doc file. The test runner surfaces ignored tests; nobody reads old docs.

2. **Claims require citations or tests.** "Well-known" is not a citation. "Cross-validated" means nothing without a test that runs.

3. **Don't separate design from code.** Property test strategies belong in test files as stubs, not in specification documents.

4. **Record what you don't know.** Open questions should be tracked where someone will see them.

**Current state:**
- Billiard: 1 literature-verified test (HK&O), 2 cross-checks with HK2019
- HK2019: Cross-checks only, no independent verification
- Tube: Zero successful capacity computations in tests
- Property tests: 1 scaling test (tesseract only), 1 monotonicity test (tesseract only)
- Symplectic invariance: Zero tests
- Random polytope generation: Not implemented

---

## Phase 1: Literature Verification

**Objective:** Establish which capacity values have actual literature backing.

### Tasks

1.1. **Find citation for tesseract capacity = 4.0**
- Search Haim-Kislev 2019 thesis/paper for explicit statement
- Search Rudolf 2022 for tesseract as example
- If found: record paper, theorem/proposition number, page
- If not found: mark as "algorithm agreement only, no literature citation"

1.2. **Find citation for simplex capacity = 1/(2n)**
- Haim-Kislev thesis claims this formula
- Need exact reference (theorem number, page)
- Verify our test simplex matches the normalization assumed in the formula

1.3. **Document findings in test-cases.md**
- Add "Literature" column with actual citations or "None"
- Remove unverified "well-known" claims

### Deliverable
Updated test-cases.md with honest literature status for each reference value.

---

## Phase 2: Cross-Algorithm Validation Matrix

**Objective:** Systematically check algorithm agreement on all polytopes where multiple algorithms apply.

### Tasks

2.1. **Build validation matrix**

For each test polytope, run all applicable algorithms and record results:

| Polytope | Facets | Billiard | HK2019 | Tube | Agreement? |
|----------|--------|----------|--------|------|------------|
| Tesseract | 8 | 4.0 | ? | NoValidOrbits | Billiard/HK2019 |
| Triangle×Triangle | 6 | 1.5 | ? | ? | ? |
| Square×Square | 8 | 4.0 | ? | ? | ? |
| Pentagon×Pentagon | 10 | 5.0 | timeout | ? | Billiard only |
| HK&O counterexample | 10 | 3.441 | timeout | ? | Billiard only |
| 4-Simplex | 5 | N/A (not Lagrangian) | ? | ? | ? |

2.2. **Add missing cross-checks as tests**
- For each cell marked "?", add a test that populates it
- Tests marked "timeout" should be `#[ignore]` with annotation

2.3. **Flag disagreements**
- Any disagreement > tolerance is a bug to investigate

### Deliverable
- Populated validation matrix in test-cases.md
- Test coverage for each cell

---

## Phase 3: Property Test Infrastructure

**Objective:** Build random polytope generators for property testing.

### 3.1 Random 2D Convex Polygon Generator

```rust
/// Generate a random convex polygon with n vertices.
///
/// Method:
/// 1. Sample n angles θ₁ < θ₂ < ... < θₙ uniformly in [0, 2π)
/// 2. Sample n radii rᵢ uniformly in [r_min, r_max]
/// 3. Vertices are (rᵢ cos θᵢ, rᵢ sin θᵢ)
///
/// This always produces a convex polygon (star-shaped from origin).
fn random_convex_polygon(
    rng: &mut impl Rng,
    n_vertices: usize,      // 3..=20
    r_min: f64,             // e.g., 0.5
    r_max: f64,             // e.g., 2.0
) -> Polygon2D
```

**Properties guaranteed:**
- Always convex (sorted angles from origin)
- Bounded (finite radii)
- Non-degenerate if r_min > 0 and n ≥ 3

**Parameters to vary:**
- n_vertices: 3 to ~12 (more = slower HK2019)
- r_min, r_max: controls eccentricity
- Optional: center offset (translation doesn't affect capacity)

### 3.2 Random Lagrangian Product Generator

```rust
/// Generate a random Lagrangian product K₁ × K₂ in ℝ⁴.
fn random_lagrangian_product(
    rng: &mut impl Rng,
    n1: usize,  // vertices in K₁
    n2: usize,  // vertices in K₂
) -> PolytopeHRep {
    let k1 = random_convex_polygon(rng, n1, 0.5, 2.0);
    let k2 = random_convex_polygon(rng, n2, 0.5, 2.0);
    lagrangian_product_hrep(&k1, &k2)
}
```

**Facet count:** n1 + n2 (one facet per edge of each polygon)

### 3.3 Proptest Strategy

```rust
fn lagrangian_product_strategy() -> impl Strategy<Value = PolytopeHRep> {
    (3usize..=6, 3usize..=6)  // n1, n2 vertices
        .prop_flat_map(|(n1, n2)| {
            any::<[u8; 32]>().prop_map(move |seed| {
                let mut rng = StdRng::from_seed(seed);
                random_lagrangian_product(&mut rng, n1, n2)
            })
        })
}
```

### 3.4 Random General Polytope (for HK2019)

Harder, but workable approaches:

**Option A: Random vertex convex hull**
- Sample k random points in 4D ball
- Compute convex hull (use external crate or convex_hull algorithm)
- Convert to H-rep
- Filter: reject if > 10 facets (HK2019 limit)

**Option B: Perturb known polytopes**
- Start with simplex, tesseract, cross-polytope
- Add small random perturbations to heights
- Stays bounded and non-degenerate for small ε

**Option C: Random H-rep with validity check**
- Sample random unit normals and heights
- Run convexity/boundedness check
- Reject invalid samples (may have high rejection rate)

Recommendation: Start with Option B (perturbations), add Option A later if needed.

### Deliverable
- `random_polygon.rs` module with generators
- Proptest strategies in test file
- Basic sanity tests for generators themselves

---

## Phase 4: Property Tests

**Objective:** Test mathematical properties across random polytopes.

### 4.1 Scaling Axiom: c(λK) = λ²c(K)

```rust
proptest! {
    #![proptest_config(ProptestConfig::with_cases(100))]

    #[test]
    fn scaling_axiom_billiard(
        polytope in lagrangian_product_strategy(),
        lambda in 0.3f64..3.0,
    ) {
        let c1 = billiard_capacity(&polytope)?;
        let scaled = scale_polytope(&polytope, lambda);
        let c2 = billiard_capacity(&scaled)?;

        let expected = lambda * lambda * c1;
        let rel_error = (c2 - expected).abs() / expected;
        prop_assert!(rel_error < 0.001,
            "c({λ}K) = {c2}, expected {expected}, rel_error = {rel_error}");
    }
}
```

Similar test for HK2019 (with smaller polytopes due to timeout).

### 4.2 Monotonicity: K ⊆ L ⟹ c(K) ≤ c(L)

```rust
proptest! {
    #[test]
    fn monotonicity_billiard(
        polytope in lagrangian_product_strategy(),
        expansion in 1.01f64..2.0,
    ) {
        let c_inner = billiard_capacity(&polytope)?;
        let outer = scale_polytope(&polytope, expansion);
        let c_outer = billiard_capacity(&outer)?;

        prop_assert!(c_inner <= c_outer + 1e-9,
            "c(K) = {c_inner} > c({expansion}K) = {c_outer}");
    }
}
```

### 4.3 Symplectic Invariance: c(SK) = c(K)

For block diagonal symplectic matrices S = diag(R(θ₁), R(θ₂)) where R(θ) is 2D rotation:

```rust
proptest! {
    #[test]
    fn symplectic_invariance_billiard(
        polytope in lagrangian_product_strategy(),
        theta1 in 0.0f64..TAU,
        theta2 in 0.0f64..TAU,
    ) {
        let c1 = billiard_capacity(&polytope)?;
        let rotated = apply_block_rotation(&polytope, theta1, theta2);
        let c2 = billiard_capacity(&rotated)?;

        let rel_error = (c1 - c2).abs() / c1;
        prop_assert!(rel_error < 0.001,
            "c(K) = {c1}, c(SK) = {c2}, rel_error = {rel_error}");
    }
}
```

**Note:** After block rotation, the polytope may no longer be a Lagrangian product. This tests billiard's behavior on near-Lagrangian inputs, or we restrict to rotations that preserve the product structure.

### 4.4 Cross-Algorithm Agreement

```rust
proptest! {
    #![proptest_config(ProptestConfig::with_cases(20))]  // HK2019 is slow

    #[test]
    fn billiard_hk2019_agreement(
        polytope in lagrangian_product_small_strategy(),  // ≤8 facets
    ) {
        let c_billiard = billiard_capacity(&polytope)?;
        let c_hk2019 = hk2019_capacity(&polytope)?;

        let rel_error = (c_billiard - c_hk2019).abs() / c_billiard;
        prop_assert!(rel_error < 0.01,
            "billiard = {c_billiard}, hk2019 = {c_hk2019}");
    }
}
```

### Deliverable
- Property tests in `algorithm/src/tests.rs` or separate `tests/property_tests.rs`
- CI runs with fixed seed for reproducibility
- Configurable case count (more for nightly, fewer for PR checks)

---

## Phase 5: Witness Verification

**Objective:** When an algorithm returns a witness orbit, verify it satisfies the mathematical definition.

### Checks for witness (p₁, ..., pₖ) with facet sequence (f₁, ..., fₖ):

1. **Boundary:** Each pᵢ lies on facet fᵢ: ⟨nᵢ, pᵢ⟩ = hᵢ (tolerance: 1e-10)
2. **Feasibility:** Each pᵢ satisfies all constraints: ⟨nⱼ, pᵢ⟩ ≤ hⱼ (tolerance: 1e-10)
3. **Flow direction:** Segment pᵢ → pᵢ₊₁ is proportional to Jnᵢ (Reeb velocity)
4. **Closure:** p₁ = pₖ (tolerance: 1e-10)
5. **Action consistency:** Sum of segment times equals reported action

```rust
fn verify_witness(witness: &WitnessOrbit, polytope: &PolytopeHRep) -> Result<(), String> {
    // ... checks above
}

proptest! {
    #[test]
    fn witness_valid_billiard(polytope in lagrangian_product_strategy()) {
        let result = billiard_capacity_with_witness(&polytope)?;
        verify_witness(&result.witness, &polytope)?;
    }
}
```

### Deliverable
- `verify_witness()` function
- Property test that all returned witnesses are valid

---

## Phase 6: Tube Algorithm Investigation

**Objective:** Determine whether the tube algorithm works on any polytope, or document its limitations.

### Tasks

6.1. **Characterize failure mode**
- Why does tube return NoValidOrbits on tesseract?
- Is it a bug, or expected for Lagrangian products?
- Read the algorithm spec and trace through manually

6.2. **Find candidate polytopes**
- Non-Lagrangian products with small facet count
- Cross-polytope (16-cell): 16 facets, non-Lagrangian
- Random perturbations of Lagrangian products
- Polytopes from literature with known capacity

6.3. **Test candidates**
- Run tube algorithm
- If success: add as regression test with cross-check
- If failure: document why

6.4. **Document status**
- If tube works on some polytopes: document which families
- If tube works on nothing: document this honestly and consider deprecation

### Deliverable
- Either: working tube tests with successful capacity computation
- Or: documentation that tube algorithm is non-functional with analysis of why

---

## Phase 7: Documentation Cleanup

**Objective:** Ensure documentation reflects actual verified state.

### Tasks

7.1. **test-cases.md**
- Remove "RESOLVED" historical notes
- Add "Literature" column with actual citations
- Add "Verified by" column (which tests check this)

7.2. **billiard-correctness-proof.md**
- Remove or qualify "High trust" claims
- Section 6 "Correctness Status": update to reflect actual test coverage
- Keep the mathematical proof (it's useful), but separate from empirical status

7.3. **test-spec.md**
- Mark which tests are implemented vs planned
- Remove aspirational language that sounds like current state

7.4. **algorithm-spec.md, algorithm-hk2019-spec.md**
- Add "Test status" section to each
- Link to specific tests that verify claims

### Deliverable
- Docs that accurately describe what is tested, not what we hope is true

---

## Execution Order

| Phase | Dependency | Effort | Impact |
|-------|------------|--------|--------|
| 1. Literature verification | None | Low | High (establishes ground truth) |
| 2. Cross-algorithm matrix | None | Medium | High (finds bugs) |
| 3. Property test infra | None | Medium | Enables Phase 4 |
| 4. Property tests | Phase 3 | Medium | High (systematic coverage) |
| 5. Witness verification | Phase 3 | Low | Medium |
| 6. Tube investigation | None | Medium | Determines if tube is viable |
| 7. Doc cleanup | Phases 1-6 | Low | High (honesty) |

**Suggested order:** 1 → 2 → 3 → 4 → 5 → 7, with Phase 6 in parallel.

---

## Phase 8: Add TODOs for Unknown Implementation Details

**Objective:** Ensure gaps are recorded in code, not lost in documentation.

Even if we don't know how to implement something, write a TODO comment or `#[ignore]` test stub so the next person sees it.

### Examples of TODOs to add

In `algorithm/src/tests.rs` or a new `tests/property_tests.rs`:

```rust
// TODO: Implement random convex polygon generator.
// Approach: sample sorted angles θ₁ < ... < θₙ, random radii rᵢ ∈ [0.5, 2.0],
// vertices at (rᵢ cos θᵢ, rᵢ sin θᵢ). Always convex.
// Needed for property tests below.

#[ignore = "needs random polygon generator"]
#[test]
fn scaling_property_random_lagrangian_products() {
    // TODO: Wire up proptest with:
    // - random Lagrangian product K₁ × K₂
    // - random λ ∈ [0.3, 3.0]
    // Check: c(λK) ≈ λ² c(K)
    todo!()
}

#[ignore = "needs random polygon generator"]
#[test]
fn monotonicity_property_random_lagrangian_products() {
    // TODO: Wire up proptest with:
    // - random Lagrangian product K
    // - random expansion factor α ∈ [1.01, 2.0]
    // Check: c(K) ≤ c(αK)
    todo!()
}

#[ignore = "needs random polygon generator + symplectic rotation helper"]
#[test]
fn symplectic_invariance_property_random_lagrangian_products() {
    // TODO: Wire up proptest with:
    // - random Lagrangian product K
    // - random block rotation angles θ₁, θ₂ ∈ [0, 2π)
    // Apply S = diag(R(θ₁), R(θ₂)) to all normals
    // Check: c(SK) ≈ c(K)
    //
    // Note: after rotation, K may no longer be a Lagrangian product.
    // Need to decide: test billiard on non-product? Or restrict rotations?
    todo!()
}

#[ignore = "needs literature citation"]
#[test]
fn tesseract_capacity_literature_value() {
    // TODO: Find literature citation for tesseract capacity = 4.0
    // If no citation exists, rename this test to indicate it's algorithm-agreement only.
    // Current sources checked: (none)
    // Candidate sources to check:
    // - Haim-Kislev 2019 thesis
    // - Rudolf 2022
    // - Artstein-Avidan & Ostrover papers
    todo!()
}

#[ignore = "tube algorithm never succeeds on tested polytopes"]
#[test]
fn tube_algorithm_computes_capacity_on_some_polytope() {
    // TODO: Find ANY polytope where tube algorithm returns Ok(capacity).
    // Current status: returns NoValidOrbits on all tested inputs.
    // Candidates to try:
    // - Non-Lagrangian products (cross-polytope, random perturbations)
    // - Small facet counts (5-6 facets)
    // - Polytopes from papers that use the CH2021 method
    //
    // If no polytope works, document why and consider deprecation.
    todo!()
}
```

### Why This Matters

The problem that led to the current state:
- test-spec.md described property tests in prose
- Prose got separated from code
- Nobody implemented the tests because the TODO wasn't visible in the test file
- Documentation claimed "strategies defined" when nothing was wired up

**Rule:** If you can't implement it now, add an `#[ignore]` test with a comment explaining what's needed. The test runner will remind everyone it exists.

### Deliverable
- Ignored test stubs for every known gap
- Each stub explains what's needed and why it's blocked

---

## Success Criteria

The codebase is "properly tested" when:

1. **Every claimed capacity value** has either:
   - A literature citation, or
   - Agreement between two independent algorithms

2. **Property tests pass** with n ≥ 100 random polytopes for:
   - Scaling axiom
   - Monotonicity axiom
   - Cross-algorithm agreement (where applicable)

3. **Witness verification passes** for all returned witnesses

4. **Documentation accurately describes** what is verified, with no misleading "trust" claims

5. **Tube algorithm status** is resolved: either working tests exist, or it's marked as non-functional

---

## Open Questions (I Don't Know the Answer)

These are recorded so someone with more context can address them:

1. **Is tesseract capacity = 4.0 in the literature?**
   - I couldn't find a direct citation in my search
   - Haim-Kislev 2019 might have it; I don't have access to verify
   - Someone should check the actual papers

2. **Why does tube algorithm always return NoValidOrbits?**
   - Is this expected for Lagrangian products?
   - Is there a bug in rotation computation?
   - Are there polytopes in the literature where CH2021-style tube search is known to work?

3. **What's the right tolerance for cross-algorithm agreement?**
   - Currently using 1% relative error
   - Is this justified by numerical analysis, or arbitrary?
   - Should different polytope families have different tolerances?

4. **Does symplectic invariance test make sense for billiard?**
   - After block rotation, a Lagrangian product may not be Lagrangian
   - Does billiard algorithm handle near-Lagrangian inputs?
   - Or should we only test rotations that preserve product structure?

5. **Are there standard benchmark polytopes in the symplectic capacity literature?**
   - Like MNIST for ML - known polytopes everyone uses
   - Would help establish what "correct" means

6. **What's the relationship between HK2019 QP and billiard LP?**
   - They agree on tested cases, but are they mathematically equivalent for Lagrangian products?
   - If so, one could validate the other by proof, not just empirical agreement

7. **Is proptest the right framework?**
   - Rust ecosystem has proptest and quickcheck
   - Are there gotchas for floating-point property testing?
   - How to handle tests that occasionally fail due to numerical edge cases?

If you know the answer to any of these, please update this document or add a test.
