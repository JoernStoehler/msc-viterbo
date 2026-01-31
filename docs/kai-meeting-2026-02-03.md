# MSc Thesis Progress Report
**Meeting with Kai Zehmisch — February 3, 2026**

Jörn Stöhler, University of Augsburg

---

## Executive Summary

**Topic:** Computational investigation of Viterbo's Conjecture boundary cases after HK-O 2024 counterexample.

**Timeline:** On track for March 2026 submission, with ~8 weeks remaining.

**Current Phase:** Algorithm toolbox complete, entering systematic experimentation phase.

---

## 1. Project Overview

### 1.1 Research Question

Viterbo's Conjecture (systolic ratio $\leq 1$ for convex bodies) was disproved by Haim-Kislev & Ostrover (2024) with a 10-facet Lagrangian product polytope achieving sys $\approx 1.047$.

**This thesis asks:** What is the true boundary? Can we discover refined conjectures through systematic computational exploration?

### 1.2 Approach

1. **Implement capacity algorithms** — compute $c_{EHZ}(K)$ for polytopes in $\mathbb{R}^4$
2. **Build polytope dataset** — systematic families + random sampling
3. **Run experiments** — characterize where counterexamples occur
4. **Formulate conjectures** — based on computational evidence

---

## 2. Completed Work

### 2.1 Algorithm Implementation (Rust)

| Algorithm | Status | Complexity | Applicability |
|-----------|--------|------------|---------------|
| **HK2017** | Complete, tested | $O(F!)$ | Any polytope, $F \leq 10$ facets |
| **Tube** | Complete, tested | $O(\text{tubes})$ | Polytopes without Lagrangian 2-faces |
| **Billiard** | Design complete, impl pending | $O(E^6)$ | Lagrangian products only |

**Test coverage:** 191 Rust tests, all passing.

**Validation:** Cross-algorithm agreement verified on applicable polytopes:
- Unit tesseract: $c = 4.0$ (HK2017)
- Unit cross-polytope: $c = 1.0$ (Tube)
- Unit 24-cell: $c = 2.0$ (Tube, self-dual)
- 4-simplex: $c \approx 0.417$ (HK2017)

### 2.2 Completed Experiments

| Experiment | Key Finding |
|------------|-------------|
| **benchmark_hk2017** | Runtime $\approx 1 \mu s$/permutation, linear scaling ($R^2 > 0.99$) |
| **algorithm_inventory** | Mahler bound exactly saturated by tesseract/cross-polytope dual pair |
| **runtime_performance_analysis** | Tube algorithm hotspots identified (40-45% in core loop) |

### 2.3 Thesis Writing

| Chapter | Lines | Status |
|---------|-------|--------|
| math.tex | 483 | Core definitions complete |
| algorithms.tex | 652 | Tube needs polish; HK2017 + Billiard simpler but missing; Clarke proof not yet migrated; figures need digital redraw |
| counterexample.tex | 67 | Stub |
| experiments.tex | 29 | Stub |
| conjectures.tex | 9 | Stub |
| intro.tex | 14 | Stub (can draft early) |

**Also completed:** Clarke duality talk (given, proof to be migrated).

---

## 3. Current Blockers

### 3.1 Critical Path

```
#92 Billiard thesis section (has design notes, needs formal writeup)
  ↓ blocks
#93 Billiard test suite
#94 Triangle×triangle discrepancy debug (billiard=3.0 vs hk2017=1.5)
  ↓ blocks
#112 Algorithm performance comparison
  ↓ blocks
#113-115 ML capacity prediction experiments
```

**Unblocking #92** is the single highest-leverage task.

### 3.2 Unblocked Experiments (ready to run)

| Issue | Experiment | Description |
|-------|------------|-------------|
| #96 | algorithm-comparison | HK2017 vs Tube on non-Lagrangian polytopes |
| #100 | billiard-hko-orbit | Validate HK-O pentagon counterexample |
| #101 | random-polytope-sys | How rare are counterexamples? |
| #102 | lagrangian-product-polygons | Regular polygon products study |
| #105 | dataset-dimension-reduction | PCA/UMAP on polytope features |
| #106 | sys-ratio-optimization | Gradient flow toward maximum sys |

---

## 4. Roadmap

### 4.1 Milestones

| Milestone | Target | Status |
|-----------|--------|--------|
| **M4: Algorithm Toolbox** | — | 5/11 issues closed |
| **M6: Dataset Characterized** | — | 1/5 issues closed |
| **M8: Thesis Submission** | End of March | 3/5 issues closed |

### 4.2 Remaining Work (Point Estimates)

<!-- [JÖRN: Please review/adjust point estimates. Scale: 1pt ≈ 1 focused hour of your attention] -->

| Task | Points | Blocked By |
|------|--------|------------|
| #92 Billiard section writeup | 3 | — |
| #93 Billiard test suite | 2 | #92 |
| #94 Triangle×triangle debug | 2 | #92, #93 |
| #96 Algorithm comparison | 3 | — |
| #100 HKO orbit validation | 2 | — |
| #101 Random polytope sys distribution | 5 | — |
| #102 Lagrangian product polygons | 4 | — |
| #126 Appendix detailed experiments | 3 | experiments done |
| Thesis chapters (counter, exp, conj) | 8 | experiments done |
| Final editing + submission | 5 | all above |
| **Total remaining** | **~37 pts** | |

### 4.3 Velocity

**Project timeline:** Thesis started ~Oct 14, 2025. Repo created Nov 17, 2025.

| Week | Dates | Commits | Phase |
|------|-------|---------|-------|
| W46-W48 | Nov 10 - Dec 1 | 63 | Initial setup, early experiments |
| W49-W52 | Dec 1 - Dec 28 | 73 | Algorithm development |
| W02-W04 | Jan 5 - Jan 25 | 60 | Steady progress |
| **W05** | **Jan 26 - Jan 31** | **264** | **Agent-driven sprint** |
| **Total** | | **460** | |

**W05 breakdown (agent sprint):**

| Day | Commits |
|-----|---------|
| Sun Jan 26 | 60 |
| Mon Jan 27 | 63 |
| Tue Jan 28 | 62 |
| Wed Jan 29 | 16 |
| Thu Jan 30 | 32 |
| Fri Jan 31 | 31 |

**Observations:**
- W05 had more commits than all previous weeks combined (264 vs 196)
- Agent parallelism dramatically increased throughput
- Bottleneck shifted from coding to Jörn's review/direction capacity

<!-- [JÖRN: Estimate points completed in W05 vs earlier weeks] -->

---

## 5. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|------------|--------|------------|
| Billiard algorithm has deeper bugs | Medium | High | Design notes are thorough; test against HK2017 |
| Experiments yield no new conjectures | Low | Medium | Negative results are still publishable |
| Time overrun on thesis writing | Medium | Medium | Chapters are scaffolded; experiments generate content |

---

## 6. Confidence in Correctness

### 6.1 Sources of Trust

1. **Known values:** Tesseract, cross-polytope, 24-cell match literature (mathematically derived, not empirical)
2. **Mathematical properties verified:**
   - Scaling: $c(\lambda K) = \lambda^2 c(K)$ ✓
   - Mahler bound: $c(K) \cdot c(K^\circ) \leq 4$ ✓ (exactly saturated by tesseract/cross-polytope pair)
   - Constraint satisfaction: $\sum \beta_i h_i = 1$, $\sum \beta_i n_i = 0$ ✓

3. **Test coverage:** 191 unit tests, including regression tests for fixed bugs

### 6.2 Known Gaps (Critical)

**⚠️ Tube lacks effective cross-validation (#144):**
- The HK2017 vs Tube comparison test can pass with **0 successful comparisons**
- Capacity axioms alone don't prove we compute $c_{EHZ}$ vs some other capacity-like function
- This is the biggest correctness gap — needs fixing before experiments

**Other gaps:**
- Billiard algorithm: design only, not yet implemented/tested
- HK thesis simplices claim: not yet verified (blocked on document access)
- Large polytopes ($F > 10$): only Tube applicable, no cross-check

---

## 7. Wasteful Efforts Summary

<!-- [JÖRN: Adjust percentages based on actual experience] -->

**Infrastructure overhead (Week 1):**
- Claude Code web crash debugging: ~X hours
- CI/environment setup: ~Y hours
- Total: ~Z% of available time

**Lesson:** Local development environment is more stable than CC web.

---

## 8. Questions for Discussion

1. Is the experiment roadmap appropriately scoped for March deadline?
2. Should billiard algorithm be prioritized, or focus on HK2017/Tube experiments only?
3. Are there specific polytope families Kai recommends investigating?

---

## 9. Experiment Prioritization

**Discussion point for Kai:** Jörn can estimate implementation effort, but Kai may have better intuition for mathematical interestingness. The table below shows Jörn's effort/utility estimates — Kai's input on "expected mathematical value" could adjust priorities.

### Priority Assessment

| Issue | Experiment | Utility | Effort | Notes |
|-------|------------|---------|--------|-------|
| #96 | algorithm-comparison | High | Mid | Cross-validates HK2017 vs Tube |
| #100 | billiard-hko-orbit | High | Mid | Validates HK-O counterexample + non-Lagrangian perturbation for Tube |
| #101 | random-polytope-sys-distribution | **High** | Mid | **Critical:** "How rare are counterexamples?" — informs all downstream experiments |
| #102 | lagrangian-product-polygons | Mid | Low | Systematic study of counterexample family |
| #105 | dataset-dimension-reduction | Low | Low | PCA/UMAP exploration |
| #106 | sys-ratio-optimization | Low | Mid | Gradient flow to max sys |
| #110 | lagrangian-product-random-polygons | Mid | Low | Same as #102 but random polygons (code reuse) |
| #111 | fixed-facet-vertex-count | High | Mid | Verify HK's simplex claim (sys ≤ 3/4 for 5-facet) |
| #112 | algorithm-performance-comparison | High | Mid | Blocked on billiard impl |
| #113 | algorithm-optimization-ablation | Low | High | Performance tuning |
| #114/#115 | ML capacity prediction | Low | High | Similar experiments (merge?); blocked on dataset |

### Recommended Order

1. **#101** (critical path: informs ML experiments, gives "fraction of counterexamples" result)
2. **#100** (validates the key counterexample)
3. **#96** (cross-validation builds confidence)
4. **#102** → **#110** (code reuse, systematic exploration)
5. **#111** (verify HK simplex claim)
6. Rest as time permits

---

## 10. Full Experiment Inventory

**Completed (with FINDINGS.md):**
| Experiment | Description |
|------------|-------------|
| benchmark_hk2017 | Runtime scaling analysis |
| algorithm_inventory | Survey existing approaches (not yet reviewed by Jörn) |
| runtime_performance_analysis | Profile Tube hotspots (not yet reviewed by Jörn) |

**Open experiments:** See prioritization table above (§9).

**Note:** This list is not exhaustive. More experiments will be designed after initial results reveal the Viterbo landscape.

---

## Appendix: Print Thesis Chapters

For detailed algorithm specifications, print:
- `packages/latex_viterbo/chapters/algorithms.tex` (Tube algorithm)
- `packages/latex_viterbo/chapters/math.tex` (definitions)

For experiment results, print:
- `packages/python_viterbo/src/viterbo/experiments/*/FINDINGS.md`
