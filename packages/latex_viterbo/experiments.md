# Experiments Tracking

Quick-scan table for all research questions and experiments. See `.claude/skills/experiment-workflow/` for the full workflow.

**Status values:** Ideation | Specified | In progress | Executed | Polished | Abandoned | Failed | Superseded

| Label | Status | Research Question | Notes |
|-------|--------|-------------------|-------|
| billiard-hko-orbit | Ideation (blocked) | Compute EHZ capacity for HK-O 2024 counterexample using billiard algorithm; verify systolic ratio ≈ 1.0472; visualize minimum-action orbit | Blocker: no trusted billiard algorithm yet. See details below. |

## billiard-hko-orbit

**Purpose:** Validation experiment. HK2024 provides ground truth, so discrepancies indicate algorithm bugs.

**Ground truth (HK2024 + thesis data):**
- Systolic ratio: exactly (√5+3)/5 ≈ 1.0472135955
- Capacity: 2cos(π/10)(1+cos(π/5)) ≈ 3.4410
- Orbit type: "2-bounce" — 2 bounces per projection (q and p), so ~4 segments total

**Orbit structure:**
- Polytope is P₅ ×_L R(-90°) P₅ (Lagrangian product of pentagons)
- Each segment: one component (q or p) moves along polygon boundary, other is constant
- Alternates: q-move → p-move → q-move → p-move
- Visualization: side-by-side projections onto q-plane and p-plane, labeled segment numbers
- Infinite family of minimum-action orbits exists; we plot whichever the algorithm returns

**Success criteria:**
- Systolic ratio within 0.1% of ground truth
- Orbit visualization shows 2-bounce pattern in each projection
- Visual inspection confirms orbit shape

**Outcomes:**
- ✓ Yes: reproduces correctly, looks right
- ✗ No: discrepancy → algorithm bug to investigate
- ? Maybe: looks good but need more validation angles

[proposed]
