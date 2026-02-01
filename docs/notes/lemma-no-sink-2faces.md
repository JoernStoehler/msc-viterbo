# Lemma: No Sink 2-Faces (Unproven)

**Status:** UNPROVEN CONJECTURE - claimed by Jörn, no proof written yet

**Statement:**

For any convex polytope K ⊂ ℝ⁴ without Lagrangian 2-faces, every 2-face has at least one outgoing transition to another 2-face.

Equivalently: There are no "sink 2-faces" (2-faces with zero outgoing transitions) in non-Lagrangian polytopes.

**Implication for code:**

If this lemma is true, then the existence of sink 2-faces in our preprocessing output indicates a BUG in the code, not a geometric property to filter out.

**Evidence of bug (seed 2661):**

The following 2-faces have no outgoing transitions:
- 2-face 1: entry=0, exit=3, omega=0.8145
- 2-face 3: entry=0, exit=5, omega=0.0978
- 2-face 8: entry=1, exit=5, omega=0.4657
- 2-face 11: entry=2, exit=5, omega=0.4507
- 2-face 13: entry=6, exit=3, omega=0.7058
- 2-face 14: entry=7, exit=3, omega=0.0109
- 2-face 16: entry=7, exit=5, omega=0.1469

All have omega > EPS_LAGRANGIAN, so they're non-Lagrangian. If the lemma is true, these sink 2-faces should not exist, indicating a bug in:
1. 2-face enumeration
2. Flow direction computation
3. Transition building
4. Lagrangian detection

**Date:** 2026-02-01
