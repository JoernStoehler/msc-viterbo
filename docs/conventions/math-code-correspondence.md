# Math-Code Correspondence

How mathematical proofs relate to Rust code, and how to verify correspondence.

## Why This Matters

Math proofs use dependent types (values in types); Rust doesn't. Tests and asserts bridge this gap—they encode properties the type system can't express, making the code a valid implementation of the math.

## Review Checklist

Verifying code implements thesis formulas correctly:

## Checklist

- [ ] Locate formula in thesis and implementation in code
- [ ] Variable names match or mapping documented
- [ ] Sign conventions match (symplectic form is antisymmetric)
- [ ] Coordinate conventions match (thesis (q,p) vs code (x,y,z,w))
- [ ] Tolerance values documented with reasoning
- [ ] Preconditions checked in code (`assert!`)
- [ ] Tests verify mathematical properties

## Domain-Specific Pitfalls

- **Sign errors**: ω(x,y) = -ω(y,x), check matrix transposes
- **Coordinate conventions**: Document (q,p) ↔ (x,y,z,w) mapping
- **Tolerance mismatch**: Thesis assumes exact arithmetic, code uses floats

## Floating-Point Conventions

Math uses ℝ; code uses f64. These conventions make the correspondence work:

**Silent assumptions (don't check everywhere, but design to catch violations):**
- No overflow, underflow, or NaN unless documented
- Comparisons use tolerance parameters (never `==` for floats)

**Conservative branching for minimum search:**

Since we're finding minimum-action orbits, tolerance errors should be biased to:
- **Not reject the true minimum** (accept slightly out-of-bounds candidates)
- **Allow rejection of inadmissible results in a final validation step**

If conservative branching is too hard, acceptable fallbacks (in order):
1. Return "uncertain" flag indicating result may be invalid
2. Return warning that result may be wrong in either direction
3. Document the danger for API users

**Tolerance philosophy:**
- Tolerances are informed guesses for numerical error accumulation
- Document reasoning for each tolerance value
- When in doubt, be more permissive during search, validate at the end

## If Code and Thesis Diverge

Fix thesis first, then update code to match. Thesis is source of truth; code implements what thesis specifies.
