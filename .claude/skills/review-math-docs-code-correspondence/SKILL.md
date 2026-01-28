---
name: review-math-docs-code-correspondence
description: Verifying that code correctly implements mathematical specifications from the thesis. Use when checking formula correspondence, validating numerical algorithms, or ensuring code matches thesis definitions.
---

# Math-Docs-Code Correspondence Review

**When to use:**
- Verifying Rust code implements thesis formulas correctly
- Checking code comments match implementation
- Ensuring numerical algorithms match theoretical descriptions
- Reviewing whether assumptions are documented

## Review Checklist

### 1. Formula Correspondence
- [ ] Locate formula in thesis (chapter, section, equation number)
- [ ] Locate implementation in code (file, function, line)
- [ ] Verify variable names match or are documented
- [ ] Check sign conventions match
- [ ] Verify order of operations matches

### 2. Numerical Tolerances
- [ ] Tolerance values are not just magic numbers
- [ ] Accumulated error is considered for iterative algorithms
- [ ] Edge cases near tolerance boundaries are tested

### 3. Assumptions and Preconditions
- [ ] Algorithm preconditions documented (e.g., "K must be star-shaped")
- [ ] Preconditions checked in code (`assert!` or runtime validation)
- [ ] Edge cases documented (what happens at boundaries?)

### 4. Test Coverage
- [ ] Tests verify mathematical properties (e.g., scaling laws)
- [ ] Known ground truth cases tested (e.g., cross-polytope, 24-cell)
- [ ] Edge cases have tests

## Common Pitfalls

**Sign errors:**
- Symplectic form is antisymmetric: ω(x,y) = -ω(y,x)
- Check matrix transpose conventions

**Coordinate conventions:**
- Thesis uses (q,p) split, code uses (x,y,z,w) or vice versa?
- Document mapping clearly

**Tolerance mismatches:**
- Code uses 1e-10 but thesis assumes exact arithmetic?
- Document where approximations occur

## Documentation Standards

**Mathematical derivations in code:**

Use comments for short derivations:
```rust
// Reeb vector: R(n,h) = 2·J·n / h
// where J is the standard complex structure on R⁴
// See thesis chapter 3, section 2.1
```

**For longer derivations:**

Reference thesis or separate doc:
```rust
// Trivialization formula derived in docs/trivialization-derivation.md
// See also thesis chapter 4, theorem 4.2
```

## When Code and Thesis Diverge

**If code is correct and thesis is wrong:**
1. Fix thesis first
2. Then verify code matches updated thesis

**If they're both correct but differ:**
- Document why they differ
- Example: "Thesis uses exact arithmetic, code uses floating point"

## Verification Process

1. **Read thesis section** that specifies the algorithm
2. **Read code implementation**
3. **Check correspondence** systematically (use checklist above)
4. **Run tests** to verify mathematical properties hold
5. **Document findings** (code comments or thesis updates)
