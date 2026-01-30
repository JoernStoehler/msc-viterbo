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

## If Code and Thesis Diverge

Fix thesis first, then update code to match. Thesis is source of truth; code implements what thesis specifies.
