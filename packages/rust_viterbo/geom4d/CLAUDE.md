# geom4d

4D convex geometry primitives for symplectic capacity algorithms.

## Design Philosophy

This crate provides **validated types** that enforce mathematical invariants at construction time. Invalid input is rejected with specific errors, not silently accepted.

### Priorities (in order)

1. **Correctness**: Code must implement the mathematical specification exactly
2. **Clarity**: Code should be readable and its correctness should be verifiable
3. **Testability**: Invariants should be checkable via tests and `debug_assert!`
4. **Strictness**: Reject invalid input early; don't accept data that violates constraints

### No Premature Optimization

- Do NOT add fast paths, heuristics, or special cases unless profiling shows they're needed
- Do NOT sacrifice clarity for performance
- One correct algorithm is better than a correct algorithm plus a "fast path" that might have bugs
- If an algorithm is O(n²) but correct and clear, that's fine for n < 1000

### Type Construction

Each struct follows this pattern:

- **`Type::new(data) -> Result<Type, TypeError>`**: Validates all invariants. Use this in production code.
- **`Type::new_unchecked(data) -> Type`**: Skips validation but has `debug_assert!` checks. Use only in tests with known-good data.

### Coordinate Validity

All coordinates must be:
- Finite (rejects NaN and Infinity)
- Within `[-MAX_COORD, MAX_COORD]` (prevents overflow in arithmetic)

This catches common bugs like uninitialized values or arithmetic overflow before they propagate.

## File Size

Files must stay under 300 lines. Split into multiple files when needed. Multiple test files for one code file are fine (e.g., `foo.rs`, `foo_tests.rs`, `foo_edge_cases_tests.rs`).

## Module Organization

| Module | Purpose |
|--------|---------|
| `tolerances.rs` | Numerical tolerance constants (see doc comments for rationale) |
| `hrep.rs` | `HRep` struct: H-representation with unit normals and positive heights |
| `bounded.rs` | Boundedness check via positive span (LP-based) |

## Tolerance Constants

All tolerances live in `tolerances.rs` with documented rationale:

```rust
pub const EPS: f64 = 1e-10;       // General floating-point comparison
pub const EPS_UNIT: f64 = 1e-9;   // Unit vector validation (‖n‖ ≈ 1)
pub const EPS_HEIGHT: f64 = 1e-12; // Height positivity check
pub const MAX_COORD: f64 = 1e15;  // Coordinate magnitude limit
```

When checking `value > 0`, use `value > EPS_*` (not `>= EPS_*`) so that values exactly at the tolerance are rejected as ambiguous.

## Testing Conventions

### Required Test Categories

1. **Positive tests**: Valid inputs are accepted
2. **Negative tests**: Each error variant has a test that triggers it
3. **Edge cases**: Boundary conditions, near-tolerance values, counterexamples for naive algorithms

### Test Naming

```rust
#[test]
fn test_<function>_<behavior>() { ... }

// Examples:
fn test_new_accepts_tesseract() { ... }           // Positive
fn test_new_rejects_unbounded_positive_orthant() { ... } // Negative
fn test_is_bounded_counterexample_axis_check_insufficient() { ... } // Critical edge case
```

### Test Fixtures

Helper functions for common test data go in the test module with clear names:

```rust
fn tesseract_hrep() -> (Vec<Vector4<f64>>, Vec<f64>) { ... }
fn cross_polytope_hrep() -> (Vec<Vector4<f64>>, Vec<f64>) { ... }
fn minimal_hrep() -> (Vec<Vector4<f64>>, Vec<f64>) { ... }
```

## Mathematical Proofs

Each public function that computes a mathematical quantity must include a **formal correctness proof** in its doc-comment. This is not an informal argument—it's a mathematical proof that the implementation correctly computes the defined quantity.

### Required Structure

```rust
/// # Proof of Correctness
///
/// **Claim:** `function(input)` returns [mathematical definition].
///
/// **Proof:** [Formal argument showing the code computes exactly that.]
```

### What to Prove

- **For computations**: Prove the algorithm computes the mathematical definition.
- **For predicates**: Prove the function returns true iff the mathematical condition holds.
- **For validation**: Prove each check correctly detects its invariant violation.

### Example (from `bounded.rs`)

The `is_bounded` function includes a full proof:

1. **Module-level**: Proves the mathematical equivalence (bounded ⟺ normals positively span ℝ⁴)
2. **Function-level**: Proves the two-phase algorithm correctly tests positive span
3. **Completeness argument**: Shows no false negatives (if unbounded, algorithm detects it)

### References

Cite textbooks or papers for non-trivial mathematical facts:
- "Convex Analysis" (Rockafellar) — positive span, recession cones
- "Computational Geometry: Algorithms and Applications" (de Berg et al.)

