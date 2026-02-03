# crates/

[proposed]

Rust workspace for EHZ capacity algorithms.

## Crates

| Crate | Purpose |
|-------|---------|
| `geom2d` | 2D convex geometry (Polygon, area) |
| `geom4d` | 4D polytope primitives (HRep, is_bounded) |
| `hk2017` | HK2017 capacity algorithm (stub) |
| `billiard` | Billiard capacity algorithm (stub) |
| `tube` | Tube capacity algorithm (stub) |
| `ffi` | PyO3 bindings (viterbo_ffi) |

Old implementations at git commit 0b5511a.

## Proof-First Workflow

Algorithms follow 7 stages before implementation:

1. **Terminology**: Define terms in thesis LaTeX
2. **Computable definitions**: Ensure definitions translate to code
3. **Lemmas**: Prove correctness-critical lemmas
4. **Signatures**: Define Rust API (types, errors)
5. **Test brainstorm**: List test cases by category
6. **Test implementation**: Write tests (they will fail)
7. **Code implementation**: Make tests pass

**Escalation**: If any stage reveals ambiguity or mathematical error, stop and escalate to Jorn before proceeding.

## Commands

```bash
scripts/test.sh                 # Run all tests (debug + release)
scripts/test.sh --debug         # Debug tests only (with debug_assert!)
scripts/test.sh --release       # Release tests only (expensive ones)
cargo clippy --workspace        # Lint
cargo fmt --all                 # Format
```

## Design Philosophy

1. **Correctness**: Code must implement the mathematical specification exactly
2. **Clarity**: Code should be readable and its correctness verifiable
3. **Testability**: Invariants checkable via tests and `debug_assert!`
4. **Strictness**: Reject invalid input early; don't accept constraint violations

No premature optimization: don't add fast paths or heuristics unless profiling shows need.

## Type Construction Pattern

```rust
Type::new(data) -> Result<Type, TypeError>   // Validates all invariants
Type::new_unchecked(data) -> Type            // debug_assert! only; tests with known-good data
```

## Testing Conventions

Required test categories:
- **Positive**: Valid inputs accepted
- **Negative**: Each error variant triggered
- **Edge cases**: Boundary conditions, near-tolerance values
- **Property tests**: Mathematical invariants (scaling, monotonicity)
- **Cross-checks**: Agreement with known values or other algorithms

## See Also

- Skill `proof-first-workflow` for the full 7-stage workflow
- Skill `capacity-algorithms` for algorithm selection guidance
- Skill `debugging-numerical` for tolerance handling
