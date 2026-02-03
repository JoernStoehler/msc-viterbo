# crates/CLAUDE.md

Rust workspace for EHZ capacity algorithms.

## Structure

```
crates/
  Cargo.toml
  Cargo.lock
  geom2d/     # general-purpose 2d geometry (polygons, Sp(2) matrix group, ...)
    src/
    tests/    # all the tests we could brainstorm
    Cargo.toml
    CLAUDE.md # crate-specific knowledge
  geom4d/     # general-purpose 4d geometry (polytopes, piecewise affine paths, Reeb flows, ...)
    ...
  hk2017/     # HK2017 capacity algorithm
    ...
  billiard/   # Billiard capacity algorithm
    ...
  tube/       # Tube capacity algorithm
    ...
  ffi/        # PyO3 bindings (viterbo_ffi)
    src/
    Cargo.toml
    pyproject.toml
```

Old broken implementations at git commit 0b5511a.

## Proof-First Workflow

Algorithms follow 7 stages before implementation:

1. **Terminology**: Define terms in thesis LaTeX
2. **Computable definitions**: Ensure definitions translate to code
3. **Lemmas**: Prove correctness-critical lemmas
4. **Signatures**: Define Rust API (types, errors)
5. **Test brainstorm**: List test cases by category
6. **Test implementation**: Write tests (they will fail)
7. **Code implementation**: Make tests pass

**Escalation**: If any stage reveals ambiguity or mathematical error, stop and escalate to Jörn before proceeding.

## Commands

```bash
cd /workspaces/worktrees/<task>/crates && ...
scripts/test.sh                 # Run all tests (debug + release)
scripts/test.sh --debug         # Debug tests only (with debug_assert!)
scripts/test.sh --release       # Release tests only (expensive ones)
cargo clippy --workspace        # Lint
cargo fmt --all                 # Format
```

## Design Philosophy

1. **Correctness**: Code must implement the mathematical specification exactly one-to-one
2. **Clarity**: Code should be readable and documented so that its correctness is easily verifiable
3. **Testability**: Invariants checkable via tests and `debug_assert!`
4. **Strictness**: Reject invalid input early; don't accept constraint violations
5. **Document dependent type theory information**: Document, and ideally assert, invariants between variables that are not expressible in Rust's type system

No premature optimization: don't add fast paths or heuristics unless profiling shows need.

## Type Construction Pattern

```rust
Type::new(data) -> Result<Type, TypeError>   // Validates all invariants
Type::new_unchecked(data) -> Type            // debug_assert! only; tests with known-good data
```

## Testing Conventions

Brainstorm tests using the following categories (plus other ad-hoc categories as possible):
- **Cover all scenarios**: Consider what inputs behave differently from a mathematical perspective: lemma applies / does not apply, different cases, different qualitative properties that may relate to the lemma's proof steps somehow. Consider similarly the implemented code paths, including rejection and error paths.
- **Alternate Lemmas**: Consider variants of the central lemma, e.g. a restricted domain lemma that is easier to prove, the contrapositive, implication chains, try out equivalent definitions, only state some implications, combinations of restricted domain + chain with other lemma + state weaker implication, ...
- **Intermediate Lemmas**: Extract lemmas/propositions about intermediate variables/definitions in the proof, and test those too.
- **Concretizations**: Consider concretized versions with specific computable values and perhaps ad-hoc arguments with an unrolled proof that is now more easily checkable.
- **Cross-checks**: Agreement with other algorithms, literature values, hand-calculated values.
- **Rust edge cases**: Consider edge cases that are opened up by Rust's type system, e.g. empty collections, zero/negative values, NaN/infty/large/tiny floating point values, mismatched collection shapes, permuted Sets/Vecs, etc.

Example: A subset of ideas for a novel example algorithm `capacity(K: Polytope) -> f64`
- Central lemma: "The algorithm \(\mathrm{capacity}\) given the encoding `K` of polytope \(K\) returns \(c_{EHZ}(K)\)."
- **Cover all scenarios**: lagrangian 2-faces, nearly lagrangian 2-faces, no lagrangian 2-faces, systolic ratio >1 / <1 / =1, many facets, few facets, high symmetry, no symmetry, nearly a sphere, nearly a tube, rather elongated, sharp angles like a hypercube, degenerate facet intersections, generic position, integer coordinates, ...
- **Alternate Lemmas**: "The function `capacity` behaves like a symplectic capacity: monotonicity, symplectic invariance, conformality" aka "\forall K polytope, \phi \in Sp(4): capacity(\phi(K)) = capacity(K)", "The output of `capacity` is bounded by known lower/upper bounds", "Under a Sp(4) symplectomorphism the orbit set transforms as follows ...", ...
- **Intermediate Lemmas**: "All candidate minimum action orbits are Reeb orbits and thus have `action`=`period`", "The best-known upper bound is non-increasing", "Along tube extensions, the affine action function is non-decreasing on the restricted endpoint set", "If a tube contains no trajectory, the search exits the branch early", ...
- **Concretizations**: "For the cube we calculated an upper bound of 3 by hand", "For the cross-polytope, the final orbit must have a shear transition map, because ...", "Symmetric polytopes have a symmetry-invariant set of minimum action orbits", ...
- **Cross-checks**: "For all lagrangian product polytopes, `capacity` equals `billiard.capacity`", "The hypercube has capacity 2 as per HK2017 Table 1", "A perturbation of the cube has capacity close to 2", ...
- **Rust edge cases**: "`capacity` is unstable around polytopes with tiny and large coordinates", "`Polytope::new` rejects polytopes with too large/tiny coordinates", "The search heap grows linearly with facet count, not exponentially", ...

## Dependencies

Add to crate's `Cargo.toml`, run `cargo build`.

## See Also

- Skill `proof-first-workflow` for the full 7-stage workflow
- Skill `capacity-algorithms` for algorithm selection guidance
- Skill `debugging-numerical` for tolerance handling
