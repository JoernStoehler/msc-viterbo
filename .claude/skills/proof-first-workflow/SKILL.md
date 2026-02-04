---
name: proof-first-workflow
description: The 7-stage proof-first development workflow for rust_viterbo. Terminology, proofs, signatures, tests, implementation.
---

# Proof-First Workflow

This workflow ensures correctness in rust_viterbo by establishing mathematical foundations before implementation. The goal is a clear chain: thesis (math) -> SPEC.md (design) -> tests (verify spec) -> code (must pass tests).

## Workflow

### Stage 1: Terminology [proposed]

Define mathematical objects precisely in thesis LaTeX. Then document the relevant definitions in SPEC.md's glossary section, referencing the thesis.

**Output:**
- Thesis: Formal definitions in appropriate chapter
- SPEC.md: Glossary section referencing thesis definitions

**Example:**
```markdown
## Terminology [proposed]

- **Facet normal** n_i: Outward unit normal to facet F_i
- **Support value** h_i: h_i = max_{x in K} <n_i, x>
- **Characteristic** (F_*, beta): Ordered facet sequence with weights
```

### Stage 2: Computable Definitions [proposed]

Transform mathematical definitions into algorithm-checkable predicates.

**Output:** Predicates that can be implemented as boolean functions.

**Example:**
```markdown
## Computable Definitions [proposed]

- **is_closed(F_*, beta)**: sum_i beta_i * n_i = 0
- **is_feasible(F_*, beta)**: all beta_i >= 0 AND is_closed(F_*, beta)
- **is_optimal(F_*, beta)**: is_feasible(F_*, beta) AND Q(F_*, beta) > 0
```

### Stage 3: Lemmas with Proofs [proposed] -> [verified]

State lemmas with complete proofs. Reference literature where applicable.

**Markers:**
- `[proposed]` - Agent-written, awaiting Jörn's review
- `[verified]` - Jörn has confirmed correctness

**Output:** Lemmas with:
- Statement
- Proof sketch or full proof
- Literature reference if applicable

**Example:**
```markdown
## Lemmas

### Lemma 3.1: Closure Constraint [proposed]
**Statement:** A characteristic (F_*, beta) represents a closed orbit iff sum_i beta_i * n_i = 0.

**Proof:** The orbit closes when the total displacement equals zero. Since each segment along facet F_i has direction n_i with length proportional to beta_i... [continue proof]

**Reference:** HK2017 Proposition 4.2
```

### Stage 4: Signatures

Define Rust types with invariant documentation. Types encode the math.

**Output:** Type definitions with doc comments explaining invariants.

**Example:**
```rust
/// A closed characteristic on the boundary of a convex body.
///
/// # Invariants
/// - `facets` is non-empty and ordered
/// - `betas` has same length as `facets`
/// - All betas are non-negative
/// - sum(beta_i * normal_i) = 0 (closure)
pub struct Characteristic {
    facets: Vec<FacetIndex>,
    betas: Vec<f64>,
}
```

### Stage 5: Test Brainstorming

Convert propositions into test cases. List all properties to verify.

**Output:** List of test case ideas mapped to lemmas.

**Example:**
```markdown
## Test Cases

From Lemma 3.1 (Closure):
- [ ] Valid characteristic satisfies closure check
- [ ] Invalid characteristic (non-zero sum) fails closure check
- [ ] Edge case: single facet (always fails closure)
- [ ] Edge case: two opposite normals (can close)

From Lemma 3.2 (Optimality):
- [ ] Known optimal characteristic returns positive Q
- [ ] Suboptimal characteristic returns smaller Q
```

### Stage 6: Test Implementation

Implement all test cases. They must all fail initially (red phase).

**Rules:**
- Tests derive directly from brainstorm list
- Each test references the lemma it verifies
- Run tests to confirm they fail before implementation

**Example:**
```rust
#[test]
fn characteristic_closure_valid() {
    // Lemma 3.1: closure constraint
    let char = Characteristic::new(facets, betas);
    assert!(char.is_closed());
}

#[test]
fn characteristic_closure_invalid_nonzero_sum() {
    // Lemma 3.1: closure constraint (negative case)
    let char = Characteristic::new_unchecked(facets, bad_betas);
    assert!(!char.is_closed());
}
```

### Stage 7: Implementation

Implement functions 1:1 from proofs. The code should read like the proof.

**Rules:**
- Follow proof structure exactly
- If implementation diverges from proof, escalate
- Run tests after each function (green phase)

## Invariants

### Escalation Rules

Escalate to Jörn when:

1. **Proof can't be implemented 1:1**
   - Algorithm requires different approach than proof
   - Numerical issues prevent direct translation

2. **Test doesn't follow math**
   - Test case seems wrong given the lemma
   - Edge case behavior is unclear

3. **Need to edit proofs during implementation**
   - This is OUT OF SCOPE for developer agent
   - Proofs are frozen once [verified]

4. **Verification fails after implementation**
   - Test fails but code looks correct
   - Check: does test match spec?
   - Check: does spec encode math correctly?
   - If both yes -> code is wrong
   - If spec/test wrong -> escalate

### The [proposed] Marker System

- Agent writes `[proposed]` next to new mathematical content
- Only Jörn removes `[proposed]` to mark as approved
- Ambiguous responses don't count as approval
- Never implement against `[proposed]` content without explicit approval

**Scope of [proposed]:**
- Terminology definitions
- Computable definitions
- Lemma statements and proofs
- Algorithm descriptions

**Not [proposed]:**
- Code (reviewed via PR process)
- Test cases (reviewed via PR process)
- FINDINGS.md (empirical, not mathematical)

### Correctness Chain

```
thesis (math)
    |
    v
SPEC.md (design) [proposed] -> [verified]
    |
    v
tests (verify spec)
    |
    v
code (must pass tests)
```

When a test fails:
1. Does test match spec?
2. Does spec encode math correctly?
3. If both yes -> code bug
4. If no -> escalate
