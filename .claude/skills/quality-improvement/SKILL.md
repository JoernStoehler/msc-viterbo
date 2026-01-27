# Quality Improvement Refactoring

Guidelines for refactoring and improving code quality in the rust_viterbo package (and related Python/thesis components). This skill captures principles for sustainable, maintainable quality work.

## Philosophy

Quality improvement is about reducing friction for future developers (humans and agents), not about achieving abstract code purity. Every change must answer: "Does this make the codebase easier to understand, maintain, or extend?"

### Core Principles

**YAGNI (You Aren't Gonna Need It)**
- Structure code for *clearly specified* planned features, not speculative ones
- If a future feature lacks a concrete interface, don't invent one preemptively
- Delete code that serves no current purpose and has no concrete future plan
- Exception: keep code with valuable documentation even if currently dead (e.g., a commented algorithm variant that explains why it was rejected)

**KISS (Keep It Simple)**
- Prefer straightforward implementations over clever ones
- Complexity must justify itself through concrete benefits
- When two designs achieve the same goal, choose the simpler one
- Simple code is easier to verify mathematically

**DRY with Caution**
- DRY (Don't Repeat Yourself) is often bad advice for this project
- Duplication is acceptable when:
  - The duplicated code serves different conceptual purposes
  - Unifying would create tight coupling between unrelated modules
  - Each copy might evolve independently
  - The abstraction would be harder to understand than the duplication
- Only extract shared code when:
  - The duplication is truly identical in purpose and likely evolution
  - The abstraction has a clear, stable interface
  - The benefit outweighs the cognitive cost of indirection

**No Premature Optimization**
- Never optimize performance without profiling data
- Never optimize for conciseness without evidence that verbosity causes confusion
- Keep code with documentation value even if:
  - It's technically "dead" (unused code path)
  - Variables are "unused" (but document what can be computed)
  - Comments are "redundant" (but explain non-obvious reasoning)

## What Quality Improvement IS

1. **Improving code organization** for cognitive clarity
   - Colocating related functionality
   - Splitting large files into focused modules (~250 line soft limit)
   - Clear file/module naming that reflects purpose

2. **Improving documentation** for knowledge preservation
   - Adding/improving comments that explain *why*, not just *what*
   - Documenting mathematical derivations and references
   - Explaining numerical tolerances and their origins
   - Noting invariants, preconditions, postconditions

3. **Improving test coverage** for confidence and documentation
   - Tests document expected behavior
   - Tests bridge Rust's type system limitations (can't express full proofs)
   - Keep proposed/incomplete test comments as future reminders

4. **Standardizing patterns** for predictability
   - Consistent error handling approaches
   - Consistent tolerance definitions and usage
   - Consistent module structure

5. **Reducing unnecessary friction**
   - Fixing confusing names
   - Removing genuinely dead code (no documentation value)
   - Eliminating unnecessary complexity

## What Quality Improvement IS NOT

1. **NOT removing features** that are used (explicitly or implicitly)
2. **NOT adding features** beyond what's needed for quality
3. **NOT performance optimization** without profiling
4. **NOT enforcing arbitrary style rules** without benefit
5. **NOT deleting code comments** that might be useful later
6. **NOT abstracting** just to reduce line count

## Assessment Methodology

### Phase 1: Understand Before Changing

1. **Read the codebase** - understand what exists and why
2. **Identify existing conventions** - don't invent new ones unnecessarily
3. **Map dependencies** - understand what relies on what
4. **Note existing documentation** - preserve knowledge already captured
5. **Check test coverage** - understand what behavior is documented

### Phase 2: Identify Improvement Opportunities

Categorize issues by type and priority:

**Structure Issues**
- [ ] Files over ~300 lines that could be split
- [ ] Related code scattered across distant files
- [ ] Unclear module boundaries
- [ ] Inconsistent file organization patterns

**Documentation Issues**
- [ ] Undocumented public APIs
- [ ] Missing mathematical explanations
- [ ] Unexplained numerical constants
- [ ] Outdated comments
- [ ] Missing invariant documentation

**Code Smell Issues**
- [ ] Type definitions duplicated without clear purpose
- [ ] Inconsistent tolerance values across modules
- [ ] Error handling inconsistencies
- [ ] Naming that obscures purpose

**Test Coverage Gaps**
- [ ] Untested public functions
- [ ] Missing integration tests
- [ ] Incomplete property tests
- [ ] Tests that don't verify mathematical claims

### Phase 3: Prioritize Changes

Order changes by:
1. **Foundational** - changes that unblock other improvements
2. **High-impact** - changes that affect many files/developers
3. **Low-risk** - changes unlikely to break existing behavior
4. **Reversible** - changes easy to undo if problematic

### Phase 4: Make Changes Incrementally

- One logical change per commit
- Run tests after each change
- Verify no features were broken
- Update documentation as you go

## Specific Guidelines for This Codebase

### File Size Targets

- **Target**: ~100-250 lines per file
- **Acceptable**: up to ~400 lines if cohesive
- **Split candidate**: >500 lines

### Type Duplication

Currently `PolytopeHRep` and `Polygon2D` are defined in multiple crates. Before unifying:
- Verify the definitions are truly equivalent
- Ensure the unified type serves all use cases
- Consider whether tight coupling is appropriate

### Numerical Tolerances

Tolerances should be:
- **Documented** - explain why this value, not just what it is
- **Justified** - mathematical or empirical basis
- **Consistent** - same concept, same value (or documented reason for difference)
- **Centralized** - defined in one place, imported elsewhere

Current tolerance inventory:
- `EPS`: 1e-10 (billiard, tube) vs 1e-12 (hk2017) - needs investigation
- `LAGRANGIAN_TOL`: 1e-8 (hk2017) vs 1e-9 (tube) - needs investigation
- `CONSTRAINT_TOL`: 1e-8 (billiard) vs 1e-10 (hk2017) - needs investigation

### Test Organization

Tests serve multiple purposes:
1. **Verification** - catch bugs during development
2. **Documentation** - explain expected behavior
3. **Regression** - prevent future breakage
4. **Validation** - bridge Rust↔Math gap

Prefer:
- Integration test files in `tests/` for cross-module behavior
- Inline `#[cfg(test)] mod tests` for unit tests
- Named test functions that state the property being tested
- `prop_*` prefix for property-based tests

### Code Comments

Valuable comments to preserve:
- Mathematical derivations and formula explanations
- References to papers (with specific theorems/equations)
- Explanations of why an approach was chosen/rejected
- Warnings about non-obvious failure modes
- TODOs with specific actionable content

Comments to remove:
- Outdated comments that no longer match code
- Comments that just restate the code
- TODOs without actionable specifics

### Error Handling

Prefer `thiserror` for error types with:
- Descriptive variant names
- Context in error messages
- Source error chaining where appropriate

## Checklists

### Pre-Change Checklist

- [ ] Read all files that will be modified
- [ ] Understand the purpose of code being changed
- [ ] Identify tests that verify this code
- [ ] Note any documentation that might need updates
- [ ] Check if change affects public API

### Post-Change Checklist

- [ ] All tests pass (`cargo test --workspace`)
- [ ] Clippy is happy (`cargo clippy --workspace --all-targets`)
- [ ] Code is formatted (`cargo fmt`)
- [ ] Documentation updated if needed
- [ ] No features were removed unintentionally
- [ ] Commit message explains the change

### Quality Gate Questions

Before finalizing changes, ask:
1. Would a new developer understand this code more easily now?
2. Did I preserve all the knowledge that was in the code before?
3. Did I make it easier to find related code?
4. Did I avoid introducing new complexity?
5. Can the change be easily reversed if problematic?

## Anti-Patterns to Avoid

1. **Abstracting prematurely** - don't create helpers for one-time operations
2. **Chasing metrics** - don't reduce line count at the cost of clarity
3. **Consistency theater** - don't change working code just to match a style
4. **Documentation purges** - don't delete comments that might help someone
5. **Test removals** - don't delete tests that document behavior, even if "redundant"
6. **Implicit breakage** - don't remove something that's used indirectly

## Communication

When proposing quality improvements:
1. **Be specific** - name exact files, lines, issues
2. **Explain rationale** - why this change helps
3. **Acknowledge tradeoffs** - what's lost, what's gained
4. **Propose incrementally** - smaller changes are easier to review
5. **Ask about unclear cases** - when unsure, clarify before changing
