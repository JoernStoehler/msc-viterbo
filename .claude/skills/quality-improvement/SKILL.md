---
name: quality-improvement
description: Refactor and improve code quality in rust_viterbo. Use for maintainability improvements, code organization, tolerance standardization, and reducing cognitive load without breaking features.
---

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

### Type Sharing via geom Crate

**Status (2026-01):** `PolytopeHRep` is now defined in `geom` crate and re-exported by all algorithms.

`Polygon2D` remains algorithm-specific because tube and billiard use different representations:
- tube: V-rep only (vertices)
- billiard: V+H-rep (vertices + normals + heights)

Each algorithm adds its own validation function (e.g., `validate_for_hk2017`) for algorithm-specific requirements.

### Numerical Tolerances

Tolerances should be:
- **Documented** - explain why this value, not just what it is
- **Justified** - mathematical or empirical basis
- **Consistent** - same concept, same value (or documented reason for difference)
- **Centralized** - defined in one place, imported elsewhere

**Status (2026-01):** Base tolerances are in `geom::tolerances`. Algorithm-specific tolerances remain local:
- hk2017 uses stricter `EPS=1e-12` due to KKT solver precision needs (documented in code)
- tube has extensive tolerance documentation in `constants.rs`
- Tolerance differences are now documented; further standardization would need empirical testing

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

## Common Mistakes (Lessons Learned)

**Mistake: Not reading this skill before starting quality work**
- Skills exist to guide HOW to do tasks — read them FIRST
- "Assess code quality" matches this skill's description — should trigger reading it immediately
- Launching exploration agents before reading methodology leads to superficial analysis
- The skill's Assessment Methodology section exists precisely to prevent wasted effort

**Mistake: Trusting linter/tool output as authoritative**
- Clippy warnings, pyright errors, etc. are suggestions, not verdicts
- Many warnings are stylistic preferences, not real issues
- Some "errors" are limitations of the tool (e.g., missing type stubs for scipy)
- Always analyze: "Is this a real problem, or tool noise?"
- Ask: "Would fixing this improve the code, or just silence the tool?"

**Mistake: Creating "ignore" patterns as solutions**
- Don't configure tools to perpetually suppress classes of warnings/errors
- Don't create rules like "always use `# type: ignore` for scipy" — that's one more thing agents must remember
- If a tool reports something, prefer actually fixing the code over silencing the tool
- Occasional targeted ignore comments are fine when genuinely unavoidable and explained
- The problem is creating patterns/rules that add cognitive load for future agents

**Mistake: Jumping to DRY without reading code**
- Grepping for duplicate struct names finds shallow duplication
- Misses duplicated *functions* (e.g., `symplectic_form()` in both hk2017 and tube)
- Misses that files with different names can have identical content

**Mistake: Skipping Phase 1 (Understand Before Changing)**
- Writing a methodology document doesn't mean you followed it
- Actually read the algorithm implementations before proposing changes
- Compare function signatures across crates, not just type definitions

**Mistake: Not planning how to achieve the goal**
- Broad goals are fine, but need a concrete plan before starting work
- Plan should specify: what to read, in what order, what to look for
- Example plan for "assess code quality":
  1. List all source files
  2. For each file: read it, note documentation gaps, unclear code, test coverage
  3. Compare similar files across crates for duplication
  4. Compile findings before proposing changes

**Mistake: Treating consolidation as the primary goal**
- Quality improvement is not primarily about reducing duplication
- Documentation quality, test coverage, code clarity matter more
- Consolidation is a means, not an end

**Mistake: Reporting "assessment complete" without reading code**
- File size counts and grep results are not an assessment
- Must actually read implementations to assess quality
- Must understand what the code does before judging how well it does it

**Mistake: No definition of done**
- Before starting, define what "complete" means concretely
- Example for "consolidate shared code":
  - [ ] All mathematical primitives listed for each crate
  - [ ] Each identified as shared vs algorithm-specific
  - [ ] Shared primitives moved to geom with tests
  - [ ] All crates updated to import from geom
  - [ ] All tests pass
- Without this, you'll do partial work and declare victory
- "I moved one struct" is not done if there are also duplicated functions

## Communication

When proposing quality improvements:
1. **Be specific** - name exact files, lines, issues
2. **Explain rationale** - why this change helps
3. **Acknowledge tradeoffs** - what's lost, what's gained
4. **Propose incrementally** - smaller changes are easier to review
5. **Ask about unclear cases** - when unsure, clarify before changing
