---
name: explain
description: Structured technical explanations with epistemic rigor. Produces explanations citing sources and marking uncertainty. Use when asking "how does X work", "explain", "what is". Invoke with /explain.
---

# Explain

Produce a precise, structured explanation of a technical topic in this codebase.

## Arguments

$ARGUMENTS

## Output Requirements

Your goal is to produce an explanation that is:
- **Mathematically correct**: No hand-waving or imprecise statements
- **Epistemically correct**: Every claim cites its source; unknowns are marked as unknown
- **Structured**: Readable sections, tables, code references

## Workflow

1. **Gather sources first**
   - Read all relevant source files (don't guess from memory)
   - Check git history for provenance of key decisions
   - Look for specs, docs, comments that explain "why"

2. **Structure your explanation**
   ```
   ## Executive Summary
   [1-3 sentences: what is this, what's the answer/situation]

   ## 1. [First concept needed to understand]
   **Source**: [file:lines](path#Lstart-Lend)
   [Explanation with code snippets if helpful]

   ## N. Epistemic Status
   | Claim | Source | Justified? |
   |-------|--------|------------|
   | ... | ... | ✅/❌/⚠️ |

   ## Open Questions
   [What remains unknown or unverified]
   ```

3. **For every claim, note its source**
   - Code: `[file.rs:42](path/file.rs#L42)`
   - Math: "standard result" or cite paper/theorem
   - Design decision: commit hash + author, or "no documented justification"
   - Hypothesis: explicitly mark as "hypothesis" or "unverified"

## Epistemic Markers

- ✅ **Justified**: Directly stated in code/spec/math, or trivially follows
- ⚠️ **Hypothesis**: Plausible but not verified
- ❌ **Unjustified**: No documented reason found
- 🔍 **Needs investigation**: Could be determined but hasn't been checked

## Anti-Patterns

- Don't guess file contents — read them
- Don't hide uncertainty — if you don't know, say "unknown"
- Don't skip the epistemic status table — it's the most valuable part
