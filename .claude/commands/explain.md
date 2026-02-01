# Explain

Produce a precise, structured explanation of a technical topic in this codebase.

## Arguments

$ARGUMENTS

## Instructions

Your goal is to produce an explanation that is:
- **Mathematically correct**: No hand-waving or imprecise statements
- **Epistemically correct**: Every claim cites its source; unknowns are marked as unknown
- **Structured**: Readable sections, tables, code references

### Process

1. **Gather sources first**
   - Read all relevant source files (don't guess from memory)
   - Check git history for provenance of key decisions
   - Look for specs, docs, comments that explain "why"

2. **Draft to a temp file**
   - Write to `/tmp/explain-draft.md`
   - You cannot fix mistakes in chat output, so draft first
   - Revise until the explanation is complete

3. **Structure your explanation**
   ```
   ## Executive Summary
   [1-3 sentences: what is this, what's the answer/situation]

   ## 1. [First concept needed to understand]
   **Source**: [file:lines](path#Lstart-Lend)
   [Explanation with code snippets if helpful]

   ## 2. [Second concept]
   ...

   ## N. Epistemic Status
   | Claim | Source | Justified? |
   |-------|--------|------------|
   | ... | ... | ✅/❌/⚠️ |

   ## Open Questions
   [What remains unknown or unverified]
   ```

4. **For every claim, note its source**
   - Code: `[file.rs:42](path/file.rs#L42)`
   - Math: "standard result" or cite paper/theorem
   - Design decision: commit hash + author, or "no documented justification"
   - Hypothesis: explicitly mark as "hypothesis" or "unverified"

5. **Present the draft**
   - Show the user the key findings in chat
   - Reference the full document at `/tmp/explain-draft.md`

### What NOT to do

- Don't guess file contents — read them
- Don't claim something is "standard" without checking if this codebase follows the standard
- Don't hide uncertainty — if you don't know, say "unknown" or "unverified"
- Don't skip the epistemic status table — it's the most valuable part
- Don't write top-to-bottom in chat — use the temp file so you can revise

### Example epistemic markers

- ✅ **Justified**: Directly stated in code/spec/math, or trivially follows
- ⚠️ **Hypothesis**: Plausible but not verified
- ❌ **Unjustified**: No documented reason found
- 🔍 **Needs investigation**: Could be determined but hasn't been checked
