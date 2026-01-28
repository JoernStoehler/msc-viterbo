---
name: review-thesis-writing-style
description: Reviewing thesis writing quality, clarity, and style. Use when checking exposition for symplectic geometer audience, improving readability, or ensuring LaTeX formatting conventions are followed.
---

# Thesis Writing Style Review

**When to use:**
- Reviewing thesis chapters for clarity
- Ensuring exposition is appropriate for audience
- Checking LaTeX formatting conventions
- Improving readability and organization

## Audience and Goals

- **Audience**: Symplectic geometers
- **Self-contained**: Expose assumptions, define notation
- **Skimmable**: Headings and structure guide reader

## Style Guidelines

### Exposition Structure

- **Spoilers up front**: State main results before proofs
- **Mainline vs asides**: Keep main argument clear, use remarks/footnotes for tangents
- **Progressive refinement**: Start intuitive, add rigor incrementally

### Notation

- **Introduce once**: Define notation when first used
- **Note deviations**: Call out when notation differs from literature
- **Consistency**: Don't switch notation mid-chapter

### Proofs

- **Use proof environment**: `\begin{proof}...\end{proof}`
- **Signpost structure**: "First we show X. Then we use X to prove Y."
- **Label key steps**: Equations that are referenced later need `\label{}`

### Work-in-Progress

- **Mark clearly**: Use `\edit{...}` or `% TODO: ...`
- **Remove before final**: WIP markers should not be in submitted thesis

## Common Issues to Check

**Passive voice overuse:**
- Bad: "It was shown that..."
- Good: "We show that..." or "Theorem 3.2 states that..."

**Undefined notation:**
- Check that every symbol is defined before use
- Exception: Standard notation (ℝ, ℤ, etc.)

**Proof without roadmap:**
- Long proofs need structure
- Add "Proof strategy" paragraph or outline steps

**Missing citations:**
- Every non-obvious statement needs a citation or proof
- Standard results can cite textbooks

## LaTeX Quality Checks

**Math mode:**
- Inline: `\(...\)` not `$...$`
- Display: `\[...\]` not `$$...$$`

**Cross-references:**
- Use `\ref{}` not hardcoded numbers
- Use `\eqref{}` for equations

**Consistent macros:**
- Define custom commands in preamble, not inline
- Example: `\newcommand{\Sp}{\operatorname{Sp}}` for symplectic group
