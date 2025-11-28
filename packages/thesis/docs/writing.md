# Thesis Writing Style (Agents)

Audience: AI agents drafting thesis text. Keep prose in academic voice; avoid GitHub-issue tone or chatty summaries.

Core rules
- Be literal, explicit, and concise; prefer short declarative sentences over hedging.
- Use precise math notation; prefer TeX copied from sources, not PDF OCR. State assumptions and dimension ($\mathbb{R}^4$) early.
- Front matter: every MDX in `packages/thesis/src/` must have `title`, `slug`, optional `summary`, and `internal: true` for drafts.
- Citations: name the primary source (paper/section) in prose; links are by path or arXiv id, not bare URLs.
- Avoid “summary” headings; use content-bearing headings (e.g., “Rotation Bounds from CH21”).

Tone examples (do / don't)
- Do: "We use the rotation bound $\rho<2$ from Chaidez–Hutchings (2021, Thm. 1.3) to prune sequences that revisit a 3-face." 
- Don't: "Here's a quick summary of the rotation stuff; see paper for details." 
- Do: "Minimum-action orbits avoid 1-faces (CH21, Lem. 5.2); we treat 2-faces separately." 
- Don't: "CH21 says something about faces; probably we can ignore edges."

Equation hygiene
- Use display math for key equations; inline math only for short symbols. Do not reflow equations into prose.
- If a formula is delicate, include the original TeX snippet in a code block under a short label `Source TeX:`.

Structure
- Keep sections shallow; prefer 2–3 levels of headings. Use lists only when they communicate structure (assumptions, algorithm steps).
- Mark speculative or unverified claims with `<proposed>` or `(?)`.

Scope boundaries
- Public content lives in `packages/thesis/src/`; internal drafts in `packages/thesis/src/internal/` with `internal: true`.
- Literature digests in `packages/thesis/src/literature/` follow the template in `workflows.md`.
