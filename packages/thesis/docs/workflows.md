# Writing Workflows (Thesis)

Bullet notes → prose (fast path)
1) Normalize scope: restate the claim in one sentence with dimension ($\mathbb{R}^4$) and object type (convex polytope).
2) Pull source TeX for any equations; paste under a short `Source TeX:` code block to avoid PDF corruption.
3) Expand bullets into short declarative sentences; group by assumption/result/implication; add a reference tag (e.g., CH21 Lem. 5.2).
4) Add front matter (`title`, `slug`, `summary`, `internal` if draft) and place in the right folder.

Literature digest recipe (`packages/thesis/src/literature/<bibkey>.mdx`)
- Front matter: `title`, `slug` (bibkey), optional `tags`, `internal` if not public.
- Sections: Context (what problem it solves), Claims Checked (with precise refs), Key Equations (TeX snippets), Caveats/Limitations, How we reuse it.
- Always cite chapter/section/lemma numbers; note if proof is assumed vs. verified.

Claim-check checklist
- Identify the minimal authoritative source (original paper/section), not a survey.
- Verify formulas against TeX sources; avoid PDFs. If only PDF exists, flag the formula as `(needs TeX verification)`.
- For algorithms, note assumptions (smoothness, non-Lagrangian faces, etc.) and whether they hold for our polytope classes.
- Record any parameter ranges or rotation bounds used for pruning.

Housekeeping
- When moving a draft to public, remove `internal: true`, re-read for tone, and ensure references point to assets and code paths under `packages/`.
- If a convention changes, update this file and the relevant MDX pages; do not leave stale alternatives.
