# AGENTS (latex_talk_clarke_duality)

Purpose
- Ephemeral seminar talk slides (PDF) about Clarke's duality principle.
- Designed for fast iteration for ~2 weeks, then migration into `packages/latex_viterbo`.
- Not intended as a long-lived, reproducible deliverable in `main`.

Build
- Build PDF: `scripts/build.sh`
- Lint (optional): `scripts/lint.sh`

Assets
- Hand-made drawings and sketches: `assets/manual/`
- Prefer vector PDFs for line drawings.

Lifecycle (freeze → migrate → teardown)
1. Freeze (final version as given):
   - Ensure slides compile and look correct.
   - The build script stamps the current *source commit* into the PDF footer as `source: <hash>`.
   - Prefer tagging the *source commit* (not the later archive commit that adds the PDF), e.g.:
     - `SOURCE_COMMIT="$(git rev-parse --short=12 HEAD)"`
     - `git tag -a talk-clarke-duality-YYYY-MM-DD -m "Clarke duality talk (final, as presented)" "$SOURCE_COMMIT"`
2. Migrate:
   - Copy the good math + figures into the thesis (`packages/latex_viterbo/chapters/` and `packages/latex_viterbo/assets/`).
3. Teardown (post-migration cleanup):
   - Keep only the final PDF (and a short pointer README) under:
     - `packages/latex_viterbo/assets/manual/talks/`
   - Delete this entire package.
   - If someone needs the exact sources/assets later, they can check out the frozen tag.

Checklist
- Follow `CHECKLIST_TEARDOWN.md` after the talk.
