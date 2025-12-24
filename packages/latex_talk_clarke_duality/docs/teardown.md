# Post-talk migration + teardown checklist

This talk is intentionally ephemeral. After giving the talk, migrate the *good*
content into the thesis and delete the talk package from `main`.

## Freeze (as presented)
- [ ] Ensure the *source commit* is clean (`git status`), so the PDF does not get a `-dirty` stamp.
- [ ] Record the source commit hash (needed if you commit the PDF afterwards):
  - [ ] `SOURCE_COMMIT="$(git rev-parse --short=12 HEAD)"`
- [ ] Build a clean "final" PDF:
  - [ ] `./scripts/build.sh --production`
- [ ] Copy the final PDF into the thesis assets:
  - [ ] `cp -f dist/main.pdf ../latex_viterbo/assets/manual/talks/YYYY-MM-DD-clarke-duality.pdf`
- [ ] Commit the archived PDF (so it stays in `main` after teardown):
  - [ ] `git add ../latex_viterbo/assets/manual/talks/YYYY-MM-DD-clarke-duality.pdf`
  - [ ] `git commit -m "archive: clarke duality talk PDF (YYYY-MM-DD)"`
- [ ] Create an annotated tag that points to the *source commit* used for the export:
  - [ ] `git tag -a talk-clarke-duality-YYYY-MM-DD -m "Clarke duality talk (final, as presented)" "$SOURCE_COMMIT"`

## Archive (keep in `main`)
- [ ] Confirm the final PDF exists under `packages/latex_viterbo/assets/manual/talks/`
  - Recommended filename: `YYYY-MM-DD-clarke-duality.pdf`
- [ ] (Optional) Add a short note to `packages/latex_viterbo/assets/manual/talks/README.md` with the tag name.

## Migrate (good content only)
- [ ] Port reusable definitions/notation to the thesis (`packages/latex_viterbo/chapters/...`).
- [ ] Port any good figures to `packages/latex_viterbo/assets/` (prefer `assets/manual/` for hand-made drawings).
- [ ] Replace slide-only “talk phrasing” by thesis-grade exposition.

## Teardown (remove clutter from `main`)
- [ ] Delete `packages/latex_talk_clarke_duality/` entirely.
- [ ] Rely on the frozen tag for any future reproduction of the original talk sources/assets.

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
<!-- Updated path after migration from CHECKLIST_TEARDOWN.md -->
- Follow `docs/teardown.md` after the talk.
