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

