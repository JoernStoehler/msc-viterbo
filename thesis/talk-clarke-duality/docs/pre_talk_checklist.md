# Pre-talk checklist (Clarke duality talk)

Goal: be able to walk into the room, plug in, and present without surprises.

## Critical (must do)

1. **Have the final PDF locally**
   - Confirm `packages/latex_talk_clarke_duality/build/main.pdf` opens on the presentation device.
   - Have a second copy somewhere easy (Downloads / Desktop / phone).
   - Optional: also generate a “production” copy via `./scripts/build.sh --production` and use `dist/main.pdf`.

2. **Hand-drawn slides workflow**
   - All “image” placeholders are **empty boxes** (intended to be drawn into directly in the PDF).
   - Ensure your PDF annotator app can draw on top of the boxes (and does not reflow pages).
   - Test: draw one line, undo, redo, save.
   - Stylus/tablet charged.

3. **Run-through for correctness hotspots**
   - Identify every red constant/marker you left yourself and decide:
     - confirm it (speak it confidently), or
     - explicitly flag it as “up to a constant” (and move on), or
     - remove the slide / hide the constant.
   - Especially: normalization (`[0,T]` vs `[0,1]`), factor `2`, factor `1/4`, scaling laws.

4. **References slide**
   - Verify the HK2024 (Haim–Kislev–Ostrover) reference is acceptable as currently written.
   - If you insist on “journal, not arXiv”, you need the final journal + year + DOI.

5. **Presentation mechanics**
   - HDMI/USB-C dongle present.
   - Clicker works (batteries).
   - Confirm aspect ratio (16:9) and that math is readable from the back.
   - Turn off notifications / airplane mode.

## High (strongly recommended)

6. **Narrative rehearsal**
   - 1 dry run of the transitions between modules (just the first sentence of each slide).
   - Identify any slide where you “don’t know what to say next” and add a 1-line speaker note (as a `%` comment).

7. **Blackboard moments**
   - For each `% TODO(Joern): blackboard` comment: decide whether you actually want to do it.
   - If yes: know what you write (1 formula, 1 picture; not more).

8. **Drawing plan**
   - For each empty box: decide the minimum viable drawing (MVD):
     - what *one picture* conveys the idea,
     - what labels are essential,
     - what can be omitted.

## Medium (nice to have)

9. **Backup if drawing fails**
   - Plan what you say if you cannot draw (e.g. “imagine this picture…” + point at formula).

10. **Post-talk hygiene**
   - Decide whether you want to save the annotated PDF and where.

