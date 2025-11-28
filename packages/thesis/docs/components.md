# MDX Components (Thesis)

Allowed components (keep the palette small; export must remain Pandoc-friendly):

- `Definition` — props: `title` (optional), `id` (optional). Body: markdown/inline math.
- `Proposition` / `Theorem` / `Lemma` — props: `title` (optional), `id` (optional). Body: statement; add a following `ProofSketch` if needed.
- `ProofSketch` — props: none required. Body: short structured argument; flag gaps with `<proposed>`.
- `Callout` — props: `variant` in `{note, warning, tip}`. Use for operational notes, not for core math.
- `FigureBlock` — props: `id` (matches assets), optional `caption`. The id must correspond to assets under `src/assets/figures/<chapter>/`.

Export expectations
- Each component must render to plain markdown via `renderStatic`; keep props minimal to ease the Pandoc pipeline.
- Avoid embedding HTML or React-only features inside components.
- Do not invent new components without updating this file and the docs-site/print exporters.

Usage examples
- Definition: `import { Definition } from "../components/Definition"` then `<Definition title="Support function">$h_K(z)=\sup_{w\in K}\langle z,w\rangle$</Definition>`.
- Proposition + proof sketch pair for algorithmic pruning, referencing CH21 bounds.
- Callout example for implementation caveats (e.g., "Floating-point version uses outward normals normalized to unit length").
