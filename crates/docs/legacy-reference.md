# Legacy Crate Reference

The following crates were deleted as part of the proof-first redesign (2026-02-02).
Their code is preserved in git history for cherry-picking and reference.

## Last Commit With Legacy Crates

```
0b5511a feat(geom): add is_bounded() using LP to check normals positively span R^4
```

## Deleted Crates

| Crate | Purpose | View Command |
|-------|---------|--------------|
| geom | Shared polytope primitives | `git show 0b5511a:packages/rust_viterbo/geom/` |
| tube | Non-Lagrangian algorithm | `git show 0b5511a:packages/rust_viterbo/tube/` |
| hk2017 | General HK2017 algorithm | `git show 0b5511a:packages/rust_viterbo/hk2017/` |
| billiard | Lagrangian product algorithm | `git show 0b5511a:packages/rust_viterbo/billiard/` |
| ffi | Python FFI bindings | `git show 0b5511a:packages/rust_viterbo/ffi/` |

## Extracting Old Code

To view a specific file:
```bash
git show 0b5511a:packages/rust_viterbo/geom/src/boundedness.rs
```

To extract a directory:
```bash
git archive 0b5511a packages/rust_viterbo/geom/ | tar -x
```

## Key Files Worth Reviewing

When reimplementing algorithms, these files contain useful reference implementations:

- `geom/SPEC.md` - Mathematical definitions and API design
- `geom/src/boundedness.rs` - LP-based boundedness check (migrated to geom4d)
- `tube/SPEC.md` - Tube algorithm specification
- `hk2017/SPEC.md` - HK2017 algorithm specification
- `billiard/SPEC.md` - Billiard algorithm specification (draft)
