# polytope-database Experiment

**Status:** Stub implementation (fake data)

## Research Question

Build a central database of polytopes for probing Viterbo's conjecture using data science methods.

## Method

Generate a pandas DataFrame where each row is a polytope and columns are computed quantities.
Currently uses stub data; real algorithms will be integrated when Rust FFI is implemented.

## Columns

| Column | Type | Description |
|--------|------|-------------|
| `id` | str | Unique identifier (e.g., "tesseract", "simplex", "random-001") |
| `family` | str | Provenance: "tesseract", "simplex", "random" |
| `facet_count` | int | Number of facets (len(normals)) |
| `normals` | list[list[float]] | Outward unit normals, shape (N, 4) |
| `heights` | list[float] | Support function values, shape (N,) |
| `capacity` | float | EHZ capacity (stub: plausible fake value) |
| `volume` | float | 4D volume (stub: plausible fake value) |
| `systolic_ratio` | float | capacity^2 / (2 * volume) |
| `orbit_breakpoints` | list[list[float]] | Cyclic points in R^4, shape (M, 4) |
| `orbit_breaktimes` | list[float] | Cumulative times, shape (M,) |
| `orbit_facet_sequence` | list[int] | Facet indices for each segment |
| `has_lagrangian_2face` | bool | Has a Lagrangian 2-face |
| `is_lagrangian_product` | bool | Is a Lagrangian product K1 x K2 |

## Invariants (even for stub data)

Per `developer-spec-v2.md`:

1. `capacity > 0`
2. `systolic_ratio = capacity^2 / (2 * volume)`
3. `orbit_breakpoints[0] == orbit_breakpoints[-1]` (closed)
4. `orbit_breaktimes` strictly increasing, ending at `capacity`
5. `len(orbit_facet_sequence) == len(orbit_breakpoints) - 1`
6. No facet appears twice in `orbit_facet_sequence`

## Success Criteria

1. DataFrame builds without errors
2. Invariants hold for all rows
3. Parquet serialization works
4. Tests pass

## Outputs

- `data/polytope-database/stub.parquet` - Stub dataset with fake data
