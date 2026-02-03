# polytope-database Experiment

**Status:** Staged implementation (stub data for volumes and capacities)

## Research Question

Build a central database of polytopes for probing Viterbo's conjecture using data science methods.

## Method

The experiment is split into 3 modular stages to enable incremental reruns:

### Stage 1: Polytope Geometries (`stage_polytopes.py`)

Generate polytope H-representations without computing capacities or volumes.

**Families:**
- `tesseract`: [-1,1]^4 (8 facets)
- `simplex`: Regular 4-simplex (5 facets)
- `cross-polytope`: 16-cell (16 facets)
- `24-cell`: Icositetrachoron (24 facets)
- `random`: Random H-reps (8 instances, 6-12 facets each)

**Output:** `data/polytope-database/polytopes.json`

**Status:** ✅ Implemented

### Stage 2: Volume Calculations (`stage_volume.py`)

Add volume calculations using Rust FFI.

**Blocked:** Waiting for `volume_hrep()` FFI implementation (TODO #31)

**Current:** Uses stub/fake volumes matching stage_build.py behavior

**Output:** `data/polytope-database/polytopes_with_volume.json`

**Status:** 🚧 Stub implementation

### Stage 3: Capacity Calculations (`stage_capacity.py`)

Add capacity and systolic ratio calculations using Rust FFI.

**Dependencies:**
- `tube_capacity_hrep()` FFI (already implemented)
- `systolic_ratio()` helper (TODO: needs FFI exposure)

**Current:** Uses stub/fake capacities and orbits

**Output:** `data/polytope-database/complete.json`

**Status:** 🚧 Stub implementation

## Schema

### Stage 1 Output (polytopes.json)

| Column | Type | Description |
|--------|------|-------------|
| `id` | str | Unique identifier (e.g., "tesseract", "cross-polytope", "random-001") |
| `family` | str | Provenance: "tesseract", "simplex", "cross-polytope", "24-cell", "random" |
| `facet_count` | int | Number of facets (len(normals)) |
| `normals` | list[list[float]] | Outward unit normals, shape (N, 4) |
| `heights` | list[float] | Support function values, shape (N,) |
| `has_lagrangian_2face` | bool | Has a Lagrangian 2-face |
| `is_lagrangian_product` | bool | Is a Lagrangian product K1 x K2 |

### Stage 2 Output (polytopes_with_volume.json)

Adds:
- `volume` (float): 4D volume

### Stage 3 Output (complete.json)

Adds:
- `capacity` (float): EHZ capacity
- `systolic_ratio` (float): capacity^2 / (2 * volume)
- `orbit_breakpoints` (list[list[float]]): Cyclic points in R^4, shape (M, 4)
- `orbit_breaktimes` (list[float]): Cumulative times, shape (M,)
- `orbit_facet_sequence` (list[int]): Facet indices for each segment

## Invariants

All stages preserve these invariants:

1. All polytopes have `id`, `family`, `facet_count`, `normals`, `heights`
2. Normals are unit vectors (||n|| = 1)
3. Heights are positive (h > 0)

Stages 2-3 additionally ensure:

4. `volume > 0`
5. `capacity > 0`
6. `systolic_ratio = capacity^2 / (2 * volume)`
7. `orbit_breakpoints[0] == orbit_breakpoints[-1]` (closed)
8. `orbit_breaktimes` strictly increasing, ending at `capacity`
9. `len(orbit_facet_sequence) == len(orbit_breakpoints) - 1`
10. No facet appears twice in `orbit_facet_sequence`

## Running the Pipeline

```bash
cd packages/python_viterbo

# Stage 1: Generate polytope geometries
uv run python -m viterbo.experiments.polytope_database.stage_polytopes

# Stage 2: Add volumes (currently uses stub data)
uv run python -m viterbo.experiments.polytope_database.stage_volume

# Stage 3: Add capacities (currently uses stub data)
uv run python -m viterbo.experiments.polytope_database.stage_capacity
```

## Success Criteria

1. Each stage runs without errors
2. Invariants hold for all rows at each stage
3. JSON serialization works
4. All tests pass (`pytest tests/test_polytope_database.py`)

## Future Work

Once FFI is complete:

1. Update `stage_volume.py` to use `ffi.volume_hrep(normals, heights)`
2. Update `stage_capacity.py` to use:
   - `ffi.tube_capacity_hrep()` for non-Lagrangian polytopes
   - `ffi.billiard_capacity_hrep()` for Lagrangian products
   - `ffi.systolic_ratio(capacity, volume)` for ratio calculation
3. Remove stub data generation
4. Convert JSON outputs to Parquet for better performance with large datasets

## Legacy

`stage_build.py` contains the original monolithic implementation and is kept as a reference. It can be removed once the staged pipeline is fully validated with real FFI data.
