"""DEPRECATED: Monolithic stub polytope database builder.

This module has been superseded by the staged pipeline:
- stage_polytopes.py: Generate polytope geometries
- stage_volume.py: Add volume calculations
- stage_capacity.py: Add capacity calculations

This file is kept as a legacy reference and may be removed in the future.

For the new pipeline, see SPEC.md.

---

Original docstring:

This module generates a DataFrame of polytopes with plausible stub data.
The stub data satisfies mathematical invariants (see SPEC.md) but does not
come from real algorithms. It serves as a template for the real database.

Usage:
    uv run python -m viterbo.experiments.polytope_database.stage_build

Output:
    data/polytope-database/stub.parquet
"""

from __future__ import annotations

import math
import random
from pathlib import Path

import pandas as pd


def tesseract_hrep() -> tuple[list[list[float]], list[float]]:
    """H-rep for tesseract [-1,1]^4. Known capacity = 4.0."""
    normals = [
        [1.0, 0.0, 0.0, 0.0],
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, -1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, -1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
        [0.0, 0.0, 0.0, -1.0],
    ]
    heights = [1.0] * 8
    return normals, heights


def simplex_hrep() -> tuple[list[list[float]], list[float]]:
    """H-rep for regular 4-simplex centered at origin. Known capacity = 0.25."""
    # 5 facets pointing toward vertices of a regular simplex
    # Vertices of regular 4-simplex (not centered, but normals work)
    sqrt5 = math.sqrt(5)
    normals = [
        [1.0, 1.0, 1.0, -1.0 / sqrt5],
        [1.0, -1.0, -1.0, -1.0 / sqrt5],
        [-1.0, 1.0, -1.0, -1.0 / sqrt5],
        [-1.0, -1.0, 1.0, -1.0 / sqrt5],
        [0.0, 0.0, 0.0, 4.0 / sqrt5],
    ]
    # Normalize to unit vectors
    for i, n in enumerate(normals):
        norm = math.sqrt(sum(x * x for x in n))
        normals[i] = [x / norm for x in n]
    heights = [0.5] * 5  # Scaled so 0 is in interior
    return normals, heights


def random_hrep(n_facets: int, seed: int) -> tuple[list[list[float]], list[float]]:
    """Generate random H-rep with n_facets facets."""
    rng = random.Random(seed)
    normals = []
    for _ in range(n_facets):
        # Random unit normal
        v = [rng.gauss(0, 1) for _ in range(4)]
        norm = math.sqrt(sum(x * x for x in v))
        normals.append([x / norm for x in v])
    # Heights all positive (0 in interior)
    heights = [rng.uniform(0.5, 2.0) for _ in range(n_facets)]
    return normals, heights


def generate_stub_orbit(
    normals: list[list[float]], capacity: float, seed: int
) -> tuple[list[list[float]], list[float], list[int]]:
    """Generate a plausible stub orbit satisfying invariants.

    Invariants:
    - breakpoints[0] == breakpoints[-1] (closed)
    - breaktimes strictly increasing, ending at capacity
    - len(facet_sequence) == len(breakpoints) - 1
    - No facet appears twice
    """
    rng = random.Random(seed)
    n_facets = len(normals)

    # Choose 3-5 segments (each visiting a unique facet)
    n_segments = min(rng.randint(3, 5), n_facets)
    facet_sequence = rng.sample(range(n_facets), n_segments)

    # Generate random breakpoints on unit sphere (fake, but plausible shape)
    breakpoints = []
    for _ in range(n_segments):
        v = [rng.gauss(0, 1) for _ in range(4)]
        norm = math.sqrt(sum(x * x for x in v))
        breakpoints.append([x / norm for x in v])
    # Close the orbit
    breakpoints.append(breakpoints[0].copy())

    # Generate strictly increasing breaktimes ending at capacity
    raw_times = sorted([rng.uniform(0, 1) for _ in range(n_segments - 1)])
    breaktimes = [0.0] + [t * capacity for t in raw_times] + [capacity]

    return breakpoints, breaktimes, facet_sequence


def is_lagrangian_product(normals: list[list[float]]) -> bool:
    """Check if polytope is a Lagrangian product K1 x K2.

    A Lagrangian product has all normals of form (n_q, 0) or (0, n_p).
    """
    for n in normals:
        q_part = n[0] ** 2 + n[1] ** 2
        p_part = n[2] ** 2 + n[3] ** 2
        # Either q-only or p-only (with tolerance)
        if not (q_part < 1e-10 or p_part < 1e-10):
            return False
    return True


def has_lagrangian_2face(normals: list[list[float]]) -> bool:
    """Check if polytope has any Lagrangian 2-face.

    A 2-face F_ij is Lagrangian iff omega(n_i, n_j) = 0.
    omega(x, y) = x[0]*y[2] + x[1]*y[3] - x[2]*y[0] - x[3]*y[1]
    """
    n = len(normals)
    for i in range(n):
        for j in range(i + 1, n):
            ni, nj = normals[i], normals[j]
            omega = ni[0] * nj[2] + ni[1] * nj[3] - ni[2] * nj[0] - ni[3] * nj[1]
            if abs(omega) < 1e-9:
                return True
    return False


def build_stub_dataframe() -> pd.DataFrame:
    """Build DataFrame with stub polytope data."""
    rows = []

    # Tesseract (ground truth: capacity=4.0, volume=16.0, ratio=0.5)
    normals, heights = tesseract_hrep()
    capacity = 4.0
    volume = 16.0  # 2^4
    bp, bt, fs = generate_stub_orbit(normals, capacity, seed=1)
    rows.append(
        {
            "id": "tesseract",
            "family": "tesseract",
            "facet_count": len(normals),
            "normals": normals,
            "heights": heights,
            "capacity": capacity,
            "volume": volume,
            "systolic_ratio": capacity**2 / (2 * volume),
            "orbit_breakpoints": bp,
            "orbit_breaktimes": bt,
            "orbit_facet_sequence": fs,
            "has_lagrangian_2face": has_lagrangian_2face(normals),
            "is_lagrangian_product": is_lagrangian_product(normals),
        }
    )

    # 4-Simplex (ground truth: capacity=0.25)
    normals, heights = simplex_hrep()
    capacity = 0.25
    volume = 0.1  # Approximate, fake
    bp, bt, fs = generate_stub_orbit(normals, capacity, seed=2)
    rows.append(
        {
            "id": "simplex",
            "family": "simplex",
            "facet_count": len(normals),
            "normals": normals,
            "heights": heights,
            "capacity": capacity,
            "volume": volume,
            "systolic_ratio": capacity**2 / (2 * volume),
            "orbit_breakpoints": bp,
            "orbit_breaktimes": bt,
            "orbit_facet_sequence": fs,
            "has_lagrangian_2face": has_lagrangian_2face(normals),
            "is_lagrangian_product": is_lagrangian_product(normals),
        }
    )

    # Random polytopes
    for i in range(8):
        seed = 100 + i
        n_facets = random.Random(seed).randint(6, 12)
        normals, heights = random_hrep(n_facets, seed)
        # Fake capacity/volume with plausible values
        capacity = random.Random(seed + 1000).uniform(0.5, 5.0)
        volume = random.Random(seed + 2000).uniform(1.0, 20.0)
        bp, bt, fs = generate_stub_orbit(normals, capacity, seed=seed + 3000)
        rows.append(
            {
                "id": f"random-{i:03d}",
                "family": "random",
                "facet_count": len(normals),
                "normals": normals,
                "heights": heights,
                "capacity": capacity,
                "volume": volume,
                "systolic_ratio": capacity**2 / (2 * volume),
                "orbit_breakpoints": bp,
                "orbit_breaktimes": bt,
                "orbit_facet_sequence": fs,
                "has_lagrangian_2face": has_lagrangian_2face(normals),
                "is_lagrangian_product": is_lagrangian_product(normals),
            }
        )

    return pd.DataFrame(rows)


def validate_invariants(df: pd.DataFrame) -> None:
    """Validate that all rows satisfy the invariants from SPEC.md."""
    for idx, row in df.iterrows():
        # capacity > 0
        assert row["capacity"] > 0, f"Row {idx}: capacity must be positive"

        # systolic_ratio = capacity^2 / (2 * volume)
        expected_ratio = row["capacity"] ** 2 / (2 * row["volume"])
        assert abs(row["systolic_ratio"] - expected_ratio) < 1e-10, (
            f"Row {idx}: systolic_ratio mismatch"
        )

        # orbit closed
        bp = row["orbit_breakpoints"]
        assert bp[0] == bp[-1], f"Row {idx}: orbit not closed"

        # breaktimes strictly increasing, ending at capacity
        bt = row["orbit_breaktimes"]
        for i in range(len(bt) - 1):
            assert bt[i] < bt[i + 1], f"Row {idx}: breaktimes not strictly increasing"
        assert abs(bt[-1] - row["capacity"]) < 1e-10, (
            f"Row {idx}: final breaktime != capacity"
        )

        # len(facet_sequence) == len(breakpoints) - 1
        fs = row["orbit_facet_sequence"]
        assert len(fs) == len(bp) - 1, f"Row {idx}: facet_sequence length mismatch"

        # No facet appears twice
        assert len(fs) == len(set(fs)), f"Row {idx}: duplicate facets in orbit"


def main() -> None:
    """Build stub database and save to Parquet."""
    df = build_stub_dataframe()
    validate_invariants(df)

    # Ensure output directory exists
    out_dir = Path(__file__).parents[4] / "data" / "polytope-database"
    out_dir.mkdir(parents=True, exist_ok=True)

    out_path = out_dir / "stub.parquet"
    df.to_parquet(out_path, index=False)
    print(f"Wrote {len(df)} rows to {out_path}")
    print(f"Columns: {list(df.columns)}")
    print(f"Families: {df['family'].value_counts().to_dict()}")


if __name__ == "__main__":
    main()
