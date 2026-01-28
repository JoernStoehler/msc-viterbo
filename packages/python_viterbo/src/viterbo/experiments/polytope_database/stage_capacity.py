"""Stage 3: Add capacity and systolic ratio calculations.

This stage reads polytopes_with_volume.json and adds capacity calculations
using the Rust FFI tube algorithm for non-Lagrangian polytopes.

BLOCKED: Can be implemented now with stubs, but real capacities require:
    - tube_capacity_hrep() FFI (already implemented)
    - systolic_ratio() helper (TODO: needs to be exposed via FFI)

Usage:
    uv run python -m viterbo.experiments.polytope_database.stage_capacity

Input:
    data/polytope-database/polytopes_with_volume.json

Output:
    data/polytope-database/complete.json
"""

from __future__ import annotations

import json
import math
import random
from pathlib import Path


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


def add_capacities(polytopes: list[dict]) -> list[dict]:
    """Add capacity, systolic_ratio, and orbit data to polytopes.

    TODO: Once tube_capacity_hrep() FFI is ready and working, implement as:
        from viterbo import ffi
        for p in polytopes:
            if not p["is_lagrangian_product"]:
                result = ffi.tube_capacity_hrep(p["normals"], p["heights"])
                p["capacity"] = result.capacity
                p["orbit_breakpoints"] = result.breakpoints
                p["orbit_breaktimes"] = result.breaktimes
                p["orbit_facet_sequence"] = result.facet_sequence
            else:
                # Use billiard algorithm for Lagrangian products
                result = ffi.billiard_capacity_hrep(p["normals"], p["heights"])
                p["capacity"] = result.capacity
                # ... (orbit data)

            # Compute systolic ratio
            p["systolic_ratio"] = p["capacity"] ** 2 / (2 * p["volume"])
    """
    # Stub: use fake capacities and orbits for now
    for p in polytopes:
        # Ground truth capacities for known polytopes
        if p["id"] == "tesseract":
            capacity = 4.0
        elif p["id"] == "simplex":
            capacity = 0.25
        elif p["id"] == "cross-polytope":
            capacity = 1.0
        elif p["id"] == "24-cell":
            capacity = 2.0
        else:
            # Random polytopes: fake capacities
            seed = int(p["id"].split("-")[1]) + 1000
            capacity = random.Random(seed).uniform(0.5, 5.0)

        p["capacity"] = capacity
        p["systolic_ratio"] = capacity**2 / (2 * p["volume"])

        # Generate stub orbit
        orbit_seed = hash(p["id"]) % (2**31)
        bp, bt, fs = generate_stub_orbit(p["normals"], capacity, orbit_seed)
        p["orbit_breakpoints"] = bp
        p["orbit_breaktimes"] = bt
        p["orbit_facet_sequence"] = fs

    return polytopes


def main() -> None:
    """Add capacities to polytopes and save to JSON."""
    data_dir = Path(__file__).parents[4] / "data" / "polytope-database"
    in_path = data_dir / "polytopes_with_volume.json"
    out_path = data_dir / "complete.json"

    # Load polytopes
    with open(in_path) as f:
        polytopes = json.load(f)

    # Add capacities
    polytopes = add_capacities(polytopes)

    # Save
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(polytopes, f, indent=2)

    print(f"Added capacities to {len(polytopes)} polytopes")
    print(f"Saved to {out_path}")
    print()
    print("NOTE: Using stub/fake capacities and orbits until FFI is fully integrated.")


if __name__ == "__main__":
    main()
