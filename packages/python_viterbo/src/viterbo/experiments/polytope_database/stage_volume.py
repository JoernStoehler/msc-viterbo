"""Stage 2: Add volume calculations to polytopes.

This stage reads polytopes.json and adds volume calculations using the Rust FFI.

BLOCKED: Waiting for volume_hrep() FFI implementation (TODO in issue #31).

Usage:
    uv run python -m viterbo.experiments.polytope_database.stage_volume

Input:
    data/polytope-database/polytopes.json

Output:
    data/polytope-database/polytopes_with_volume.json
"""

from __future__ import annotations

import json
from pathlib import Path


def add_volumes(polytopes: list[dict]) -> list[dict]:
    """Add volume calculations to polytopes.

    TODO: Once volume FFI is ready, implement as:
        from viterbo import ffi
        for p in polytopes:
            p["volume"] = ffi.volume_hrep(p["normals"], p["heights"])
    """
    # Stub: use fake volumes for now (matching stage_build.py behavior)
    import random

    for p in polytopes:
        if p["id"] == "tesseract":
            p["volume"] = 16.0  # Ground truth: 2^4
        elif p["id"] == "simplex":
            p["volume"] = 0.1  # Approximate, fake
        elif p["id"] == "cross-polytope":
            p["volume"] = 2.0  # Approximate, fake
        elif p["id"] == "24-cell":
            p["volume"] = 4.0  # Approximate, fake
        else:
            # Random polytopes: fake volumes
            seed = int(p["id"].split("-")[1]) + 2000
            p["volume"] = random.Random(seed).uniform(1.0, 20.0)

    return polytopes


def main() -> None:
    """Add volumes to polytopes and save to JSON."""
    data_dir = Path(__file__).parents[4] / "data" / "polytope-database"
    in_path = data_dir / "polytopes.json"
    out_path = data_dir / "polytopes_with_volume.json"

    # Load polytopes
    with open(in_path) as f:
        polytopes = json.load(f)

    # Add volumes
    polytopes = add_volumes(polytopes)

    # Save
    out_path.parent.mkdir(parents=True, exist_ok=True)
    with open(out_path, "w") as f:
        json.dump(polytopes, f, indent=2)

    print(f"Added volumes to {len(polytopes)} polytopes")
    print(f"Saved to {out_path}")
    print()
    print("NOTE: Using stub/fake volumes until volume_hrep() FFI is implemented.")


if __name__ == "__main__":
    main()
