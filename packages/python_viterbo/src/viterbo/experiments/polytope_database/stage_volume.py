"""Stage 2: Add volume calculations to polytopes.

This stage reads polytopes.json and adds volume calculations using the Rust FFI.

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
from typing import Any

try:
    import rust_viterbo_ffi as ffi
except ImportError:
    ffi: Any = None


def add_volumes(polytopes: list[dict]) -> list[dict]:
    """Add volume calculations to polytopes using FFI."""
    if ffi is None:
        raise ImportError(
            "rust_viterbo_ffi is not installed. Build it with:\n"
            "  cd packages/python_viterbo\n"
            "  uv run maturin develop --manifest-path ../rust_viterbo/ffi/Cargo.toml"
        )

    for p in polytopes:
        # Compute volume using FFI
        p["volume"] = ffi.volume_hrep(p["normals"], p["heights"])

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

    # Show some sample volumes
    for p in polytopes[:4]:
        print(f"  {p['id']:20s}: volume = {p['volume']:.6f}")


if __name__ == "__main__":
    main()
