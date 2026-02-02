"""Stage 1: Build synthetic data.

This stage demonstrates:
- Loading config from JSON
- Generating reproducible random data (seeded RNG)
- Writing output to data/<label>/

Usage:
    uv run python -m viterbo.experiments.example_pipeline.stage_build
    uv run python -m viterbo.experiments.example_pipeline.stage_build --config config/example-pipeline/default.json
"""

from __future__ import annotations

import argparse
import json
import random
from pathlib import Path


def load_config(path: Path) -> dict:
    """Load JSON config file."""
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def generate_data(size: int, seed: int) -> list[float]:
    """Generate list of random floats.

    Args:
        size: Number of elements to generate.
        seed: RNG seed for reproducibility.

    Returns:
        List of random floats in [0, 1).
    """
    rng = random.Random(seed)
    return [rng.random() for _ in range(size)]


def main(config_path: str = "config/example-pipeline/default.json") -> None:
    """Build synthetic data and save to output directory."""
    cfg = load_config(Path(config_path))

    # Ensure output directory exists
    out_dir = Path(cfg["output_dir"])
    out_dir.mkdir(parents=True, exist_ok=True)

    # Generate data for each size
    datasets = {}
    for size in cfg["sizes"]:
        datasets[str(size)] = generate_data(size, cfg["seed"])

    # Save to JSON (for this example; real experiments might use Parquet)
    out_path = out_dir / "synthetic_data.json"
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(datasets, f)

    print(f"Wrote synthetic data to {out_path}")
    print(f"Sizes: {list(datasets.keys())}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Build synthetic data")
    parser.add_argument(
        "--config",
        default="config/example-pipeline/default.json",
        help="Path to config file",
    )
    args = parser.parse_args()
    main(args.config)
