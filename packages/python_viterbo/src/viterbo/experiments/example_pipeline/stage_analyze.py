"""Stage 2: Analyze synthetic data.

This stage demonstrates:
- Reading output from previous stage
- Computing derived quantities
- Writing analysis results

Usage:
    uv run python -m viterbo.experiments.example_pipeline.stage_analyze
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path


def sum_of_squares(data: list[float]) -> float:
    """Compute sum of squares."""
    return sum(x * x for x in data)


def analyze(datasets: dict[str, list[float]]) -> dict[str, dict]:
    """Analyze each dataset.

    Args:
        datasets: Dict mapping size (as string) to list of floats.

    Returns:
        Dict mapping size to analysis results.
    """
    results = {}
    for size_str, data in datasets.items():
        size = int(size_str)
        sos = sum_of_squares(data)
        results[size_str] = {
            "size": size,
            "sum_of_squares": sos,
            "sos_per_element": sos / size if size > 0 else 0,
        }
    return results


def main(data_dir: str = "data/example-pipeline") -> None:
    """Load synthetic data, analyze, and save results."""
    data_path = Path(data_dir) / "synthetic_data.json"

    if not data_path.exists():
        raise FileNotFoundError(f"{data_path} not found. Run stage_build first.")

    with data_path.open("r", encoding="utf-8") as f:
        datasets = json.load(f)

    results = analyze(datasets)

    out_path = Path(data_dir) / "results.json"
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(results, f, indent=2)

    print(f"Wrote analysis results to {out_path}")
    for size_str, r in sorted(results.items(), key=lambda x: int(x[0])):
        print(f"  Size {r['size']}: sum_of_squares = {r['sum_of_squares']:.4f}")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Analyze synthetic data")
    parser.add_argument(
        "--data-dir", default="data/example-pipeline", help="Path to data directory"
    )
    args = parser.parse_args()
    main(args.data_dir)
