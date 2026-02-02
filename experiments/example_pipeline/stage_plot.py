"""Stage 3: Plot analysis results.

This stage demonstrates:
- Reading analysis results
- Creating publication-quality plots
- Saving to thesis assets directory

Usage:
    uv run python -m viterbo.experiments.example_pipeline.stage_plot
"""

from __future__ import annotations

import argparse
import json
from pathlib import Path

import matplotlib.pyplot as plt


def plot_growth_curve(results: dict[str, dict], out_path: Path) -> None:
    """Plot sum of squares vs input size.

    Args:
        results: Dict mapping size (string) to analysis results.
        out_path: Where to save the plot.
    """
    sizes = []
    sos_values = []

    for size_str, r in sorted(results.items(), key=lambda x: int(x[0])):
        sizes.append(r["size"])
        sos_values.append(r["sum_of_squares"])

    fig, ax = plt.subplots(figsize=(8, 6))
    ax.plot(sizes, sos_values, "o-", linewidth=2, markersize=8)
    ax.set_xlabel("Input Size", fontsize=12)
    ax.set_ylabel("Sum of Squares", fontsize=12)
    ax.set_title("Growth of Sum of Squares", fontsize=14)
    ax.set_xscale("log")
    ax.set_yscale("log")
    ax.grid(True, alpha=0.3)

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, dpi=150, bbox_inches="tight")
    plt.close(fig)

    print(f"Saved plot to {out_path}")


def main(
    data_dir: str = "data/example-pipeline",
    assets_dir: str = "../latex_viterbo/assets/example-pipeline",
) -> None:
    """Load results and create plot."""
    results_path = Path(data_dir) / "results.json"

    if not results_path.exists():
        raise FileNotFoundError(f"{results_path} not found. Run stage_analyze first.")

    with results_path.open("r", encoding="utf-8") as f:
        results = json.load(f)

    out_path = Path(assets_dir) / "growth-curve.png"
    plot_growth_curve(results, out_path)


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Plot analysis results")
    parser.add_argument(
        "--data-dir", default="data/example-pipeline", help="Path to data directory"
    )
    parser.add_argument(
        "--assets-dir",
        default="../latex_viterbo/assets/example-pipeline",
        help="Path to thesis assets directory",
    )
    args = parser.parse_args()
    main(args.data_dir, args.assets_dir)
