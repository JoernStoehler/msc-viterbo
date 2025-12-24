"""Generate placeholder interactive + static plots for the docs site."""

from __future__ import annotations

import json
import math
from pathlib import Path
from typing import Tuple

import matplotlib.pyplot as plt
import plotly.graph_objects as go

__all__ = ["save_dummy_plot", "build_dummy_figure"]


def build_dummy_samples() -> tuple[list[float], list[float]]:
    samples = [step / 10 for step in range(0, 63)]
    y_values = [math.sin(sample) * math.exp(-0.03 * sample) for sample in samples]
    return samples, y_values


def build_dummy_figure(samples: list[float], y_values: list[float]) -> go.Figure:
    """Return a deterministic Plotly figure used for smoke tests."""

    figure = go.Figure()
    figure.add_trace(
        go.Scatter(
            x=samples,
            y=y_values,
            mode="lines+markers",
            name="dummy signal",
            line={"color": "#4C6EF5", "width": 3},
            marker={"size": 6},
        )
    )
    figure.update_layout(
        title="Demo Symplectic Section",
        xaxis_title="t",
        yaxis_title="f(t)",
        template="plotly_white",
        margin={"l": 40, "r": 20, "t": 45, "b": 40},
    )
    return figure


def save_static_plot(
    samples: list[float], y_values: list[float], png_path: Path
) -> None:
    """Render the static PNG version via matplotlib."""
    fig, ax = plt.subplots(figsize=(6, 4))
    ax.plot(samples, y_values, color="#4C6EF5", linewidth=2.2, marker="o", markersize=3)
    ax.set_title("Demo Symplectic Section")
    ax.set_xlabel("t")
    ax.set_ylabel("f(t)")
    ax.grid(True, alpha=0.2)
    fig.tight_layout()
    fig.savefig(png_path, dpi=220)
    plt.close(fig)


def default_output_dir() -> Path:
    repo_root = Path(__file__).resolve().parents[4]
    return repo_root / "packages" / "latex_viterbo" / "assets" / "demo"


def save_dummy_plot(output_dir: Path | None = None) -> Tuple[Path, Path]:
    """Generate the dummy plot and persist both interactive + static variants."""
    target_dir = (output_dir or default_output_dir()).resolve()
    target_dir.mkdir(parents=True, exist_ok=True)

    samples, y_values = build_dummy_samples()
    figure = build_dummy_figure(samples, y_values)
    payload = {
        "data": figure.to_plotly_json()["data"],
        "layout": figure.to_plotly_json()["layout"],
        "config": {"displaylogo": False, "responsive": True},
    }

    json_path = target_dir / "dummy-plot.json"
    png_path = target_dir / "dummy-plot.png"

    json_path.write_text(json.dumps(payload, indent=2))
    save_static_plot(samples, y_values, png_path)
    return json_path, png_path


def main() -> None:
    json_path, png_path = save_dummy_plot()
    repo_root = Path(__file__).resolve().parents[4]
    try:
        rel_json = json_path.relative_to(repo_root)
        rel_png = png_path.relative_to(repo_root)
    except ValueError:
        rel_json, rel_png = json_path, png_path
    print(f"Wrote interactive spec to {rel_json}")
    print(f"Wrote static image to      {rel_png}")


if __name__ == "__main__":
    main()
