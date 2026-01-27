"""Plot the HK&O orbit projections onto both factors.

Creates a two-panel figure showing:
- Left: Projection onto q-plane (K factor)
- Right: Projection onto p-plane (T factor)

The minimum action orbit is shown with numbered segments. Each segment
appears as a line in one factor and a point in the other, alternating.

Usage:
    uv run python -m viterbo.experiments.counterexample_hko.stage_plot
"""

from __future__ import annotations

import json
import math
from pathlib import Path

import matplotlib.pyplot as plt
import matplotlib.patches as mpatches
from matplotlib.collections import LineCollection


def load_data(data_path: Path) -> dict:
    """Load the HK&O JSON data."""
    with data_path.open("r", encoding="utf-8") as f:
        return json.load(f)


def regular_polygon_vertices(
    n: int, circumradius: float = 1.0, phase: float = 0.0
) -> list[tuple[float, float]]:
    """Return CCW vertices of a regular n-gon."""
    return [
        (
            circumradius * math.cos(phase + 2 * math.pi * k / n),
            circumradius * math.sin(phase + 2 * math.pi * k / n),
        )
        for k in range(n)
    ]


def plot_polygon(ax, vertices: list[tuple[float, float]], **kwargs) -> None:
    """Plot a closed polygon."""
    xs = [v[0] for v in vertices] + [vertices[0][0]]
    ys = [v[1] for v in vertices] + [vertices[0][1]]
    ax.plot(xs, ys, **kwargs)


def plot_orbit_projections(data: dict, out_path: Path) -> None:
    """Create the two-panel orbit projection plot.

    Left panel: q-plane (K factor)
    Right panel: p-plane (T factor)
    """
    orbit = data["minimum_orbit"]
    breakpoints = orbit["breakpoints"]
    facet_labels = orbit["facet_labels"]

    # Pentagon vertices
    verts_k = regular_polygon_vertices(5, circumradius=1.0, phase=0.0)
    verts_t = regular_polygon_vertices(5, circumradius=1.0, phase=-math.pi / 2)

    fig, (ax_q, ax_p) = plt.subplots(1, 2, figsize=(12, 5.5))

    # Colors for segments
    cmap = plt.get_cmap("tab10")
    n_segments = len(facet_labels)

    # Draw pentagons
    plot_polygon(ax_q, verts_k, color="steelblue", linewidth=2, label="K (q-plane)")
    plot_polygon(ax_p, verts_t, color="firebrick", linewidth=2, label="T (p-plane)")

    # Track which segments are lines vs points in each projection
    q_lines = []  # Segments that are lines in q-plane
    q_points = []  # Segments that are points in q-plane
    p_lines = []  # Segments that are lines in p-plane
    p_points = []  # Segments that are points in p-plane

    for i in range(n_segments):
        bp_start = breakpoints[i]
        bp_end = breakpoints[i + 1]
        label = facet_labels[i]
        color = cmap(i % 10)

        # q-plane projection
        q_start = (bp_start[0], bp_start[1])
        q_end = (bp_end[0], bp_end[1])

        # p-plane projection
        p_start = (bp_start[2], bp_start[3])
        p_end = (bp_end[2], bp_end[3])

        # Check if this segment is a line or point in each projection
        q_dist = math.hypot(q_end[0] - q_start[0], q_end[1] - q_start[1])
        p_dist = math.hypot(p_end[0] - p_start[0], p_end[1] - p_start[1])

        if q_dist > 0.01:
            q_lines.append((i, q_start, q_end, color, label))
        else:
            q_points.append((i, q_start, color, label))

        if p_dist > 0.01:
            p_lines.append((i, p_start, p_end, color, label))
        else:
            p_points.append((i, p_start, color, label))

    # Draw lines in q-plane
    for seg_i, start, end, color, label in q_lines:
        ax_q.annotate(
            "",
            xy=end,
            xytext=start,
            arrowprops=dict(arrowstyle="->", color=color, lw=2),
        )
        # Number at midpoint
        mid = ((start[0] + end[0]) / 2, (start[1] + end[1]) / 2)
        ax_q.annotate(
            str(seg_i + 1),
            mid,
            fontsize=10,
            fontweight="bold",
            color="white",
            ha="center",
            va="center",
            bbox=dict(boxstyle="circle,pad=0.2", fc=color, ec="none"),
        )

    # Draw points in q-plane (segments that are stationary in q)
    for seg_i, pos, color, label in q_points:
        ax_q.plot(pos[0], pos[1], "o", color=color, markersize=10, zorder=5)
        ax_q.annotate(
            str(seg_i + 1),
            pos,
            fontsize=8,
            fontweight="bold",
            color="white",
            ha="center",
            va="center",
            zorder=6,
        )

    # Draw lines in p-plane
    for seg_i, start, end, color, label in p_lines:
        ax_p.annotate(
            "",
            xy=end,
            xytext=start,
            arrowprops=dict(arrowstyle="->", color=color, lw=2),
        )
        mid = ((start[0] + end[0]) / 2, (start[1] + end[1]) / 2)
        ax_p.annotate(
            str(seg_i + 1),
            mid,
            fontsize=10,
            fontweight="bold",
            color="white",
            ha="center",
            va="center",
            bbox=dict(boxstyle="circle,pad=0.2", fc=color, ec="none"),
        )

    # Draw points in p-plane
    for seg_i, pos, color, label in p_points:
        ax_p.plot(pos[0], pos[1], "o", color=color, markersize=10, zorder=5)
        ax_p.annotate(
            str(seg_i + 1),
            pos,
            fontsize=8,
            fontweight="bold",
            color="white",
            ha="center",
            va="center",
            zorder=6,
        )

    # Styling
    for ax, title in [(ax_q, "K (q-plane)"), (ax_p, "T (p-plane)")]:
        ax.set_aspect("equal")
        ax.set_title(title, fontsize=14)
        ax.grid(True, alpha=0.3)
        ax.set_xlim(-1.3, 1.3)
        ax.set_ylim(-1.3, 1.3)
        ax.axhline(0, color="gray", linewidth=0.5)
        ax.axvline(0, color="gray", linewidth=0.5)

    ax_q.set_xlabel(r"$q_1$", fontsize=12)
    ax_q.set_ylabel(r"$q_2$", fontsize=12)
    ax_p.set_xlabel(r"$p_1$", fontsize=12)
    ax_p.set_ylabel(r"$p_2$", fontsize=12)

    # Add legend explaining the orbit structure
    fig.suptitle(
        "HK&O 2024 Counterexample: Minimum Action Orbit Projections",
        fontsize=14,
        fontweight="bold",
    )

    # Add text annotation about orbit structure
    fig.text(
        0.5,
        0.02,
        "Numbered segments: line in one factor, point in the other (alternating). "
        f"Systolic ratio = {data['systolic_ratio']:.4f} > 1",
        ha="center",
        fontsize=10,
        style="italic",
    )

    plt.tight_layout(rect=(0.0, 0.05, 1.0, 0.95))

    out_path.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(out_path, dpi=150, bbox_inches="tight")
    plt.close(fig)

    print(f"Saved plot to {out_path}")


def main(data_path: str | None = None, assets_dir: str | None = None) -> None:
    """Load data and create orbit projection plot."""
    pkg_root = Path(__file__).parents[4]

    resolved_data_path: Path
    if data_path is None:
        resolved_data_path = pkg_root / "data" / "counterexample-hko" / "hko2024.json"
    else:
        resolved_data_path = Path(data_path)

    resolved_assets_dir: Path
    if assets_dir is None:
        resolved_assets_dir = (
            pkg_root.parent / "latex_viterbo" / "assets" / "counterexample-hko"
        )
    else:
        resolved_assets_dir = Path(assets_dir)

    if not resolved_data_path.exists():
        raise FileNotFoundError(
            f"{resolved_data_path} not found. Run stage_build first."
        )

    data = load_data(resolved_data_path)
    out_path = resolved_assets_dir / "orbit-projections.png"
    plot_orbit_projections(data, out_path)


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Plot HK&O orbit projections")
    parser.add_argument("--data-path", help="Path to hko2024.json")
    parser.add_argument("--assets-dir", help="Output directory for plot")
    args = parser.parse_args()
    main(args.data_path, args.assets_dir)
