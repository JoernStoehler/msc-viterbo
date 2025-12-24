"""Build facet data and lightweight assets for the HK&O 2024 counterexample.

Creates:
- data/counterexamples/hk-o-2024/facets.json with normals (4D) and heights
- data/counterexamples/hk-o-2024/summary.json with capacity/volume/sys values
- assets/counterexamples/hko-2024/polygons.png showing K and T in their planes

Conventions: coordinates (q1, q2, p1, p2); J(q, p) = (-p, q).
"""

from __future__ import annotations

import json
import math
from dataclasses import dataclass
from pathlib import Path
from typing import List, Tuple

import matplotlib.pyplot as plt


def repo_root() -> Path:
    """Locate repo root by walking up to the .git directory."""
    here = Path(__file__).resolve()
    for anc in here.parents:
        if (anc / ".git").exists():
            return anc
    raise RuntimeError("Could not find repo root (.git)")


REPO_ROOT = repo_root()
DATA_DIR = (
    REPO_ROOT / "packages" / "python_viterbo" / "data" / "counterexamples" / "hk-o-2024"
)
ASSET_DIR = (
    REPO_ROOT / "packages" / "latex_viterbo" / "assets" / "counterexamples" / "hko-2024"
)


@dataclass
class Facet:
    normal4: Tuple[float, float, float, float]
    height: float


def regular_polygon_vertices(
    n: int, radius: float = 1.0, phase: float = 0.0
) -> List[Tuple[float, float]]:
    """Return CCW vertices of a regular n-gon on the circle of given radius."""
    return [
        (
            radius * math.cos(phase + 2 * math.pi * k / n),
            radius * math.sin(phase + 2 * math.pi * k / n),
        )
        for k in range(n)
    ]


def edge_normals(
    vertices: List[Tuple[float, float]],
) -> List[Tuple[float, float, float]]:
    """Compute outward unit normals and heights for a convex CCW polygon with origin inside."""
    normals_heights: List[Tuple[float, float, float]] = []
    m = len(vertices)
    for i in range(m):
        a = vertices[i]
        b = vertices[(i + 1) % m]
        dx, dy = b[0] - a[0], b[1] - a[1]
        # For CCW order, outward normal is tangent rotated clockwise.
        nx, ny = dy, -dx
        norm = math.hypot(nx, ny)
        nx, ny = nx / norm, ny / norm
        # Height is support value n·a (same along the edge).
        h = nx * a[0] + ny * a[1]
        normals_heights.append((nx, ny, h))
    return normals_heights


def build_facets() -> List[Facet]:
    """Construct 4D facet normals/heights for K x T with T rotated by -pi/2."""
    verts_k = regular_polygon_vertices(5, radius=1.0, phase=0.0)
    verts_t = regular_polygon_vertices(5, radius=1.0, phase=-math.pi / 2)
    facets: List[Facet] = []
    for nx, ny, h in edge_normals(verts_k):
        facets.append(Facet(normal4=(nx, ny, 0.0, 0.0), height=h))
    for nx, ny, h in edge_normals(verts_t):
        facets.append(Facet(normal4=(0.0, 0.0, nx, ny), height=h))
    return facets


def capacity_values() -> Tuple[float, float, float]:
    """Return (c_EHZ, volume, systolic ratio) for the pentagon product."""
    cap = 2 * math.cos(math.pi / 10) * (1 + math.cos(math.pi / 5))
    area = 0.5 * 5 * math.sin(2 * math.pi / 5)
    vol = area * area
    sys = cap * cap / (2 * vol)
    return cap, vol, sys


def write_json(facets: List[Facet]) -> None:
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    normals = [f.normal4 for f in facets]
    heights = [f.height for f in facets]
    cap, vol, sys = capacity_values()
    facets_path = DATA_DIR / "facets.json"
    summary_path = DATA_DIR / "summary.json"
    facets_path.write_text(
        json.dumps(
            {
                "normals": normals,
                "heights": heights,
                "meta": {
                    "name": "HK&O 2024 pentagon product",
                    "convention": "(q1,q2,p1,p2), J(q,p)=(-p,q)",
                    "polygon": {"type": "regular pentagon", "circumradius": 1.0},
                    "rotation_T_rad": -math.pi / 2,
                    "source": "Haim-Kislev & Ostrover 2024, Proposition 1",
                },
            },
            indent=2,
        )
    )
    summary_path.write_text(
        json.dumps(
            {
                "capacity": cap,
                "volume": vol,
                "systolic_ratio": sys,
                "formula": {
                    "capacity": "2*cos(pi/10)*(1+cos(pi/5))",
                    "volume": "area(K)*area(T), area = (5/2)*sin(2pi/5)",
                    "systolic_ratio": "(sqrt(5)+3)/5",
                },
            },
            indent=2,
        )
    )


def plot_polygons() -> None:
    ASSET_DIR.mkdir(parents=True, exist_ok=True)
    verts_k = regular_polygon_vertices(5, radius=1.0, phase=0.0)
    verts_t = regular_polygon_vertices(5, radius=1.0, phase=-math.pi / 2)
    fig, ax = plt.subplots(figsize=(4.5, 4.5))

    def close(poly):
        return poly + [poly[0]]

    kx, ky = zip(*close(verts_k))
    tx, ty = zip(*close(verts_t))
    ax.plot(kx, ky, "-o", label="K (q-plane)", color="#1f77b4")
    ax.plot(tx, ty, "-o", label="T (p-plane rotated)", color="#d62728")
    ax.set_aspect("equal", "box")
    ax.grid(True, alpha=0.3)
    ax.legend()
    ax.set_title("HK&O 2024 pentagon factors (projections)")
    fig.tight_layout()
    fig.savefig(ASSET_DIR / "polygons.png", dpi=200)
    plt.close(fig)


def main() -> None:
    facets = build_facets()
    write_json(facets)
    plot_polygons()
    print(f"Wrote {DATA_DIR}/facets.json and summary.json")
    print(f"Wrote {ASSET_DIR}/polygons.png")


if __name__ == "__main__":
    main()
