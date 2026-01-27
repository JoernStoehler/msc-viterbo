"""4D polytope visualization using Plotly.

Renders 4D polytopes in 3D via radial + stereographic projection.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any, Sequence

import numpy as np
import plotly.graph_objects as go  # pyright: ignore[reportMissingTypeStubs]
from numpy.typing import NDArray

from viterbo.visualization.polytope_geometry import (
    PolytopeGeometry,
    build_polytope_geometry,
    order_face_vertices,
)
from viterbo.visualization.projection import (
    project_4d_points,
    project_4d_segment_to_3d,
)


# Color palette for visualization
VERTEX_COLOR = "#2E86AB"
EDGE_COLOR = "#A23B72"
FACE_COLOR = "#F18F01"
ORBIT_COLOR = "#C73E1D"
FACET_COLORS = [
    "#1f77b4", "#ff7f0e", "#2ca02c", "#d62728", "#9467bd",
    "#8c564b", "#e377c2", "#7f7f7f", "#bcbd22", "#17becf",
]


def create_polytope_mesh(
    geom: PolytopeGeometry,
    *,
    pole: int = 3,
    n_edge_samples: int = 20,
    show_vertices: bool = True,
    show_edges: bool = True,
    show_faces: bool = True,
    face_opacity: float = 0.3,
    vertex_size: float = 6,
    edge_width: float = 2,
) -> list[Any]:
    """Create Plotly traces for a 4D polytope.

    Projects the polytope to 3D and creates traces for vertices, edges,
    and 2-faces.

    Args:
        geom: PolytopeGeometry containing polytope structure
        pole: Stereographic projection pole index
        n_edge_samples: Samples per edge (more = smoother curves)
        show_vertices: Whether to render vertices
        show_edges: Whether to render edges
        show_faces: Whether to render 2-faces
        face_opacity: Opacity for face rendering
        vertex_size: Size of vertex markers
        edge_width: Width of edge lines

    Returns:
        List of Plotly trace objects
    """
    traces: list[Any] = []

    # Project vertices to 3D
    vertices_3d = project_4d_points(geom.vertices, pole=pole)

    # Vertices
    if show_vertices:
        traces.append(
            go.Scatter3d(
                x=vertices_3d[:, 0],
                y=vertices_3d[:, 1],
                z=vertices_3d[:, 2],
                mode="markers",
                marker={"size": vertex_size, "color": VERTEX_COLOR},
                name="Vertices",
                hoverinfo="text",
                text=[f"v{i}" for i in range(len(vertices_3d))],
            )
        )

    # Edges (projected as curved lines)
    if show_edges:
        for i, (v1, v2) in enumerate(geom.edges):
            edge_3d = project_4d_segment_to_3d(
                geom.vertices[v1],
                geom.vertices[v2],
                n_samples=n_edge_samples,
                pole=pole,
            )
            traces.append(
                go.Scatter3d(
                    x=edge_3d[:, 0],
                    y=edge_3d[:, 1],
                    z=edge_3d[:, 2],
                    mode="lines",
                    line={"width": edge_width, "color": EDGE_COLOR},
                    name=f"Edge {i}" if i == 0 else "",
                    showlegend=(i == 0),
                    hoverinfo="skip",
                )
            )

    # 2-faces (as triangulated meshes)
    if show_faces:
        for face_idx, face_vertices in enumerate(geom.faces_2d):
            if len(face_vertices) < 3:
                continue

            # Order vertices cyclically
            ordered = order_face_vertices(geom.vertices, face_vertices)

            # Project face vertices
            face_verts_3d = vertices_3d[ordered]

            # Triangulate (fan from first vertex)
            n = len(ordered)
            triangles_i = []
            triangles_j = []
            triangles_k = []

            for t in range(1, n - 1):
                triangles_i.append(0)
                triangles_j.append(t)
                triangles_k.append(t + 1)

            color = FACET_COLORS[face_idx % len(FACET_COLORS)]

            traces.append(
                go.Mesh3d(
                    x=face_verts_3d[:, 0],
                    y=face_verts_3d[:, 1],
                    z=face_verts_3d[:, 2],
                    i=triangles_i,
                    j=triangles_j,
                    k=triangles_k,
                    color=color,
                    opacity=face_opacity,
                    name=f"Face {face_idx}" if face_idx == 0 else "",
                    showlegend=(face_idx == 0),
                    hoverinfo="skip",
                )
            )

    return traces


def create_orbit_traces(
    breakpoints: Sequence[Sequence[float]] | NDArray[np.floating],
    *,
    pole: int = 3,
    n_segment_samples: int = 30,
    line_width: float = 4,
    show_arrows: bool = True,
    color: str = ORBIT_COLOR,
) -> list[Any]:
    """Create Plotly traces for a Reeb orbit.

    Args:
        breakpoints: Orbit breakpoints as list of 4D points
        pole: Stereographic projection pole
        n_segment_samples: Samples per segment
        line_width: Width of orbit line
        show_arrows: Whether to show direction arrows
        color: Color for the orbit

    Returns:
        List of Plotly trace objects
    """
    breakpoints_arr = np.asarray(breakpoints, dtype=np.float64)
    traces: list[Any] = []

    n_segments = len(breakpoints_arr) - 1

    for seg_idx in range(n_segments):
        start = breakpoints_arr[seg_idx]
        end = breakpoints_arr[seg_idx + 1]

        # Project segment to 3D curve
        curve_3d = project_4d_segment_to_3d(
            start, end, n_samples=n_segment_samples, pole=pole
        )

        traces.append(
            go.Scatter3d(
                x=curve_3d[:, 0],
                y=curve_3d[:, 1],
                z=curve_3d[:, 2],
                mode="lines",
                line={"width": line_width, "color": color},
                name=f"Orbit segment {seg_idx}" if seg_idx == 0 else "",
                showlegend=(seg_idx == 0),
            )
        )

        # Add arrow at midpoint
        if show_arrows:
            mid_idx = n_segment_samples // 2
            if mid_idx + 1 < len(curve_3d):
                # Arrow direction
                arrow_start = curve_3d[mid_idx]
                arrow_end = curve_3d[mid_idx + 1]

                traces.append(
                    go.Cone(
                        x=[arrow_start[0]],
                        y=[arrow_start[1]],
                        z=[arrow_start[2]],
                        u=[arrow_end[0] - arrow_start[0]],
                        v=[arrow_end[1] - arrow_start[1]],
                        w=[arrow_end[2] - arrow_start[2]],
                        colorscale=[[0, color], [1, color]],
                        showscale=False,
                        sizemode="absolute",
                        sizeref=0.15,
                        name="",
                        showlegend=False,
                    )
                )

    # Mark breakpoints
    breakpoints_3d = project_4d_points(breakpoints_arr, pole=pole)
    traces.append(
        go.Scatter3d(
            x=breakpoints_3d[:, 0],
            y=breakpoints_3d[:, 1],
            z=breakpoints_3d[:, 2],
            mode="markers",
            marker={"size": 8, "color": color, "symbol": "diamond"},
            name="Orbit breakpoints",
        )
    )

    return traces


def visualize_polytope_4d(
    normals: Sequence[Sequence[float]] | NDArray[np.floating],
    heights: Sequence[float] | NDArray[np.floating],
    *,
    title: str = "4D Polytope Visualization",
    pole: int = 3,
    show_vertices: bool = True,
    show_edges: bool = True,
    show_faces: bool = True,
    face_opacity: float = 0.3,
    width: int = 800,
    height: int = 700,
) -> go.Figure:
    """Visualize a 4D polytope given H-representation.

    Args:
        normals: Facet normal vectors
        heights: Facet heights
        title: Plot title
        pole: Stereographic projection pole
        show_vertices: Whether to show vertices
        show_edges: Whether to show edges
        show_faces: Whether to show 2-faces
        face_opacity: Face transparency
        width: Figure width in pixels
        height: Figure height in pixels

    Returns:
        Plotly Figure object
    """
    geom = build_polytope_geometry(normals, heights)

    traces = create_polytope_mesh(
        geom,
        pole=pole,
        show_vertices=show_vertices,
        show_edges=show_edges,
        show_faces=show_faces,
        face_opacity=face_opacity,
    )

    fig = go.Figure(data=traces)

    fig.update_layout(
        title=title,
        scene={
            "xaxis_title": "x",
            "yaxis_title": "y",
            "zaxis_title": "z",
            "aspectmode": "data",
        },
        width=width,
        height=height,
        showlegend=True,
        legend={"x": 0.02, "y": 0.98},
    )

    return fig


def visualize_orbit_4d(
    normals: Sequence[Sequence[float]] | NDArray[np.floating],
    heights: Sequence[float] | NDArray[np.floating],
    breakpoints: Sequence[Sequence[float]] | NDArray[np.floating],
    *,
    title: str = "4D Polytope with Reeb Orbit",
    pole: int = 3,
    face_opacity: float = 0.2,
    width: int = 800,
    height: int = 700,
) -> go.Figure:
    """Visualize a 4D polytope with a Reeb orbit.

    Args:
        normals: Facet normal vectors
        heights: Facet heights
        breakpoints: Orbit breakpoints (4D coordinates)
        title: Plot title
        pole: Stereographic projection pole
        face_opacity: Face transparency
        width: Figure width
        height: Figure height

    Returns:
        Plotly Figure object
    """
    geom = build_polytope_geometry(normals, heights)

    # Polytope traces
    traces = create_polytope_mesh(
        geom,
        pole=pole,
        show_vertices=True,
        show_edges=True,
        show_faces=True,
        face_opacity=face_opacity,
    )

    # Orbit traces
    orbit_traces = create_orbit_traces(breakpoints, pole=pole)
    traces.extend(orbit_traces)

    fig = go.Figure(data=traces)

    fig.update_layout(
        title=title,
        scene={
            "xaxis_title": "x",
            "yaxis_title": "y",
            "zaxis_title": "z",
            "aspectmode": "data",
        },
        width=width,
        height=height,
        showlegend=True,
        legend={"x": 0.02, "y": 0.98},
    )

    return fig


def load_hko_polytope() -> tuple[list[list[float]], list[float], list[list[float]]]:
    """Load the HKO 2024 counterexample polytope data.

    Returns:
        Tuple of (normals, heights, orbit_breakpoints)
    """
    # Find the data file
    # Path: src/viterbo/visualization/ -> src/viterbo/ -> src/ -> python_viterbo/ -> data/
    this_dir = Path(__file__).parent
    data_path = (
        this_dir.parent.parent.parent
        / "data"
        / "counterexample-hko"
        / "hko2024.json"
    )

    with open(data_path) as f:
        data = json.load(f)

    normals = [facet["normal"] for facet in data["hrep"]["facets"]]
    heights = [facet["height"] for facet in data["hrep"]["facets"]]
    breakpoints = data["minimum_orbit"]["breakpoints"]

    return normals, heights, breakpoints


def save_visualization(
    fig: go.Figure,
    output_path: Path,
    *,
    include_plotlyjs: bool = True,
) -> None:
    """Save visualization to HTML file.

    Args:
        fig: Plotly figure
        output_path: Output file path
        include_plotlyjs: Whether to include plotly.js in the HTML
    """
    fig.write_html(
        output_path,
        include_plotlyjs=include_plotlyjs,
        full_html=True,
    )


def save_visualization_json(
    fig: go.Figure,
    output_path: Path,
) -> None:
    """Save visualization as JSON (for embedding in web pages).

    Args:
        fig: Plotly figure
        output_path: Output file path (should end in .json)
    """
    payload = {
        "data": fig.to_plotly_json()["data"],
        "layout": fig.to_plotly_json()["layout"],
        "config": {"displaylogo": False, "responsive": True},
    }

    output_path.write_text(json.dumps(payload, indent=2))


def main() -> None:
    """Generate example visualization of HKO counterexample."""
    print("Loading HKO 2024 counterexample polytope...")
    normals, heights, breakpoints = load_hko_polytope()

    print("Creating visualization...")
    fig = visualize_orbit_4d(
        normals,
        heights,
        breakpoints,
        title="HKO 2024 Counterexample: Pentagon × Pentagon (4D → 3D)",
    )

    # Determine output paths
    this_dir = Path(__file__).parent
    output_dir = (
        this_dir.parent.parent.parent
        / "data"
        / "4d-visualization"
    )
    output_dir.mkdir(parents=True, exist_ok=True)

    html_path = output_dir / "hko-polytope.html"
    json_path = output_dir / "hko-polytope.json"

    save_visualization(fig, html_path)
    save_visualization_json(fig, json_path)

    print(f"Saved interactive HTML: {html_path}")
    print(f"Saved JSON spec: {json_path}")


if __name__ == "__main__":
    main()
