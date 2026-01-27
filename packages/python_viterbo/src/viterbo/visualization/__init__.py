"""4D polytope visualization utilities.

This module provides tools for visualizing 4D polytopes by projecting them
to 3D space and rendering with Plotly.

Projection pipeline:
1. Radial projection to S³: v ∈ ∂K → v/|v| ∈ S³
2. Stereographic projection S³ → R³
3. 3D rendering via Plotly to 2D screen
"""

from __future__ import annotations

from viterbo.visualization.projection import (
    radial_project_to_s3,
    stereographic_s3_to_r3,
    project_4d_to_3d,
    project_4d_points,
)
from viterbo.visualization.polytope_geometry import (
    hrep_to_vertices,
    extract_faces,
    PolytopeGeometry,
)
from viterbo.visualization.vis_4d import (
    visualize_polytope_4d,
    visualize_orbit_4d,
    create_polytope_mesh,
)

__all__ = [
    # Projection
    "radial_project_to_s3",
    "stereographic_s3_to_r3",
    "project_4d_to_3d",
    "project_4d_points",
    # Polytope geometry
    "hrep_to_vertices",
    "extract_faces",
    "PolytopeGeometry",
    # Visualization
    "visualize_polytope_4d",
    "visualize_orbit_4d",
    "create_polytope_mesh",
]
