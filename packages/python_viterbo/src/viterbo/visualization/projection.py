"""Projection utilities for 4D → 3D visualization.

Projection pipeline:
1. Radial projection to S³: v ∈ R⁴ → v/|v| ∈ S³
2. Stereographic projection S³ → R³

The stereographic projection maps S³ (3-sphere in R⁴) to R³.
It is conformal (angle-preserving) but curves straight lines.
"""

from __future__ import annotations

import numpy as np
from numpy.typing import NDArray


def radial_project_to_s3(
    v: NDArray[np.floating],
    *,
    epsilon: float = 1e-12,
) -> NDArray[np.floating]:
    """Project a 4D point onto S³ via radial projection.

    Maps v ∈ R⁴ to v/|v| ∈ S³.

    Args:
        v: 4D point as shape (4,) array
        epsilon: Minimum norm to avoid division by zero

    Returns:
        Unit 4D vector on S³

    Raises:
        ValueError: If point is too close to origin
    """
    norm = np.linalg.norm(v)
    if norm < epsilon:
        raise ValueError(f"Point too close to origin (norm={norm:.2e})")
    return v / norm


def stereographic_s3_to_r3(
    v: NDArray[np.floating],
    *,
    pole: int = 3,
    epsilon: float = 1e-10,
) -> NDArray[np.floating]:
    """Stereographic projection from S³ to R³.

    Projects from the 3-sphere in R⁴ to R³. The projection is done from
    a pole (by default, the positive w-axis pole at (0,0,0,1)).

    For a point (x, y, z, w) on S³, the stereographic projection is:
        (x/(1-w), y/(1-w), z/(1-w))

    This is conformal (preserves angles) but maps circles to circles/lines.

    Args:
        v: Point on S³ as shape (4,) array (must have |v| ≈ 1)
        pole: Index of coordinate to project from (default 3 = w-axis)
        epsilon: Tolerance for near-pole detection

    Returns:
        3D point in R³

    Note:
        Points very close to the pole map to infinity and are returned
        as a large finite value.
    """
    # Get the pole coordinate
    pole_coord = v[pole]

    # Handle near-pole case (maps to "infinity")
    if 1 - pole_coord < epsilon:
        # Return a large but finite point in the direction away from pole
        scale = 1e6
        coords_3d = np.array([v[i] for i in range(4) if i != pole])
        return coords_3d * scale

    # Standard stereographic formula
    denom = 1 - pole_coord
    coords_3d = np.array([v[i] / denom for i in range(4) if i != pole])

    return coords_3d


def project_4d_to_3d(
    v: NDArray[np.floating],
    *,
    pole: int = 3,
    epsilon: float = 1e-12,
) -> NDArray[np.floating]:
    """Combined radial + stereographic projection: R⁴ → R³.

    Applies the full projection pipeline:
    1. Radial projection to S³
    2. Stereographic projection to R³

    Args:
        v: 4D point as shape (4,) array
        pole: Stereographic pole index (default 3 = w-axis)
        epsilon: Tolerance for near-zero norms

    Returns:
        3D point in R³
    """
    v_s3 = radial_project_to_s3(v, epsilon=epsilon)
    return stereographic_s3_to_r3(v_s3, pole=pole, epsilon=epsilon)


def project_4d_points(
    points: NDArray[np.floating],
    *,
    pole: int = 3,
    epsilon: float = 1e-12,
) -> NDArray[np.floating]:
    """Project multiple 4D points to 3D via radial+stereographic projection.

    Args:
        points: Array of shape (n, 4) containing n 4D points
        pole: Stereographic pole index (default 3 = w-axis)
        epsilon: Tolerance for near-zero norms

    Returns:
        Array of shape (n, 3) containing projected 3D points
    """
    n = points.shape[0]
    result = np.zeros((n, 3), dtype=points.dtype)

    for i in range(n):
        result[i] = project_4d_to_3d(points[i], pole=pole, epsilon=epsilon)

    return result


def interpolate_4d_segment(
    start: NDArray[np.floating],
    end: NDArray[np.floating],
    n_samples: int = 20,
) -> NDArray[np.floating]:
    """Interpolate along a 4D line segment.

    Creates sample points along the straight line from start to end.
    After projection, this will become a curved arc.

    Args:
        start: Starting 4D point
        end: Ending 4D point
        n_samples: Number of sample points (including endpoints)

    Returns:
        Array of shape (n_samples, 4) with interpolated points
    """
    t = np.linspace(0, 1, n_samples)[:, np.newaxis]
    return start + t * (end - start)


def project_4d_segment_to_3d(
    start: NDArray[np.floating],
    end: NDArray[np.floating],
    *,
    n_samples: int = 20,
    pole: int = 3,
) -> NDArray[np.floating]:
    """Project a 4D line segment to a 3D curve.

    Since stereographic projection curves straight lines, we interpolate
    along the segment and project each point individually.

    Args:
        start: Starting 4D point
        end: Ending 4D point
        n_samples: Number of sample points for the curve
        pole: Stereographic pole index

    Returns:
        Array of shape (n_samples, 3) with the projected curve
    """
    segment_4d = interpolate_4d_segment(start, end, n_samples)
    return project_4d_points(segment_4d, pole=pole)
