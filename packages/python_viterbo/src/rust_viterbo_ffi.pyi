"""Type stubs for rust_viterbo_ffi.

This module provides Python bindings to Rust implementations of EHZ capacity
algorithms for convex polytopes.
"""

from __future__ import annotations

from typing import Sequence

Vector4 = tuple[float, float, float, float] | list[float]

class Hk2017Result:
    """Result of HK2017 capacity computation."""

    @property
    def capacity(self) -> float:
        """The computed EHZ capacity."""
        ...

    @property
    def q_max(self) -> float:
        """The maximum Q value achieved (capacity = 4/q_max)."""
        ...

    @property
    def optimal_permutation(self) -> list[int]:
        """Indices of facets in the optimal cyclic ordering."""
        ...

    @property
    def optimal_beta(self) -> list[float]:
        """The beta values (time spent on each facet) at the optimum."""
        ...

    @property
    def permutations_evaluated(self) -> int:
        """Number of permutations evaluated."""
        ...

    @property
    def permutations_rejected(self) -> int:
        """Number of permutations rejected by pruning criteria."""
        ...

def hk2017_capacity_hrep(
    normals: Sequence[Vector4],
    heights: Sequence[float],
    use_graph_pruning: bool = False,
) -> Hk2017Result:
    """Compute EHZ capacity using the HK2017 combinatorial formula.

    Implements the algorithm from Haim-Kislev's paper "On the Symplectic Size
    of Convex Polytopes" (arXiv:1712.03494, published GAFA 2019).

    Args:
        normals: Unit outward normal vectors for each facet.
        heights: Signed distances from origin to each facet (must be positive).
        use_graph_pruning: If True, use graph-based cycle enumeration (faster).
                          If False (default), use naive enumeration.

    Returns:
        Hk2017Result with capacity, optimal permutation, and statistics.

    Raises:
        ValueError: If the polytope is invalid (non-unit normals, non-positive
            heights, mismatched lengths, etc.).

    Warning:
        This implementation assumes the global maximum of Q occurs at an
        interior point. If the true maximum is on the boundary, the result
        may be incorrect.
    """
    ...

def symplectic_form_4d(a: Vector4, b: Vector4) -> float:
    """Compute the symplectic form ω(a, b) in R⁴.

    The standard symplectic form is:
        ω(x, y) = x₁y₃ + x₂y₄ - x₃y₁ - x₄y₂

    where x = (q₁, q₂, p₁, p₂) and y = (q₁', q₂', p₁', p₂').

    Args:
        a: First vector [q₁, q₂, p₁, p₂].
        b: Second vector [q₁', q₂', p₁', p₂'].

    Returns:
        The symplectic form value ω(a, b).
    """
    ...

class TubeResult:
    """Result of tube capacity computation."""

    @property
    def capacity(self) -> float:
        """The computed EHZ capacity."""
        ...

    @property
    def tubes_explored(self) -> int:
        """Number of tubes explored in branch-and-bound."""
        ...

    @property
    def tubes_pruned(self) -> int:
        """Number of tubes pruned by bounds."""
        ...

def tube_capacity_hrep(
    normals: Sequence[Vector4],
    heights: Sequence[float],
) -> TubeResult:
    """Compute EHZ capacity using the tube algorithm for non-Lagrangian polytopes.

    The tube algorithm uses Reeb dynamics and branch-and-bound search over
    "tubes" of trajectories. It requires all 2-faces to be non-Lagrangian.

    Args:
        normals: Unit outward normal vectors for each facet, as [x, y, z, w].
        heights: Signed distances from origin to each facet (must be positive).

    Returns:
        TubeResult with capacity and orbit information.

    Raises:
        ValueError: If polytope has Lagrangian 2-faces or other issues.
    """
    ...

def volume_hrep(
    normals: Sequence[Vector4],
    heights: Sequence[float],
) -> float:
    """Compute the 4D volume of a polytope from its H-representation.

    Uses QHull to enumerate vertices and compute the convex hull volume.

    Args:
        normals: Unit outward normal vectors for each facet, as [x, y, z, w].
        heights: Signed distances from origin to each facet (must be positive).

    Returns:
        The 4-dimensional Lebesgue volume of the polytope.

    Raises:
        ValueError: If the polytope is invalid or volume computation fails.

    Example:
        >>> # Tesseract [-1, 1]⁴ has volume 2⁴ = 16
        >>> normals = [
        ...     [1, 0, 0, 0], [-1, 0, 0, 0],
        ...     [0, 1, 0, 0], [0, -1, 0, 0],
        ...     [0, 0, 1, 0], [0, 0, -1, 0],
        ...     [0, 0, 0, 1], [0, 0, 0, -1],
        ... ]
        >>> heights = [1.0] * 8
        >>> volume_hrep(normals, heights)
        16.0
    """
    ...

def systolic_ratio(capacity: float, volume: float) -> float:
    """Compute the systolic ratio from capacity and volume.

    The systolic ratio is defined as:
        sys(K) = c_EHZ(K)² / (2 · vol(K))

    For balls and cylinders of radius r, sys = 1.

    Args:
        capacity: The EHZ capacity (must be > 0).
        volume: The 4D volume (must be > 0).

    Returns:
        The systolic ratio, a dimensionless positive number.

    Raises:
        ValueError: If capacity or volume is non-positive or NaN.

    Example:
        >>> # For a tesseract: c = 4.0, vol = 16.0
        >>> systolic_ratio(4.0, 16.0)
        0.5
    """
    ...
