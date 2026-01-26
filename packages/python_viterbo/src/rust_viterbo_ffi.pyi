from __future__ import annotations

from typing import Sequence, TypedDict

Vector4 = tuple[float, float, float, float]

class WitnessOrbit(TypedDict):
    breakpoints: list[Vector4]
    facet_sequence: list[int]
    segment_times: list[float]

class Diagnostics(TypedDict):
    nodes_explored: int
    nodes_pruned_empty: int
    nodes_pruned_action: int
    nodes_pruned_rotation: int
    best_action_found: float
    lagrangian: str | None
    perturbation: str

class CapacityResult(TypedDict):
    capacity: float
    diagnostics: Diagnostics
    witness: WitnessOrbit | None

def symplectic_form_4d(a: Vector4, b: Vector4) -> float: ...
def tube_capacity_hrep(
    normals: Sequence[Vector4], heights: Sequence[float], *, unit_tol: float = ...
) -> CapacityResult:
    """Compute EHZ capacity using the Tube (CH2021) algorithm."""
    ...

def billiard_capacity_hrep(
    normals: Sequence[Vector4], heights: Sequence[float], *, unit_tol: float = ...
) -> CapacityResult:
    """Compute EHZ capacity using the Minkowski billiard algorithm.

    Only works for Lagrangian products K = K₁ × K₂.
    """
    ...

def hk2019_capacity_hrep(
    normals: Sequence[Vector4], heights: Sequence[float], *, unit_tol: float = ...
) -> float:
    """LEGACY: Compute EHZ capacity using the HK2017 algorithm.

    This is an alias for hk2017_capacity_hrep for backwards compatibility.
    Returns just the capacity value (not the full result object).
    """
    ...

class Hk2017Result:
    """Result of HK2017 capacity computation."""

    capacity: float
    q_max: float
    optimal_permutation: list[int]
    optimal_beta: list[float]
    permutations_evaluated: int
    permutations_rejected: int

def hk2017_capacity_hrep(
    normals: Sequence[Vector4],
    heights: Sequence[float],
    use_graph_pruning: bool = False,
) -> Hk2017Result:
    """Compute EHZ capacity using the HK2017 combinatorial formula.

    Args:
        normals: Unit outward normal vectors for each facet.
        heights: Signed distances from origin to each facet (must be positive).
        use_graph_pruning: If True, use graph-based cycle enumeration (faster).
                          If False (default), use naive enumeration.

    Returns:
        Hk2017Result with capacity, optimal permutation, and statistics.
    """
    ...
