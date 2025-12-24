from __future__ import annotations

from typing import Sequence

Vector4 = tuple[float, float, float, float]

def symplectic_form_4d(a: Vector4, b: Vector4) -> float: ...
def tube_capacity_hrep(
    normals: Sequence[Vector4],
    heights: Sequence[float],
    *,
    eps_lagr: float = ...,
    eps_perturb: float = ...,
    seed: int = ...,
    unit_tol: float = ...,
) -> object: ...
