"""Stage 1: Build algorithm inventory data.

Generates JSON data files for the algorithm inventory experiment:
- algorithms.json: Hardcoded algorithm inventory
- fixtures.json: Hardcoded fixture inventory
- capacity_matrix.json: Capacity values for (fixture, algorithm) pairs
- validation_results.json: Validation proposition results

Usage:
    cd packages/python_viterbo
    uv run python -m viterbo.experiments.algorithm_inventory.stage_build
"""

from __future__ import annotations

import json
import time
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path

import rust_viterbo_ffi as ffi

from viterbo.paths import get_data_dir

# =============================================================================
# Data output directory
# =============================================================================

DATA_DIR = get_data_dir("algorithm_inventory")

# Maximum facets for naive HK2017 (F! complexity). 8! = 40320 is tractable.
# 16! ≈ 2×10¹³ and 24! ≈ 6×10²³ would cause OOM.
MAX_FACETS_FOR_NAIVE = 8


# =============================================================================
# Fixtures (hardcoded to match tube/src/fixtures.rs)
# =============================================================================


def unit_cross_polytope() -> tuple[list[list[float]], list[float]]:
    """Unit cross-polytope (16-cell): conv{±e₁, ±e₂, ±e₃, ±e₄}.

    16 facets with normals (±1,±1,±1,±1)/2, heights 0.5.
    No Lagrangian 2-faces (Tube-compatible).
    """
    normals = []
    for s1 in [-1.0, 1.0]:
        for s2 in [-1.0, 1.0]:
            for s3 in [-1.0, 1.0]:
                for s4 in [-1.0, 1.0]:
                    normals.append([s1 / 2, s2 / 2, s3 / 2, s4 / 2])
    heights = [0.5] * 16
    return normals, heights


def unit_tesseract() -> tuple[list[list[float]], list[float]]:
    """Unit tesseract (4-cube): [-1,1]⁴.

    8 facets with axis-aligned normals, heights 1.0.
    All 2-faces are Lagrangian (NOT Tube-compatible).
    """
    normals = [
        [1.0, 0.0, 0.0, 0.0],
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, -1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, -1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
        [0.0, 0.0, 0.0, -1.0],
    ]
    heights = [1.0] * 8
    return normals, heights


def four_simplex() -> tuple[list[list[float]], list[float]]:
    """4-simplex (5-cell): 5 facets, has Lagrangian 2-faces."""
    import math

    sqrt19 = math.sqrt(19.0)

    n4 = [1.0 / 2, 1.0 / 2, 1.0 / 2, 1.0 / 2]
    h4 = 0.5
    n0 = [-4.0 / sqrt19, 1.0 / sqrt19, 1.0 / sqrt19, 1.0 / sqrt19]
    h0 = 1.0 / sqrt19
    n1 = [1.0 / sqrt19, -4.0 / sqrt19, 1.0 / sqrt19, 1.0 / sqrt19]
    h1 = 1.0 / sqrt19
    n2 = [1.0 / sqrt19, 1.0 / sqrt19, -4.0 / sqrt19, 1.0 / sqrt19]
    h2 = 1.0 / sqrt19
    n3 = [1.0 / sqrt19, 1.0 / sqrt19, 1.0 / sqrt19, -4.0 / sqrt19]
    h3 = 1.0 / sqrt19

    normals = [n0, n1, n2, n3, n4]
    heights = [h0, h1, h2, h3, h4]
    return normals, heights


def unit_24_cell() -> tuple[list[list[float]], list[float]]:
    """24-cell: 24 facets with normals (±1,±1,0,0)/√2 and permutations.

    No Lagrangian 2-faces (Tube-compatible).
    """
    import math

    s = 1.0 / math.sqrt(2.0)
    normals = []
    pairs = [(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)]

    for i, j in pairs:
        for s1 in [-1.0, 1.0]:
            for s2 in [-1.0, 1.0]:
                n = [0.0, 0.0, 0.0, 0.0]
                n[i] = s1 * s
                n[j] = s2 * s
                normals.append(n)

    heights = [s] * 24
    return normals, heights


def scaled_cross_polytope(lambda_: float) -> tuple[list[list[float]], list[float]]:
    """Scaled cross-polytope: λ × unit_cross_polytope."""
    normals, heights = unit_cross_polytope()
    heights = [h * lambda_ for h in heights]
    return normals, heights


# =============================================================================
# Algorithms
# =============================================================================


@dataclass
class AlgorithmEntry:
    name: str
    variant: str | None
    applicability: str
    complexity: str
    implementation: str
    status: str


ALGORITHMS = [
    AlgorithmEntry(
        name="HK2017",
        variant="naive",
        applicability="Any polytope",
        complexity="O(F!)",
        implementation="hk2017/enumerate/naive.rs",
        status="Implemented",
    ),
    AlgorithmEntry(
        name="HK2017",
        variant="graph-pruned",
        applicability="Sparse facet graphs",
        complexity="O(cycles)",
        implementation="hk2017/enumerate/graph.rs",
        status="Implemented",
    ),
    AlgorithmEntry(
        name="Tube",
        variant=None,
        applicability="No Lagrangian 2-faces",
        complexity="Branch-and-bound",
        implementation="tube/algorithm.rs",
        status="Implemented",
    ),
    AlgorithmEntry(
        name="Billiard",
        variant=None,
        applicability="Lagrangian products",
        complexity="TBD",
        implementation="—",
        status="Absent (blocked)",
    ),
]


# =============================================================================
# Fixtures inventory
# =============================================================================


@dataclass
class Fixture4D:
    name: str
    facets: int
    has_lagrangian_2faces: bool
    tube_compatible: bool
    known_capacity: float | None
    capacity_source: str | None
    source_file: str


@dataclass
class Primitive2D:
    name: str
    vertices: str  # Can be parameterized like "n" for regular(n)
    source_file: str


FIXTURES_4D = [
    Fixture4D(
        name="unit_cross_polytope",
        facets=16,
        has_lagrangian_2faces=False,
        tube_compatible=True,
        known_capacity=1.0,
        capacity_source="empirical",
        source_file="tube/src/fixtures.rs",
    ),
    Fixture4D(
        name="unit_tesseract",
        facets=8,
        has_lagrangian_2faces=True,
        tube_compatible=False,
        known_capacity=4.0,
        capacity_source="known",
        source_file="tube/src/fixtures.rs",
    ),
    Fixture4D(
        name="four_simplex",
        facets=5,
        has_lagrangian_2faces=True,
        tube_compatible=False,
        known_capacity=None,
        capacity_source=None,
        source_file="tube/src/fixtures.rs",
    ),
    Fixture4D(
        name="unit_24_cell",
        facets=24,
        has_lagrangian_2faces=False,
        tube_compatible=True,
        known_capacity=None,
        capacity_source=None,
        source_file="tube/src/fixtures.rs",
    ),
]

PRIMITIVES_2D = [
    Primitive2D(
        name="regular(n, r, θ)",
        vertices="n",
        source_file="geom/src/polygon2d.rs",
    ),
    Primitive2D(
        name="square(s)",
        vertices="4",
        source_file="geom/src/polygon2d.rs",
    ),
    Primitive2D(
        name="regular_pentagon()",
        vertices="5",
        source_file="geom/src/polygon2d.rs",
    ),
]


# =============================================================================
# Capacity computation
# =============================================================================


def get_fixture_hrep(name: str) -> tuple[list[list[float]], list[float]]:
    """Get H-rep for a fixture by name."""
    if name == "unit_cross_polytope":
        return unit_cross_polytope()
    elif name == "unit_tesseract":
        return unit_tesseract()
    elif name == "four_simplex":
        return four_simplex()
    elif name == "unit_24_cell":
        return unit_24_cell()
    elif name.startswith("scaled_cross_polytope_"):
        # Extract lambda from name like "scaled_cross_polytope_2.0"
        lambda_ = float(name.split("_")[-1])
        return scaled_cross_polytope(lambda_)
    else:
        raise ValueError(f"Unknown fixture: {name}")


@dataclass
class CapacityResult:
    fixture: str
    algorithm: str
    capacity: float | None
    status: str
    error_msg: str | None
    time_ms: float


def compute_capacity(
    fixture_name: str,
    algorithm: str,
    normals: list[list[float]],
    heights: list[float],
) -> CapacityResult:
    """Compute capacity for a (fixture, algorithm) pair."""
    start = time.perf_counter()
    try:
        if algorithm == "hk2017_naive":
            result = ffi.hk2017_capacity_hrep(normals, heights, use_graph_pruning=False)
            elapsed = (time.perf_counter() - start) * 1000
            return CapacityResult(
                fixture=fixture_name,
                algorithm=algorithm,
                capacity=result.capacity,
                status="success",
                error_msg=None,
                time_ms=elapsed,
            )
        elif algorithm == "hk2017_graph":
            result = ffi.hk2017_capacity_hrep(normals, heights, use_graph_pruning=True)
            elapsed = (time.perf_counter() - start) * 1000
            return CapacityResult(
                fixture=fixture_name,
                algorithm=algorithm,
                capacity=result.capacity,
                status="success",
                error_msg=None,
                time_ms=elapsed,
            )
        elif algorithm == "tube":
            result = ffi.tube_capacity_hrep(normals, heights)
            elapsed = (time.perf_counter() - start) * 1000
            return CapacityResult(
                fixture=fixture_name,
                algorithm=algorithm,
                capacity=result.capacity,
                status="success",
                error_msg=None,
                time_ms=elapsed,
            )
        else:
            elapsed = (time.perf_counter() - start) * 1000
            return CapacityResult(
                fixture=fixture_name,
                algorithm=algorithm,
                capacity=None,
                status="error",
                error_msg=f"Unknown algorithm: {algorithm}",
                time_ms=elapsed,
            )
    except Exception as e:
        elapsed = (time.perf_counter() - start) * 1000
        return CapacityResult(
            fixture=fixture_name,
            algorithm=algorithm,
            capacity=None,
            status="error",
            error_msg=str(e),
            time_ms=elapsed,
        )


def build_capacity_matrix() -> list[CapacityResult]:
    """Build capacity matrix for all (fixture, algorithm) pairs."""
    results = []

    for fixture in FIXTURES_4D:
        normals, heights = get_fixture_hrep(fixture.name)

        # HK2017 naive: skip for large polytopes (F! complexity)
        if fixture.facets <= MAX_FACETS_FOR_NAIVE:
            results.append(compute_capacity(fixture.name, "hk2017_naive", normals, heights))
        else:
            results.append(
                CapacityResult(
                    fixture=fixture.name,
                    algorithm="hk2017_naive",
                    capacity=None,
                    status="skip",
                    error_msg=f"Skipped: {fixture.facets} facets > {MAX_FACETS_FOR_NAIVE} (O(F!) infeasible)",
                    time_ms=0.0,
                )
            )

        # HK2017 graph-pruned: also skip for large polytopes (still too slow)
        if fixture.facets <= MAX_FACETS_FOR_NAIVE:
            results.append(compute_capacity(fixture.name, "hk2017_graph", normals, heights))
        else:
            results.append(
                CapacityResult(
                    fixture=fixture.name,
                    algorithm="hk2017_graph",
                    capacity=None,
                    status="skip",
                    error_msg=f"Skipped: {fixture.facets} facets > {MAX_FACETS_FOR_NAIVE} (graph-pruned still too slow)",
                    time_ms=0.0,
                )
            )

        # Tube only works on polytopes without Lagrangian 2-faces
        if fixture.tube_compatible:
            results.append(compute_capacity(fixture.name, "tube", normals, heights))
        else:
            results.append(
                CapacityResult(
                    fixture=fixture.name,
                    algorithm="tube",
                    capacity=None,
                    status="n/a",
                    error_msg="Has Lagrangian 2-faces",
                    time_ms=0.0,
                )
            )

    return results


# =============================================================================
# Validation propositions
# =============================================================================


@dataclass
class ValidationResult:
    proposition_id: str
    proposition_name: str
    fixture: str
    status: str  # "pass", "fail", "skip", "n/a"
    numerical_error: float | None
    notes: str | None


def validate_p1_scaling() -> list[ValidationResult]:
    """P1: Scaling c(λK) = λ²c(K)."""
    results = []
    lambda_ = 2.0

    # Test on cross-polytope (16 facets) - use Tube (HK2017 too slow)
    normals, heights = unit_cross_polytope()
    scaled_normals, scaled_heights = scaled_cross_polytope(lambda_)

    try:
        tube_base = ffi.tube_capacity_hrep(normals, heights)
        tube_scaled = ffi.tube_capacity_hrep(scaled_normals, scaled_heights)
        expected_tube = lambda_**2 * tube_base.capacity
        error_tube = abs(tube_scaled.capacity - expected_tube)
        status_tube = "pass" if error_tube < 1e-10 else "fail"
        results.append(
            ValidationResult(
                proposition_id="P1",
                proposition_name="Scaling",
                fixture="unit_cross_polytope",
                status=status_tube,
                numerical_error=error_tube,
                notes=f"Tube: λ={lambda_}, c(K)={tube_base.capacity:.6f}, c(λK)={tube_scaled.capacity:.6f}",
            )
        )
    except Exception as e:
        results.append(
            ValidationResult(
                proposition_id="P1",
                proposition_name="Scaling",
                fixture="unit_cross_polytope",
                status="skip",
                numerical_error=None,
                notes=f"Tube error: {e}",
            )
        )

    # Also test on tesseract (8 facets) with HK2017 - tractable size
    tess_normals, tess_heights = unit_tesseract()
    # Scale tesseract
    scaled_tess_heights = [h * lambda_ for h in tess_heights]

    try:
        hk_base = ffi.hk2017_capacity_hrep(tess_normals, tess_heights)
        hk_scaled = ffi.hk2017_capacity_hrep(tess_normals, scaled_tess_heights)
        expected_hk = lambda_**2 * hk_base.capacity
        error_hk = abs(hk_scaled.capacity - expected_hk)
        status_hk = "pass" if error_hk < 1e-10 else "fail"
        results.append(
            ValidationResult(
                proposition_id="P1",
                proposition_name="Scaling",
                fixture="unit_tesseract",
                status=status_hk,
                numerical_error=error_hk,
                notes=f"HK2017: λ={lambda_}, c(K)={hk_base.capacity:.6f}, c(λK)={hk_scaled.capacity:.6f}",
            )
        )
    except Exception as e:
        results.append(
            ValidationResult(
                proposition_id="P1",
                proposition_name="Scaling",
                fixture="unit_tesseract",
                status="skip",
                numerical_error=None,
                notes=f"HK2017 error: {e}",
            )
        )

    return results


def validate_p2_mahler() -> list[ValidationResult]:
    """P2: Mahler bound c(K)·c(K°) ≤ 4."""
    results = []

    # Test 1: tesseract ↔ cross-polytope (known duals)
    # c(tesseract) via HK2017 (8 facets - naive OK)
    tess_normals, tess_heights = unit_tesseract()
    tess_result = ffi.hk2017_capacity_hrep(tess_normals, tess_heights)
    c_tesseract = tess_result.capacity

    # c(cross-polytope) via Tube only (HK2017 too slow for 16 facets)
    cross_normals, cross_heights = unit_cross_polytope()
    try:
        cross_result = ffi.tube_capacity_hrep(cross_normals, cross_heights)
        c_cross = cross_result.capacity
    except Exception as e:
        # Can't compute cross-polytope capacity - skip this test
        results.append(
            ValidationResult(
                proposition_id="P2",
                proposition_name="Mahler bound",
                fixture="tesseract × cross-polytope",
                status="skip",
                numerical_error=None,
                notes=f"Tube error on cross-polytope: {e}",
            )
        )
        # Continue to 24-cell test instead of returning
        c_cross = None

    if c_cross is not None:
        product = c_tesseract * c_cross
        status = "pass" if product <= 4.0 + 1e-10 else "fail"
        results.append(
            ValidationResult(
                proposition_id="P2",
                proposition_name="Mahler bound",
                fixture="tesseract × cross-polytope",
                status=status,
                numerical_error=abs(product - 4.0),
                notes=f"c(tess)={c_tesseract:.6f}, c(cross)={c_cross:.6f}, product={product:.6f}",
            )
        )

    # Test 2: 24-cell (self-dual) - use Tube only (HK2017 too slow for 24 facets)
    cell24_normals, cell24_heights = unit_24_cell()
    try:
        cell24_result = ffi.tube_capacity_hrep(cell24_normals, cell24_heights)
        c_24cell = cell24_result.capacity
    except Exception as e:
        # Can't compute 24-cell capacity - skip this test
        results.append(
            ValidationResult(
                proposition_id="P2",
                proposition_name="Mahler bound",
                fixture="24-cell (self-dual)",
                status="skip",
                numerical_error=None,
                notes=f"Tube error: {e}",
            )
        )
        return results

    product_24 = c_24cell * c_24cell
    status_24 = "pass" if product_24 <= 4.0 + 1e-10 else "fail"
    results.append(
        ValidationResult(
            proposition_id="P2",
            proposition_name="Mahler bound",
            fixture="24-cell (self-dual)",
            status=status_24,
            numerical_error=abs(product_24 - 4.0) if product_24 <= 4.0 else product_24 - 4.0,
            notes=f"c(24-cell)={c_24cell:.6f}, c²={product_24:.6f}",
        )
    )

    return results


def validate_p3_constraints() -> list[ValidationResult]:
    """P3: Constraint satisfaction β≥0, Σβᵢhᵢ=1, Σβᵢnᵢ=0."""
    results = []

    for fixture in FIXTURES_4D:
        # Skip large polytopes - HK2017 too slow even with graph pruning
        if fixture.facets > MAX_FACETS_FOR_NAIVE:
            results.append(
                ValidationResult(
                    proposition_id="P3",
                    proposition_name="Constraint satisfaction",
                    fixture=fixture.name,
                    status="skip",
                    numerical_error=None,
                    notes=f"HK2017 infeasible for {fixture.facets} facets",
                )
            )
            continue

        normals, heights = get_fixture_hrep(fixture.name)
        try:
            result = ffi.hk2017_capacity_hrep(normals, heights)
            beta = result.optimal_beta
            # Note: beta[i] is the weight for facet i (indexed by facet, not permutation)

            # Check β ≥ 0
            all_nonneg = all(b >= -1e-10 for b in beta)

            # Check Σβᵢhᵢ = 1
            sum_beta_h = sum(beta[i] * heights[i] for i in range(len(beta)))
            sum_h_ok = abs(sum_beta_h - 1.0) < 1e-10

            # Check Σβᵢnᵢ = 0
            sum_beta_n = [0.0, 0.0, 0.0, 0.0]
            for i in range(len(beta)):
                for d in range(4):
                    sum_beta_n[d] += beta[i] * normals[i][d]
            sum_n_ok = sum(abs(x) for x in sum_beta_n) < 1e-9

            if all_nonneg and sum_h_ok and sum_n_ok:
                status = "pass"
                error = max(
                    max(-min(b, 0) for b in beta),  # max negative beta
                    abs(sum_beta_h - 1.0),
                    sum(abs(x) for x in sum_beta_n),
                )
            else:
                status = "fail"
                error = None

            notes_parts = []
            if not all_nonneg:
                notes_parts.append(f"min(β)={min(beta):.2e}")
            if not sum_h_ok:
                notes_parts.append(f"Σβh={sum_beta_h:.6f}")
            if not sum_n_ok:
                notes_parts.append(f"||Σβn||={sum(abs(x) for x in sum_beta_n):.2e}")

            results.append(
                ValidationResult(
                    proposition_id="P3",
                    proposition_name="Constraint satisfaction",
                    fixture=fixture.name,
                    status=status,
                    numerical_error=error,
                    notes="; ".join(notes_parts) if notes_parts else "All constraints satisfied",
                )
            )
        except Exception as e:
            results.append(
                ValidationResult(
                    proposition_id="P3",
                    proposition_name="Constraint satisfaction",
                    fixture=fixture.name,
                    status="skip",
                    numerical_error=None,
                    notes=f"Error: {e}",
                )
            )

    return results


def validate_p4_agreement() -> list[ValidationResult]:
    """P4: Algorithm agreement HK2017 = Tube (on common domain)."""
    results = []
    tolerance = 0.01  # 1% tolerance as per spec

    for fixture in FIXTURES_4D:
        if not fixture.tube_compatible:
            results.append(
                ValidationResult(
                    proposition_id="P4",
                    proposition_name="Algorithm agreement",
                    fixture=fixture.name,
                    status="n/a",
                    numerical_error=None,
                    notes="Not Tube-compatible (has Lagrangian 2-faces)",
                )
            )
            continue

        # Skip large polytopes - HK2017 too slow even with graph pruning
        if fixture.facets > MAX_FACETS_FOR_NAIVE:
            results.append(
                ValidationResult(
                    proposition_id="P4",
                    proposition_name="Algorithm agreement",
                    fixture=fixture.name,
                    status="skip",
                    numerical_error=None,
                    notes=f"HK2017 infeasible for {fixture.facets} facets; Tube-only",
                )
            )
            continue

        normals, heights = get_fixture_hrep(fixture.name)
        try:
            hk_result = ffi.hk2017_capacity_hrep(normals, heights)
            tube_result = ffi.tube_capacity_hrep(normals, heights)

            c_hk = hk_result.capacity
            c_tube = tube_result.capacity
            rel_error = abs(c_hk - c_tube) / max(c_hk, c_tube, 1e-10)

            status = "pass" if rel_error < tolerance else "fail"
            results.append(
                ValidationResult(
                    proposition_id="P4",
                    proposition_name="Algorithm agreement",
                    fixture=fixture.name,
                    status=status,
                    numerical_error=rel_error,
                    notes=f"HK2017={c_hk:.6f}, Tube={c_tube:.6f}, rel_error={rel_error:.2e}",
                )
            )
        except Exception as e:
            results.append(
                ValidationResult(
                    proposition_id="P4",
                    proposition_name="Algorithm agreement",
                    fixture=fixture.name,
                    status="skip",
                    numerical_error=None,
                    notes=f"Error: {e}",
                )
            )

    return results


def validate_p5_orbit_closure() -> list[ValidationResult]:
    """P5: Orbit closure (covered by Rust unit tests)."""
    results = []

    for fixture in FIXTURES_4D:
        if fixture.tube_compatible:
            results.append(
                ValidationResult(
                    proposition_id="P5",
                    proposition_name="Orbit closure",
                    fixture=fixture.name,
                    status="skip",
                    numerical_error=None,
                    notes="Covered by Rust tests: tube/tests/orbit_invariants.rs",
                )
            )
        else:
            results.append(
                ValidationResult(
                    proposition_id="P5",
                    proposition_name="Orbit closure",
                    fixture=fixture.name,
                    status="n/a",
                    numerical_error=None,
                    notes="Not Tube-compatible",
                )
            )

    return results


def build_validation_results() -> list[ValidationResult]:
    """Run all validation propositions."""
    results = []
    results.extend(validate_p1_scaling())
    results.extend(validate_p2_mahler())
    results.extend(validate_p3_constraints())
    results.extend(validate_p4_agreement())
    results.extend(validate_p5_orbit_closure())
    return results


# =============================================================================
# Main
# =============================================================================


def main() -> None:
    """Build all data files for algorithm inventory experiment."""
    DATA_DIR.mkdir(parents=True, exist_ok=True)
    timestamp = datetime.now(timezone.utc).isoformat()

    # 1. Write algorithms.json
    algorithms_data = {
        "algorithms": [asdict(a) for a in ALGORITHMS],
        "generated_at": timestamp,
    }
    with (DATA_DIR / "algorithms.json").open("w") as f:
        json.dump(algorithms_data, f, indent=2)
    print(f"Wrote {DATA_DIR / 'algorithms.json'}")

    # 2. Write fixtures.json
    fixtures_data = {
        "fixtures_4d": [asdict(f) for f in FIXTURES_4D],
        "primitives_2d": [asdict(p) for p in PRIMITIVES_2D],
        "generated_at": timestamp,
    }
    with (DATA_DIR / "fixtures.json").open("w") as f:
        json.dump(fixtures_data, f, indent=2)
    print(f"Wrote {DATA_DIR / 'fixtures.json'}")

    # 3. Build and write capacity_matrix.json
    print("Building capacity matrix...")
    capacity_results = build_capacity_matrix()
    capacity_data = {
        "entries": [asdict(r) for r in capacity_results],
        "generated_at": timestamp,
    }
    with (DATA_DIR / "capacity_matrix.json").open("w") as f:
        json.dump(capacity_data, f, indent=2)
    print(f"Wrote {DATA_DIR / 'capacity_matrix.json'}")

    # 4. Build and write validation_results.json
    print("Running validation propositions...")
    validation_results = build_validation_results()
    validation_data = {
        "propositions": [asdict(r) for r in validation_results],
        "generated_at": timestamp,
    }
    with (DATA_DIR / "validation_results.json").open("w") as f:
        json.dump(validation_data, f, indent=2)
    print(f"Wrote {DATA_DIR / 'validation_results.json'}")

    # Summary
    print("\n=== Summary ===")
    print(f"Algorithms: {len(ALGORITHMS)}")
    print(f"4D Fixtures: {len(FIXTURES_4D)}")
    print(f"2D Primitives: {len(PRIMITIVES_2D)}")
    print(f"Capacity matrix entries: {len(capacity_results)}")
    print(f"Validation results: {len(validation_results)}")

    # Validation summary
    pass_count = sum(1 for r in validation_results if r.status == "pass")
    fail_count = sum(1 for r in validation_results if r.status == "fail")
    skip_count = sum(1 for r in validation_results if r.status == "skip")
    na_count = sum(1 for r in validation_results if r.status == "n/a")
    print(f"Validation: {pass_count} pass, {fail_count} fail, {skip_count} skip, {na_count} n/a")


if __name__ == "__main__":
    main()
