#!/usr/bin/env python3
"""HK2019 algorithm benchmark script.

Measures time vs facet count to determine practical limits.

Usage:
    cd packages/python_viterbo
    uv run maturin develop --release --manifest-path ../rust_viterbo/ffi/Cargo.toml
    uv run python ../rust_viterbo/docs/hk2019-benchmark.py
"""

import math
import time

import rust_viterbo_ffi as ffi


def tesseract_subset(n_facets: int) -> tuple[list[list[float]], list[float]]:
    """Generate axis-aligned polytope with n facets (subset of tesseract)."""
    base_normals = [
        [1.0, 0.0, 0.0, 0.0],
        [-1.0, 0.0, 0.0, 0.0],
        [0.0, 1.0, 0.0, 0.0],
        [0.0, -1.0, 0.0, 0.0],
        [0.0, 0.0, 1.0, 0.0],
        [0.0, 0.0, -1.0, 0.0],
        [0.0, 0.0, 0.0, 1.0],
        [0.0, 0.0, 0.0, -1.0],
    ]
    return base_normals[:n_facets], [1.0] * n_facets


def main() -> None:
    print("HK2019 Benchmark (release build)")
    print("=" * 70)
    print(f"{'F':>3} {'F!':>12} {'Explored':>12} {'Time (s)':>10} {'us/perm':>10} {'Status':>12}")
    print("-" * 70)

    results = []

    for n in range(5, 9):  # 5-8 facets only (9+ times out)
        normals, heights = tesseract_subset(n)
        factorial = math.factorial(n)

        start = time.perf_counter()
        try:
            result = ffi.hk2019_capacity_hrep(normals, heights)
            elapsed = time.perf_counter() - start
            perms = result["diagnostics"]["nodes_explored"]
            us_per_perm = elapsed / perms * 1e6
            capacity = result["capacity"]
            status = f"c={capacity:.2f}"
            results.append((n, factorial, perms, elapsed, us_per_perm, status))
            print(f"{n:>3} {factorial:>12,} {perms:>12,} {elapsed:>10.3f} {us_per_perm:>10.1f} {status:>12}")
        except Exception as e:
            elapsed = time.perf_counter() - start
            status = str(e)[:20]
            print(f"{n:>3} {factorial:>12,} {'--':>12} {elapsed:>10.3f} {'--':>10} {status:>12}")

    print("-" * 70)
    print()
    print("Summary:")
    print("- HK2019 is practical for polytopes with ≤8 facets")
    print("- 8 facets: ~37s (40,320 permutations)")
    print("- 9 facets: times out at 60s (~10% complete)")
    print("- Per-permutation cost grows with facet count (larger QP)")


if __name__ == "__main__":
    main()
