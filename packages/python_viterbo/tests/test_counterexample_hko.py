from __future__ import annotations

import json
import math
from pathlib import Path

from viterbo.experiments.counterexample_hko.stage_build import DATA_DIR, capacity_values, write_json, build_facets


def test_capacity_formula_matches_closed_form() -> None:
    cap, vol, sys = capacity_values()
    assert math.isclose(sys, (math.sqrt(5) + 3) / 5, rel_tol=1e-12)
    assert cap > 0 and vol > 0 and sys > 1


def test_facets_written_and_lengths_match() -> None:
    facets = build_facets()
    write_json(facets)
    data = json.loads((DATA_DIR / "facets.json").read_text())
    normals = data["normals"]
    heights = data["heights"]
    # 10 facets total: 5 from K, 5 from T
    assert len(normals) == 10
    assert len(heights) == 10
    # All normals are unit length
    for n in normals:
        assert math.isclose(sum(x * x for x in n) ** 0.5, 1.0, rel_tol=1e-12)
    # Heights positive
    assert all(h > 0 for h in heights)
