"""Tiny hello-world experiment to keep the pipeline exercised.

Reads a JSON config (name + sequence), prints a greeting using viterbo.dummy,
computes an alternating sum, and echoes where it would write outputs.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Sequence

from viterbo.dummy import alternating_sum, greet


def load_config(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def run(name: str, sequence: Sequence[int]) -> dict:
    greeting = greet(name)
    total = alternating_sum(sequence)
    return {"greeting": greeting, "alternating_sum": total}


def main(config_path: str = "config/hello/hello.json") -> None:
    cfg = load_config(Path(config_path))
    result = run(cfg.get("name", "friend"), cfg.get("sequence", []))
    print(json.dumps(result, indent=2))
    print("(sample run; write outputs under data/hello/ if needed)")


if __name__ == "__main__":
    main()
