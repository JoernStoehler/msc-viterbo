"""
Example stage demonstrating experiment conventions.

Run: cd experiments && uv run python _example/stage_1.py
"""

from pathlib import Path

# =============================================================================
# CONFIG - All configuration is hardcoded for reproducibility
# =============================================================================

CONFIG = {
    "experiment_name": "_example",
    "variant": "full",  # Change to "smoke" for quick test runs
    "seed": 42,
}

# For smoke tests, override values:
if CONFIG["variant"] == "smoke":
    pass  # Example: CONFIG["n_samples"] = 10

# =============================================================================
# PATHS - Derived from config
# =============================================================================

DATA_DIR = Path(__file__).parent.parent.parent / "data"
OUTPUT_DIR = DATA_DIR / "outputs" / CONFIG["experiment_name"]


# =============================================================================
# MAIN
# =============================================================================


def main() -> None:
    """Run the stage."""
    OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

    # Example computation
    result = {"message": "Hello from _example", "variant": CONFIG["variant"]}

    # Write output
    output_path = OUTPUT_DIR / "stage_1_output.txt"
    output_path.write_text(str(result))
    print(f"Wrote: {output_path}")


if __name__ == "__main__":
    main()
