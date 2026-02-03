"""
Example stage demonstrating thesis asset creation.

Run: cd experiments && uv run python _example/stage_2.py
"""

from pathlib import Path

import matplotlib.pyplot as plt

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
INPUT_DIR = DATA_DIR / CONFIG["experiment_name"]
THESIS_DIR = Path(__file__).parent.parent.parent / "thesis"
ASSETS_DIR = THESIS_DIR / "assets" / CONFIG["experiment_name"]


# =============================================================================
# MAIN
# =============================================================================


def main() -> None:
    """Run the stage."""
    # Read input from stage_1
    input_path = INPUT_DIR / "stage_1_output.txt"
    if input_path.exists():
        stage_1_output = input_path.read_text()
        print(f"Read: {input_path}")
    else:
        stage_1_output = "No stage_1 output found"
        print(f"Warning: {input_path} does not exist")

    # Create output directory
    ASSETS_DIR.mkdir(parents=True, exist_ok=True)

    # Create a simple figure
    fig, ax = plt.subplots(figsize=(6, 4))

    # Dummy data for demonstration
    categories = ["A", "B", "C", "D"]
    values = [23, 45, 56, 78]

    ax.bar(categories, values, color="steelblue")
    ax.set_xlabel("Category")
    ax.set_ylabel("Value")
    ax.set_title("Example Figure for Thesis")

    # Add a note showing data from stage_1
    ax.text(
        0.95,
        0.95,
        f"Source: {stage_1_output[:30]}...",
        transform=ax.transAxes,
        ha="right",
        va="top",
        fontsize=8,
        color="gray",
    )

    # Save figure
    output_path = ASSETS_DIR / "figure.png"
    fig.savefig(output_path, dpi=150, bbox_inches="tight")
    plt.close(fig)
    print(f"Wrote: {output_path}")


if __name__ == "__main__":
    main()
