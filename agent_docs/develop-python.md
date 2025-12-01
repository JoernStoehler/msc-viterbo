# Developing in Python
- Package: `packages/python_viterbo`
- Goal: Orchestration layer and logic of quickly written experiments/pipelines.
- Toolchain: we pinned a recent-ish version.
- Caching: `uv` has a global cache. Worktrees have local `.venv` virtual environments.
- Commands: Use `uv run` to run all commands.

## Conventions
- Experiments consume and produce artifacts and json files in `packages/python_viterbo/{data/,config/}` that are committed to git and git LFS.
- E2E tests sanity check experiment outputs and experiment behavior on small inputs.
- Unit tests for mathematical helper functions to catch bugs and regressions early.
- Docstrings/comments explain the "why" behind design decisions and the "contract" of public APIs.
- Layout: `data/<producer>/` for artifacts, `config/<consumer>/<stage_variant>.json` for experiment config json files, `src/viterbo/experiments/<experiment>/stage_<name>.py` for entrypoints, `src/viterbo/experiments/<experiment>/<other>.py` for helper code that can be imported by other experiments.
- Experiments are run as `uv run python -m viterbo.experiments.<experiment>.stage_<name> --config <path/to/json_file>`.
- Use basic type hints to catch bugs early with `uv run pyright`.
- Docstrings document shapes and dtypes and conventions of numpy/pytorch tensors where applicable.
- Use `uv run ruff check --fix .` to autoformat and fix simple linter errors.
- Use `uv run pytest <args>` to run a selection of relevant tests.
- Avoid code reuse between experiments, experiments rarely are stable enough to justify abstracting common code.
- Focus on quick iteration, e2e tests to catch regressions and confirm contracts of artifacts and configs, and unit tests for mathematical helper functions to catch bugs early.
- Reference the thesis writeup where applicable for mathematics, and for experiment motivation and interpretation.
- Keep all configuration in the json files instead of custom command args, so that git tracks the reproducible experiment setups.
