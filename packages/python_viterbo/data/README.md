# Experiment Data

Output data from `viterbo.experiments.<label>` stages.

## Layout

Each experiment writes to `data/<label>/`:

| Directory | Experiment | Contents |
|-----------|------------|----------|
| `algorithm-comparison/` | Algorithm comparison | Benchmark results |
| `algorithm_inventory/` | Algorithm inventory | Algorithm metadata, fixtures |
| `benchmark-hk2017/` | HK2017 benchmarks | Timings, analysis, plots |
| `counterexample-hko/` | HK&O counterexample | Counterexample data |
| `hello/` | Hello example | Sample input |
| `polytope-database/` | Polytope database | Polytope geometries, capacities |
| `polytope-visualization-4d/` | 4D visualization | HTML/JSON visualizations |
| `runtime_performance_analysis/` | Runtime analysis | Performance metrics |

## Conventions

- JSON for small structured data
- Parquet for large tabular data
- PNG for plots (also copied to `packages/latex_viterbo/assets/`)
