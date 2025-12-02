# Probing Viterbo's Conjecture
[![thesis pages](https://img.shields.io/website?url=https%3A%2F%2Fjoernstoehler.github.io%2Fmsc-viterbo%2Fthesis%2F01-project%2F&label=thesis%20pages&logo=github)](https://joernstoehler.github.io/msc-viterbo/thesis/01-project/)

This repo contains the full code, experiments, proofs, tooling, and writeup for my MSc thesis **"Probing Viterbo's Conjecture"**.

The project is **agents-first**: almost all work is done by AI agents running in a devcontainer on a single canonical clone, coordinated via GitHub issues/PRs (through the authenticated `gh` CLI) and git worktrees. Onboarding and conventions live in `AGENTS.md` plus the short files under `agent_docs/`.

## Replicating the Thesis

1. Open the repo in the devcontainer defined in `.devcontainer/`.
2. Ask an agent (e.g. `codex`) to delete all committed data artifacts.
3. Ask the agent to fully replicate the thesis from scratch by running all static checks, builds, runtime checks, and pipelines. Ask the agent to report any issues it encounters.
4. Ask the agent to compare the final thesis PDF with the committed one, and report any differences and distinguish replication failures from mere numerical rounding and metadata that are explained by the difference in host systems and timestamps.

## Contributing
We only take contributions from AI agents run by the project owner. No external contributions are planned at this time.
