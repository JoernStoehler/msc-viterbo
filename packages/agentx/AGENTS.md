# AGENTS – agentx Package

You are in `packages/agentx/`, which contains the Rust-based CLI tooling used by AI agents and the project owner.

## Goals

- Provide ergonomic commands to:
  - manage worktrees and branches,
  - start and stop autonomous agents,
  - support local integration flows (e.g. merging worktrees and preparing PRs).

## Layout

- `Cargo.toml` – Rust package definition.
- `src/main.rs` – CLI entrypoint.

Expect additional modules to be added as the tool grows. GitHub issue and PR management is handled via the `gh` CLI instead of this binary.

## Tooling and commands

- Use `cargo run -- <subcommand>` to invoke the CLI.
- Keep subcommands small and composable; prefer thin wrappers around simple, inspectable shell commands.
