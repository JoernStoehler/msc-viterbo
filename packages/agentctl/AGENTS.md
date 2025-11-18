# packages/agentctl/AGENTS.md

This document explains how to develop the `agentctl` CLI and defines the interface contract that other onboarding files reference.

## Purpose

`agentctl` is the user-facing CLI for every lifecycle step around agents and worktrees. The root-level `AGENTS.md` tells you when to invoke it; this file captures the precise arguments, stdout/stderr wording, and exit codes. Drop down into this document only when:

- You are modifying `agentctl` (new flags, wording tweaks, bug fixes).
- You are troubleshooting an `agentctl` failure and need to confirm expected output, exit codes, or side effects.
- You plan to automate or delegate work via helper agents and need to script against the CLI surface.

If you are only executing issue work inside your assigned worktree, stay within the root onboarding and treat `agentctl` as a black box.

## Local Development

- The crate lives in `packages/agentctl` and is self-contained. Run `cargo run -- <subcommand>` from that directory, or `cargo run --manifest-path packages/agentctl/Cargo.toml -- <subcommand>` from the repo root.
- Always run `cargo fmt` and `cargo check` (or `cargo test` once we have tests) before pushing changes. Prefer `cargo clippy --all-targets --all-features` when time allows.
- Keep dependencies minimal. We currently use `clap` for argument parsing and `rand` for producing the canned outputs in varying order. Do not add heavyweight crates without syncing with the project owner.
- The binary entry point is `src/main.rs`. Each subcommand has its own handler function; keep them side-effect free until real orchestration logic is ready.
- Every handler is intentionally nondeterministic within a fixed set of responses so downstream automation can observe all patterns. If you change any wording or exit code, update this file and the root onboarding at the same time.

## CLI Contract

Common rules:
- Successful runs write the documented lines to stdout and exit `0`.
- Failure modes write exactly one error line to stderr and exit with the non-zero code listed below.
- Arguments are strictly positional or flag-based as written. Extra flags trigger Clap's built-in validation before entering our handlers.

### `agentctl provision <worktree> --branch <branch> [--from-branch <branch>]`

- `<worktree>`: absolute path such as `/workspaces/worktrees/issue-123`.
- `--branch`: branch name such as `agent/issue-123`.
- `--from-branch` (optional, default `main`): source branch used when creating the worktree.
- Output: `Worktree is ready. Start a new agent with 'agentctl start <worktree> --prompt \"...\"' (branch <branch> from <parent>)`
- Exit code: `0`.

### `agentctl start <worktree> --prompt <prompt>`

- Prints a random-looking identifier `hhhh-hhhh` (hex). This becomes the canonical session uuid for follow-up commands.
- Exit code: `0`.

### `agentctl list`

- Always prints the header `uuid status worktree updated_at`.
- Includes at least:
  - `8f12-873c running /workspaces/worktrees/issue-123 2025-11-18T12:35:14`
  - `9acb-1234 stopped /workspaces/worktrees/issue-120 2025-11-18T10:24:10`
- May include extra shuffled rows with similar formatting.
- Exit code: `0`.

### `agentctl stop <uuid>`

Randomly chooses one response:
1. stdout: `Stopped agent <uuid>`; exit `0`.
2. stderr: `Error: Unknown agent <uuid>`; exit `1`.
3. stderr: `Error: Agent already stopped <uuid>`; exit `2`.

### `agentctl resume <uuid> --prompt-file <path>`

Random responses:
1. stdout: `Resumed agent <uuid> with <path>`; exit `0`.
2. stderr: `Error: Unknown agent <uuid>`; exit `3`.
3. stderr: `Error: Agent already running <uuid> /workspaces/worktrees/issue-123`; exit `4`.
4. stderr: `Error: Worktree no longer present <uuid> /workspaces/worktrees/issue-123`; exit `5`.

### `agentctl merge <source> --into <target> [flags]`

Flags (`--ignore-uncomitted-source`, `--allow-uncomitted-target`, `--attempt-rebase`, `--attempt-squash`, `--ignore-missing-squash`, `--allow-merge-conflict`) are optional and currently only surface in the success message.

Random responses:
1. stdout: `Merge successful.` and, when flags are present, `Applied flags: ...`; exit `0`.
2. stderr: `validation failed: uncommitted changes in source folder, uncommitted changes in target folder, need to rebase before merge, need to squash before merge, will cause merge conflicts` plus the guidance line; exit `10`.
3. stderr: `Merge conflicts occured, please fix manually in target directory <target>.`; exit `11`.
4. stderr: `Rebase conflicts occured, please fix manually in source directory <source>.`; exit `12`.

### `agentctl remove <worktree>`

Random responses:
1. stdout: `Removed unused worktree <path>. Archived agents: [comma-separated uuids]`; exit `0`.
2. stderr: `Cannot remove worktree <path> while agents are running in it: [comma-separated uuids]`; exit `20`.

## Future Extensions

When adding new functionality:
- Extend this file first so tooling consumers can rely on the documented contract.
- Keep stdout/stderr wording deterministic (apart from intentionally randomized permutations) to make parsing easy.
- Update the root `AGENTS.md` once the high-level workflow changes.
