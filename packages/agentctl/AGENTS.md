# packages/agentctl/AGENTS.md

This file defines the `agentctl` contract. The root-level `AGENTS.md` tells every agent when to use the CLI; this document explains how the tool is wired internally, which commands exist, and what stdout/stderr/exit codes to expect. Keep it in sync with the code—agents and automation rely on it verbatim.

## Scope

`agentctl` is the lifecycle orchestrator for worktrees and Codex-backed sessions. The only user-facing identifier is the **agent handle** (for example `issue-456-a3f1`). Handles are unique per repository and stay stable for the lifetime of an agent. Every turn starts with the canonical bootstrap command:

```
bash -lc 'pwd && agentctl self && git status -sb'
```

That prints the current handle plus git status before any edits happen.

Drop into this file when you modify the CLI, touch the SQLite schema, or need to know the precise outputs for scripting.

## Local Development

- Location: `packages/agentctl`. Run the binary via `cargo run -- <subcommand>` from that directory or supply `--manifest-path packages/agentctl/Cargo.toml` from the repo root.
- Style/quality gates: `cargo fmt`, `cargo clippy --all-targets --all-features`, and `cargo check` must pass before you hand work back to the project owner. Add tests when feasible.
- Dependencies: `clap` (CLI), `rusqlite` (state store, bundled SQLite), `serde`/`serde_json` (structured output), `chrono` (timestamps), `nix` (signal handling), and `thiserror` (error wrappers). Do not add heavier stacks without prior approval.
- Modules: `main.rs` contains the CLI wiring; `state.rs` abstracts SQLite; `util.rs` keeps git/process helpers; `error.rs` implements the `CliError` type.

## Architecture Overview

### State Store

 - Path: `~/.agentctl/repos/<slug>/state.db` (shared across all worktrees for that repo slug). Created on demand.
- Selected pragmas: WAL journaling + `foreign_keys = ON`.
- Tables (simplified):

| Table | Key | Columns (highlights) |
| --- | --- | --- |
| `worktrees` | `path TEXT PRIMARY KEY` | `branch TEXT`, `repo_root TEXT`, `bootstrapped_at TEXT` |
| `agents` | `handle TEXT PRIMARY KEY` | `worktree_path TEXT REFERENCES worktrees(path)`, `parent_handle TEXT`, `model TEXT`, `reasoning_budget TEXT`, `defined_at TEXT` |
| `turns` | `id INTEGER PRIMARY KEY` | `handle TEXT REFERENCES agents(handle)`, `status TEXT`, `prompt_path TEXT`, `log_path TEXT`, `final_path TEXT`, `turn_dir TEXT`, `session_uuid TEXT`, `child_pid INTEGER`, `started_at TEXT`, `last_active_at TEXT`, `stopped_at TEXT`, `failure_reason TEXT` |

`status ∈ {launching,running,stopped,failed}`. Agents use handles exclusively; Codex session UUIDs stay internal but are recorded for diagnostics.

Session artifacts live under `~/.agentctl/repos/<slug>/sessions/<handle>/turn-<timestamp>/`, where `<slug>` is derived from the repo root path. Every turn stores:

- `prompt.txt` – copy of the prompt passed to `agentctl start`.
- `events.jsonl` – Codex JSONL stream (`codex exec --json`) plus stderr lines.
- `final_message.txt` – content written via `--output-last-message`.

### Session Lifecycle

1. `agentctl define` records `handle → worktree` metadata.
2. `agentctl start` ensures no active turn exists, copies the prompt into the next turn directory, inserts a `launching` row, and spawns the hidden helper `agentctl _exec ...`. If a previous turn recorded a `session_uuid`, the command resumes that conversation; otherwise it opens a fresh one. `_exec` launches the appropriate `codex exec` invocation with stdin pointing at the prompt file and logs Codex output to `events.jsonl`.
3. `_exec` keeps reading Codex JSONL until it sees the first `thread.started` event. It prints `SESSION <uuid>` to stdout (consumed by `agentctl start`) and continues logging. When resuming, `_exec` verifies the UUID matches the requested one. If Codex crashes before emitting the UUID, `_exec` prints `ERROR ...` and exits non-zero.
4. The public `start` command blocks until it reads `SESSION ...` (or `ERROR ...`) from `_exec`. Timeouts (default 30 s, configurable via `--timeout`) kill `_exec`, mark the turn `failed`, and exit 74. On success the turn row flips to `running` and records `_exec`’s PID so later `stop/await` commands can signal it.
5. `_exec` waits for Codex to finish, then updates the turn row to `stopped` (or `failed` if Codex exited non-zero). It also prints `ERROR codex exec failed` when Codex returns a non-zero status so that automation can pick up the failure.

`agentctl stop` sends SIGTERM (and escalates to SIGKILL after 10 s) to the recorded `_exec` PID. `agentctl await` polls the PID until it disappears or a timeout expires. Both commands rely on the DB entry; there is no background daemon.

`agentctl print` simply reads the most recent `N` turn directories and dumps the prompt/final message for quick inspection.

## CLI Reference

All commands exit `0` on success unless mentioned otherwise. Failures print a single `Error: ...` line to stderr and use the exit code listed here. The `--json` flag (available on `list`, `print`, `self`) emits a single JSON document matching the tabular data.

### `agentctl list [--json]`

Shows every defined handle plus the latest turn status. Text mode output uses a space-aligned table with headers `handle worktree parent model budget status last_active`. JSON mode emits an array of objects with the same fields plus the raw timestamps.

### `agentctl bootstrap <worktree-path>`

Registers an existing git worktree. The command canonicalizes `<worktree-path>`, ensures it lives inside the repo root, records the branch name in SQLite, and ensures the repo-scoped `~/.agentctl/repos/<slug>/state.db` exists (slug derived from the repo root). If the environment variable `AGENTCTL_BOOTSTRAP_HOOK` is set (for example `export AGENTCTL_BOOTSTRAP_HOOK="bash scripts/agentctl-bootstrap-hook.sh"`), the referenced command is executed after registration with these env vars: `AGENTCTL_REPO_ROOT`, `AGENTCTL_WORKTREE`, `AGENTCTL_WORKTREE_BRANCH`. The hook runs in the repo root and can handle toolchain-specific setup (e.g., `uv sync`). Exit codes: `65` invalid path, `70` filesystem/git error or hook failure.

### `agentctl define <handle> --worktree <path> [--parent <handle>] [--model <gpt-5|gpt-5-codex>] [--reasoning-budget <high|medium|low>]`

Associates a human-friendly handle with a bootstrapped worktree. Handles must match `[a-z0-9._-]+`. Defaults: `parent=project_owner`, `model=gpt-5-codex`, `reasoning-budget=high`. Exit code `65` when the worktree has not been bootstrapped.

### `agentctl start <handle> --prompt <text> | --prompt-file <path> [--timeout <seconds>]`

- Fails with `65` if the handle is unknown or already running.
- Copies the prompt into `~/.agentctl/repos/<slug>/sessions/<handle>/turn-<timestamp>/prompt.txt`.
- Spawns `_exec` and waits (default 30 s) for `SESSION <uuid>`. Timeout → exit `74`. Codex spawn failure → exit `73` (`ERROR failed to spawn codex exec` is also printed by `_exec`).
- If the agent already has a recorded `session_uuid`, `_exec` runs `codex exec resume <uuid> -` so Codex continues the same conversation; otherwise it runs a fresh `codex exec --json -`. The summary includes a `mode: fresh|resume` line so humans know which path was used.
- On success prints:

```
started agent <handle>
worktree: <abs-path>
session_uuid: <uuid>
mode: fresh|resume
```

Future `stop/await/print` commands refer to the same handle; the Codex UUID stays internal except for the summary line above.

### `agentctl stop <handle>`

Sends SIGTERM to the `_exec` PID recorded for the handle. After the process exits, marks the turn `stopped` and prints `Stopped agent <handle>.` Exit codes:

- `65`: unknown handle or no running turn.
- `70`: failure sending signals.
- `124`: `_exec` refused to die within the hardcoded 10 s window.

### `agentctl await <handle> [--timeout <seconds>]`

Blocks until the handle’s current turn finishes or the timeout elapses. A clean finish prints `Agent <handle> completed.` and exits `0`. If the turn is still running after `--timeout`, exits `124` so the caller can decide whether to stop or inspect the agent. Invoking `await` does **not** change the stored turn status; the turn remains `running` until it stops naturally or via `agentctl stop`. If no running turn exists, exits `65`.

### `agentctl print <handle> [--last N] [--json]`

Reads the last `N` (default 1) turn directories. Text mode prints the per-handle turn number (e.g. `Turn #3`), status, timestamps, session UUID, prompt content, and the final message (or `[no final message yet]`). JSON mode emits the raw turn records from SQLite.

### `agentctl self [--json]`

Echoes the current handle/worktree metadata.

1. Use `AGENTCTL_HANDLE` if set (the start command exports this env var before launching `_exec` so the Codex process can call `agentctl self` immediately).
2. Otherwise, print an "unbound" record with the canonical current directory plus `none`/`undefined` placeholders (JSON mode emits `null` for those fields). This makes it obvious that the caller is not running inside an agent turn, even when the worktree hosts other handles.

Outputs (text mode):

```
handle: issue-456-a3f1
worktree: /workspaces/worktrees/issue-456
parent: project_owner
model: gpt-5-codex
budget: high
defined_at: 2025-11-19T12:30:00Z
```

When no handle is active:

```
handle: undefined
worktree: /workspaces/msc-viterbo
parent: none
model: none
budget: none
defined_at: none
```

### `agentctl interactive <handle> [--allocate --worktree <path>]`

Launches the Codex TUI for the given handle. Behavior:

1. If `--allocate --worktree <path>` is provided, the command first bootstraps the handle (same defaults as `agentctl define`—parent inferred from `AGENTCTL_HANDLE`, model defaults to `gpt-5-codex`, reasoning budget defaults to `high`). Pass `--model` / `--reasoning-budget` alongside `--allocate` to override those defaults.
2. Fails with `65` when the handle does not exist (and `--allocate` is missing) or when another turn is already running.
3. Prepares a fresh turn directory (prompt/log/final files) and inserts a `turns` row with status `launching`.
4. Spawns `codex resume <uuid>` when a previous session exists, otherwise `codex` for a fresh session. The child inherits STDIN/STDOUT/STDERR so the user controls the session manually. All environment variables (`AGENTCTL_*`) match the automatic `_exec` workflow.
5. Updates SQLite to mark the turn as `interactive` plus the Codex PID so that `agentctl stop/await` can supervise the TUI just like automated turns.
6. Once the user exits the TUI, `agentctl interactive` stores the latest session UUID (parsed from `~/.codex/history.jsonl`), marks the turn `stopped` (or `failed` if Codex returned a non-zero status), and prints a short summary.

Use this command whenever the project owner wants to take over a handle interactively without losing track of the turn history.

### `agentctl _exec ...` (internal)

Hidden helper invoked by `agentctl start`. Arguments (all required):

```
agentctl _exec \
  --handle <handle> \
  --turn-id <id> \
  --worktree <path> \
  --prompt-file <path> \
  --log-path <path> \
  --final-path <path> \
  --repo-root <path> \
  --model <gpt-5|gpt-5-codex> \
  --budget <high|medium|low> \
  [--resume-uuid <uuid>]
```

Behavior:

1. Launches either `codex exec --json --sandbox danger-full-access -C <worktree> --model <model> --output-last-message <final-path> -` (fresh turn) or `codex exec resume <uuid> --json --sandbox danger-full-access -C <worktree> --model <model> --output-last-message <final-path> -` (when `--resume-uuid` is provided). Stdout/stderr are captured.
2. Tails JSONL stdout, appending every line to `<log-path>`. Once it observes a `thread_id`, prints `SESSION <uuid>` to its own stdout (consumed by `agentctl start`) and flushes. When resuming, `_exec` verifies the UUID matches; mismatches trigger `ERROR session-id-mismatch`, kill Codex, and mark the turn failed.
3. Writes stderr lines prefixed with `STDERR ` to the same log file from a helper thread.
4. When Codex exits:
   - Success → mark the turn `stopped` in SQLite.
   - Failure → mark the turn `failed`, print `ERROR codex exec failed`, and exit with code `73`.
5. If Codex exits before emitting a session UUID, `_exec` prints `ERROR session-id-missing`, marks the turn `failed`, and exits `74`.

`_exec` is the **only** component that ever talks to `codex exec`. All other commands interact solely with SQLite and the filesystem.

## Exit Codes Summary

| Code | Meaning |
| --- | --- |
| `0` | success |
| `65` | invalid arguments / unknown handle / missing bootstrapping |
| `70` | git/filesystem/SQLite error |
| `71` | worktree missing on disk |
| `72` | prompt file unreadable |
| `73` | failed to spawn Codex or Codex exited non-zero |
| `74` | timed out waiting for session UUID or resume mismatch |
| `124` | await/stop timeout |

Update this table whenever you introduce new exit codes.

## Future Work

- Add `agentctl inspect <handle> --json` to dump the entire agent + turn history for dashboards.
- Surface `agentctl print --follow` to stream Codex output while a turn is running.
- Heartbeats: a future `agentctl ping <handle>` command could refresh `last_active_at` without touching the Codex process.

Always update this document (and the root onboarding) before shipping new behavior so downstream automation sees a consistent contract.
