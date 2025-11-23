# Codex GPT Agents Reference

Comprehensive reference for **Codex agents powered by GPT-5 series models** that are managed via `agentctl`. The devcontainer already includes a built `agentctl`; verify with `agentctl --version` and never suggest installing it. Agent shells are non-interactive for Git via `~/.codex/config.toml`; project-owner shells remain interactive. This file assumes you already read `/workspaces/msc-viterbo/AGENTS.md` and need exact, low-level behavior and tooling for Codex turns.

---

## 1. Invocation

### 1.1 Start the daemon
- `agentctl daemon [--port <port>] [--background]`
  - Default port: `3000` (overridable via `AGENTCTL_PORT`).
  - Runs an HTTP server that owns all Codex processes.
  - Exits fast with an “already running on port …” error if the port is in use.

### 1.2 Start a Codex turn
- `agentctl start [PROMPT] --workdir <path> [--thread <id>] [--detach|--await]`
  - `PROMPT` (positional): Initial user/system prompt for the Codex process.
  - `--workdir <path>`: Working directory passed to `codex exec --cd <path>`.
  - `--thread <id>`: Optional thread/session id to resume/force.
  - `--detach` (default): Return immediately after spawning.
  - `--await`: Block until the turn finishes.
  - Output: prints the discovered/assigned `thread_id`.

### 1.3 Other CLI commands
- `agentctl status <id>`: Show `status.json` for a thread.
- `agentctl await <id> [--timeout <seconds>]`: Poll until terminal state; exit codes 0/1/124.
- `agentctl list [--json] [--status <running|done|failed|aborted>]`: Enumerate threads.
- `agentctl stop <id>`: SIGTERM (then SIGKILL) the Codex process; sets status `aborted`.
- `agentctl self [--json]`: Print `project_owner` when outside a Codex shell; otherwise the detected agent UUID. Uses PID-based ancestry matching to identify the agent by tracing the process tree and matching against the daemon's thread state. Exits non-zero if `CODEX_SHELL_ENV=1` and no UUID is found.

### 1.4 Environment variables
- `AGENTCTL_CODEX_BIN`: Path to the `codex` binary (or mock). Required if not on `$PATH`.
- `AGENTCTL_CODEX_MOCK_INSTRUCTION_FILE`: JSONL replay file used when `AGENTCTL_CODEX_BIN` points to the mock implementation.
- `AGENTCTL_PORT`: Port for daemon and CLI (default `3000`).
- `AGENTCTL_STATE_DIR`: Override default state dir (`~/.agentctl/state`).

### 1.5 Codex process invocation (what the daemon actually runs)
- `codex exec [resume <thread_id>] --yolo --json --output-final-message <FILE> --cd <WORKDIR> <PROMPT>`
  - `--yolo`: suppresses interactive confirmations.
  - `--json`: newline-delimited JSON events on stdout.
  - `--output-final-message <FILE>`: final assistant message written separately.
  - `resume <thread_id>`: supplied when daemon continues an existing thread.

---

## 2. Tools & Functions (Codex SDK in this repo)

Each tool is exposed via the `functions.*` (CLI harness) or `web.run` namespace. Parameter types follow the JSON schema shown. Quirks are the things that routinely trip agents.

### 2.1 Shell / Process

#### `functions.exec_command`
- **Signature**: `exec_command({ cmd: string, justification?: string, login?: boolean, max_output_tokens?: number, shell?: string, with_escalated_permissions?: boolean, workdir?: string, yield_time_ms?: number })`
- **Effect**: Run `cmd` in a PTY shell (default `/bin/bash`, login shell by default).
- **Output**: Captures stdout/stderr and exit code; harness may prefix metadata (Chunk ID, wall time).
- **Quirks**:
  - Use full shell commands; wrap with `bash -lc '...'` only when you need shell features explicitly.
  - `with_escalated_permissions` triggers elevated execution when approval policies allow.
  - `yield_time_ms` controls how long the harness waits before returning incremental output.
  - Long output may be truncated by `max_output_tokens`.

#### `functions.write_stdin`
- **Signature**: `write_stdin({ session_id: number, chars?: string, max_output_tokens?: number, yield_time_ms?: number })`
- **Effect**: Send keystrokes to a running `exec_command` PTY session.
- **Output**: Returns latest stdout/stderr from that session.
- **Quirks**:
  - Use empty `chars` to poll output without sending input.
  - Session IDs come from the `exec_command` response when a command keeps running.

### 2.2 File editing

#### `functions.apply_patch`
- **Signature**: freeform string following the grammar:
  ```
  *** Begin Patch
  *** (Add|Delete|Update) File: <filename>
  ...unified diff hunks...
  *** End Patch
  ```
- **Effect**: Apply unified-diff style edits (add/update/delete/move).
- **Output**: Success/failure; no automatic formatting.
- **Quirks**:
  - No JSON escaping; send raw text exactly as it should appear on disk.
  - Cannot be issued in parallel with other tools.
  - Fails if patch does not apply cleanly; re-read file before retrying.

### 2.3 MCP resource tools

#### `functions.list_mcp_resources`
- **Signature**: `list_mcp_resources({ cursor?: string, server?: string })`
- **Effect**: Enumerate resources exposed by configured MCP servers.
- **Output**: Resource metadata array, paginated via `cursor`.
- **Quirks**: Use `cursor` for pagination; omit to start from first page.

#### `functions.list_mcp_resource_templates`
- **Signature**: `list_mcp_resource_templates({ cursor?: string, server?: string })`
- **Effect**: List parameterized resource templates available from MCP servers.
- **Output**: Template metadata array with pagination.
- **Quirks**: Same pagination semantics as `list_mcp_resources`.

#### `functions.read_mcp_resource`
- **Signature**: `read_mcp_resource({ server: string, uri: string })`
- **Effect**: Fetch the content of a specific MCP resource by URI.
- **Output**: Resource contents (often text/JSON).
- **Quirks**: `uri` must come from a prior `list_mcp_resources` call.

### 2.4 Planning

#### `functions.update_plan`
- **Signature**: `update_plan({ explanation?: string, plan: [{ step: string, status: "pending"|"in_progress"|"completed" }] })`
- **Effect**: Persist a lightweight, ordered plan with statuses.
- **Output**: Updated plan state.
- **Quirks**:
  - Do not use for trivial tasks; no single-step plans.
  - Only one step should be `in_progress` at any time.

### 2.5 Media

#### `functions.view_image`
- **Signature**: `view_image({ path: string })`
- **Effect**: Attach a local image file (by path) into the conversation context.
- **Output**: Inline image preview to the user; no file mutations.
- **Quirks**: Path must exist on disk; use for debugging screenshots or plots.

### 2.6 Web / research (multi-tool wrapper)

#### `web.run`
- **Signature**: 
  ```json
  {
    "open": [{ "ref_id": string, "lineno"?: integer }],
    "click": [{ "ref_id": string, "id": integer }],
    "find": [{ "ref_id": string, "pattern": string }],
    "screenshot": [{ "ref_id": string, "pageno": integer }],
    "image_query": [{ "q": string, "recency"?: integer, "domains"?: string[] }],
    "sports": [{ "tool":"sports","fn":"schedule"|"standings","league": "...","team"?:string,"opponent"?:string,"date_from"?:string,"date_to"?:string,"num_games"?:integer,"locale"?:string }],
    "finance": [{ "ticker": string, "type": "equity"|"fund"|"crypto"|"index", "market"?: string }],
    "weather": [{ "location": string, "start"?: string, "duration"?: integer }],
    "calculator": [{ "expression": string, "prefix": string, "suffix": string }],
    "time": [{ "utc_offset": string }],
    "search_query": [{ "q": string, "recency"?: integer, "domains"?: string[] }],
    "response_length": "short"|"medium"|"long"
  }
  ```
- **Effect**: Swiss-army web/calc/time wrapper. Executes only the provided sub-commands.
- **Output**: A combined object keyed by tool name; each item includes results plus `ref_id` tokens for follow-up `open/click/find/screenshot`.
- **Quirks**:
  - `search_query` limited to 4 queries per call; >3 requires `response_length` ≥ `medium`.
  - `screenshot` works only on PDFs; `pageno` is 0-indexed.
  - Use `open/click/find` to navigate within prior `ref_id` documents.
  - `calculator` is exact arithmetic, not floating shell.
  - Results are not automatically cited; the agent must add citations manually when responding.

---

## 3. Lifecycle

1. **Spawn**: CLI sends `POST /turn/start` to daemon with prompt/workdir (and optional thread id).
2. **Codex exec**: Daemon runs `codex exec ...` (see §1.5) detached.
3. **Handshake**: First JSON event on stdout includes the thread id. Daemon:
   - Creates `~/.agentctl/state/threads/<thread_id>/`.
   - Writes `status.json` with `status=running` and the child PID.
4. **Streaming**: All Codex stdout JSONL is copied verbatim to `log.jsonl`; stderr to `stderr.log`; raw stdout (for human-readable traces) to `stdout.log` if enabled.
5. **Final message**: Codex writes final assistant text to the `--output-final-message` path; daemon updates `status.json` (`status=done|failed`, `exit_code`).
6. **Stop**: `agentctl stop` sends SIGTERM (SIGKILL after timeout). Status becomes `aborted`.
7. **Resume**: `agentctl start --thread <existing>` issues `codex exec resume <thread_id> ...` so the Codex model continues the session history.

**State layout** (`~/.agentctl/state/threads/<thread_id>/`):
- `status.json`: `id`, `pid`, `status`, `exit_code`, `workdir`, timestamps.
- `log.jsonl`: Append-only event stream from Codex stdout (`turn_start`, tool calls, messages, `turn_end`, daemon process events).
- `stdout.log` / `stderr.log`: Raw streams (useful for debugging parsing failures).
- Optional `final_message.txt` (path passed via `--output-final-message`).

---

## 4. Quirks & Best Practices

- **Shell vs patch**: Use `exec_command` for commands (bash-escaped); use `apply_patch` for edits (raw text, no escaping). Mixing them causes escaping bugs.
- **Refresh before patching**: Read files just before patching; patches fail on drift.
- **Long-running commands**: Prefer `yield_time_ms` to stream output; follow with `write_stdin` to interact.
- **Plan tool discipline**: Use `update_plan` only for multi-step tasks; keep a single `in_progress` step; update after completing steps.
- **Web tool**: Batch multiple `search_query` items in one `web.run` call to reduce latency; respect recency/domain filters to avoid irrelevant hits.
- **State visibility**: Everything is persisted under `~/.agentctl/state/threads/`; check `stderr.log` when Codex fails to emit JSON.
- **Mocking**: Set `AGENTCTL_CODEX_BIN` to the mock script plus `AGENTCTL_CODEX_MOCK_INSTRUCTION_FILE` to replay deterministic JSONL for tests.
- **Approvals & sandboxing**: Approval policy/sandbox mode is set per turn by the harness; `with_escalated_permissions` should be true only when necessary. Never rely on network unless `network_access` is enabled.
- **Context budgeting**: Keep responses concise; Codex context window (GPT-5 series) is large but smaller than Claude/Gemini—trim logs and avoid pasting huge files.
- **Citations (when using `web.run`)**: Provide citations with the returned `ref_id`s; avoid dumping raw URLs.

---

## 5. Comparison with AntiGravity Agents (Claude / Gemini)

| Aspect | Codex (GPT-5, CLI) | AntiGravity Claude / Gemini (IDE-native) |
| --- | --- | --- |
| Invocation | `agentctl start --workdir ... --prompt ...` (daemon-backed CLI) | Started from AntiGravity IDE UI; no CLI |
| Editing tools | `functions.apply_patch` (raw unified diff) | `replace_file_content` / `multi_replace_file_content` (exact-match blocks) |
| Command exec | `functions.exec_command` + `write_stdin` PTY; explicit `workdir` | `run_command` with `SafeToAutoRun`, `WaitMsBeforeAsync`; no `cd` in command |
| Search/web | `web.run` wrapper (search/open/click/find/screenshot/image_query/calculator/etc.) | `codebase_search`, `grep_search`, `browser_subagent`, `read_url_content`, `search_web` |
| Context window | GPT-5 series context (large, but typically smaller than Claude Sonnet 4.5 and Gemini 3 Pro) | Claude Sonnet 4.5 ~200k; Gemini 3 Pro larger (multi-hundred‑k to M range) |
| Process control | State in `~/.agentctl/state/threads/<id>`; daemon manages lifecycle | IDE manages terminals/processes; no external state dir |
| Browser | None natively; only `web.run` static fetch + PDF screenshots | Full interactive browser via `browser_subagent` with video recording |

---

### Pointers
- Root onboarding: `/workspaces/msc-viterbo/AGENTS.md`
- Agentctl design/API: `/workspaces/msc-viterbo/packages/agentctl/SPEC.md`
- Agentctl package onboarding: `/workspaces/msc-viterbo/packages/agentctl/AGENTS.md`
- Companion docs: `packages/agentctl/docs/antigravity-claude-agents.md`, `packages/agentctl/docs/antigravity-gemini-agents.md`
