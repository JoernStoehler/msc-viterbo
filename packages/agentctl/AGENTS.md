# agentctl Onboarding

This package contains the `agentctl` tool, which manages the lifecycle of Codex agents. The devcontainer already ships a built and linked `agentctl`; do not tell users to install it. Verify availability with `agentctl --version`.

## Architecture
See [SPEC.md](./SPEC.md) for the detailed architecture and API contract.

## Development

### Prerequisites
-   Node.js (v18+)
-   `npm`
-   **Linux** (required for `agentctl self` — uses `/proc` filesystem for PID-based identity detection)
 -   Only needed when developing `agentctl` itself; not needed for normal agents in this repo (they already have `agentctl` on PATH).


### Quick Start
For local development of `agentctl` (not required inside the devcontainer):

**Important**: Start the daemon first in a separate terminal:
```bash
npm install
npm run build
npm start   # runs dist/src/daemon.js
```

Then use CLI commands:
```bash
node dist/src/cli.js list
node dist/src/cli.js start "Hello" --workdir /workspaces/some-dir
# Interactive TUI, registered as external:
node dist/src/cli.js codex-tui -- --search "do X"
```

### Build
```bash
npm install
npm run build
```

### Running Locally
1.  **Start Daemon**:
    ```bash
    npm start
    # OR
    AGENTCTL_PORT=3000 node dist/src/daemon.js
    ```
2.  **Run CLI**:
    ```bash
    node dist/src/cli.js list
    ```
3.  **Health check**:
    ```bash
    curl http://localhost:3000/health
    ```

### Try the packaged CLI
- For an end-to-end packaging check (what post-create uses): `npm install -g .` then run `agentctl --help`.
- For quicker local iterations without touching the global bin: `npm link` (undo with `npm unlink -g agentctl`).

### Output formats
- Default output is plain, grep-friendly text with a header row (`workdir id status managed pid last_active_at`), sorted by `last_active_at` (updated_at) descending. Suppress the header with `--no-header`.
- Add `--json` to `start`, `status`, `await`, `stop`, or `list` to get machine-readable JSON (also sorted by last activity); `list --jsonl` emits NDJSON.

### Self-identification
- `agentctl self` prints `project_owner` when not running inside a Codex shell, otherwise the detected agent UUID. With `--json` it returns a structured object `{ identity, agent_uuid?, source }`. Uses PID-based ancestry matching to identify the agent by tracing the process tree and matching against the daemon's thread state. Exits non-zero if `CODEX_SHELL_ENV=1` and no UUID is found.

### Detach/await behavior
- `agentctl start` returns immediately by default (`--detach=true`). Use `--await` or `--detach=false` to block until the turn finishes.

### Testing
- Integration tests use the mock Codex, writing session files to a temp `AGENTCTL_CODEX_SESSIONS_DIR`. Run `npm test`.
- Set `AGENTCTL_MOCK_SESSION_DELAY_MS` to simulate slow session creation for timeout paths.

### Troubleshooting
- **Daemon fails to start**: Check port (default 3000) and `~/.agentctl/state/daemon.pid` (if present).
- **Daemon already running**: A second `agentctl daemon` exits with a clear “already running on port …” message; stop the existing daemon or use `AGENTCTL_PORT` to pick another port.
- **Session file not found**: Ensure `AGENTCTL_CODEX_SESSIONS_DIR` points to the actual Codex sessions root (default `~/.codex/sessions`), the process can write there, and increase `AGENTCTL_DISCOVERY_TIMEOUT_MS` if Codex is slow to emit `session_meta`.
- **Stop fails**: `agentctl stop` only works for `managed=daemon`; external threads must be exited in their owning terminal.
- **Git prompts inside agent shells**: Non-interactive Git is enforced for agents via `~/.codex/config.toml` (`GIT_TERMINAL_PROMPT=0`, `GIT_SSH_COMMAND='ssh -oBatchMode=yes'`, etc.). Project-owner shells remain interactive; adjust env only if you are deliberately debugging Git inside an agent shell.
