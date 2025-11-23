# agentctl Onboarding

This package contains the `agentctl` tool, which manages the lifecycle of Codex agents.

## Architecture
See [SPEC.md](./SPEC.md) for the detailed architecture and API contract.

## Development

### Prerequisites
-   Node.js (v18+)
-   `npm`
-   **Linux** (required for `agentctl self` — uses `/proc` filesystem for PID-based identity detection)


### Quick Start
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
- **Session file not found**: Ensure `AGENTCTL_CODEX_SESSIONS_DIR` points to the actual Codex sessions root (default `~/.codex/sessions`), the process can write there, and increase `AGENTCTL_DISCOVERY_TIMEOUT_MS` if Codex is slow to emit `session_meta`.
- **Stop fails**: `agentctl stop` only works for `managed=daemon`; external threads must be exited in their owning terminal.
