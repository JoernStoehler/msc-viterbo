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
- Default output is plain, grep-friendly text.
- Add `--json` to `start`, `status`, `await`, `stop`, or `list` to get machine-readable JSON on stdout. `list --json` returns a JSON array; add `--jsonl` to get newline-delimited JSON (one thread per line) for streaming use.

### Self-identification
- `agentctl self` prints `project_owner` when not running inside a Codex shell, otherwise the detected agent UUID. With `--json` it returns a structured object `{ identity, agent_uuid?, source }`. Uses PID-based ancestry matching to identify the agent by tracing the process tree and matching against the daemon's thread state. Exits non-zero if `CODEX_SHELL_ENV=1` and no UUID is found.

### Detach/await behavior
- `agentctl start` returns immediately by default (`--detach=true`). Use `--await` or `--detach=false` to block until the turn finishes.

### Testing
We use a self-contained integration test suite that mocks the Codex agent.
```bash
npm test
```

### Troubleshooting
-   **Daemon fails to start**: Check if the port (default 3000) is in use. Check `~/.agentctl/state/daemon.pid` (if implemented) or just `ps aux | grep daemon`.
-   **Codex not spawning**: Ensure `codex` is in your PATH, or set `AGENTCTL_CODEX_BIN` to the absolute path.
-   **Handshake timeout**: The daemon waits 10s for the first JSON event from Codex (override with `AGENTCTL_HANDSHAKE_TIMEOUT_MS`). If Codex is slow or silent, this will fail. Check `~/.agentctl/state/threads/<id>/stderr.log`.
