# agentctl Onboarding

This package contains the `agentctl` tool, which manages the lifecycle of Codex agents.

## Architecture
See [SPEC.md](./SPEC.md) for the detailed architecture and API contract.

## Development

### Prerequisites
-   Node.js (v18+)
-   `npm`

### Quick Start
**Important**: Start the daemon first in a separate terminal:
```bash
npx ts-node src/cli.ts daemon
```

Then use CLI commands:
```bash
npm install
npm run build
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
    AGENTCTL_PORT=3000 npx ts-node src/daemon.ts
    ```
2.  **Run CLI**:
    ```bash
    npx ts-node src/cli.ts list
    ```

### Try the packaged CLI
- For an end-to-end packaging check (what post-create uses): `npm install -g .` then run `agentctl --help`.
- For quicker local iterations without touching the global bin: `npm link` (undo with `npm unlink -g agentctl`).

### JSON output
- Add `--json` to `start`, `status`, `await`, `stop`, or `list` to get machine-readable JSON on stdout.

### Self-identification
- `agentctl self` prints `project_owner` when not running inside a Codex shell, otherwise the detected agent UUID. With `--json` it returns a structured object `{ identity, agent_uuid?, source }`. Uses PID-based ancestry matching to identify the agent by tracing the process tree and matching against the daemon's thread state. Exits non-zero if `CODEX_SHELL_ENV=1` and no UUID is found.

### Testing
We use a self-contained integration test suite that mocks the Codex agent.
```bash
npm test
```

### Troubleshooting
-   **Daemon fails to start**: Check if the port (default 3000) is in use. Check `~/.agentctl/state/daemon.pid` (if implemented) or just `ps aux | grep daemon`.
-   **Codex not spawning**: Ensure `codex` is in your PATH, or set `AGENTCTL_CODEX_BIN` to the absolute path.
-   **Handshake timeout**: The daemon waits 10s for the first JSON event from Codex. If Codex is slow or silent, this will fail. Check `~/.agentctl/state/threads/<id>/stderr.log`.
