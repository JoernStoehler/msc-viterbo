# agentctl Onboarding

This package contains the `agentctl` tool, which manages the lifecycle of Codex agents.

## Architecture
See [SPEC.md](./SPEC.md) for the detailed architecture and API contract.

## Development

### Prerequisites
-   Node.js (v18+)
-   `npm`

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

### Testing
We use a self-contained integration test suite that mocks the Codex agent.
```bash
npm test
```

### Troubleshooting
-   **Daemon fails to start**: Check if the port (default 3000) is in use. Check `~/.agentctl/state/daemon.pid` (if implemented) or just `ps aux | grep daemon`.
-   **Codex not spawning**: Ensure `codex` is in your PATH, or set `AGENTCTL_CODEX_BIN` to the absolute path.
-   **Handshake timeout**: The daemon waits 10s for the first JSON event from Codex. If Codex is slow or silent, this will fail. Check `~/.agentctl/state/threads/<id>/stderr.log`.
