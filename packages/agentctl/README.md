# agentctl

Manage Codex AI agent lifecycles in devcontainers.

## Quick Start

**Terminal 1** (start daemon):
```bash
cd packages/agentctl
npm install
npm run build
npm start
```

**Terminal 2** (use CLI):
```bash
cd packages/agentctl
npx agentctl start "Hello world task" --workdir /path/to/workspace
# Returns thread ID immediately (runs in background by default). Add --await or --detach=false to block until done.

npx agentctl list
npx agentctl status <thread-id>
npx agentctl await <thread-id>  # Wait for completion
```

## What is agentctl?

`agentctl` is a daemon-based tool that provides visibility, traceability, and robust process management for AI agents (specifically Codex instances) running in development containers.

### Core Features

- **Visibility**: All agent state persisted to disk (`~/.agentctl/state/`)
- **Reliability**: Long-running agents managed by daemon, not shell
- **Simplicity**: CLI is a thin client; daemon handles complexity
- **Traceability**: Complete logs (stdout, stderr, events) for every agent session

## Documentation

- **[SPEC.md](./SPEC.md)** — Complete architecture, API contracts, and implementation details
- **[AGENTS.md](./AGENTS.md)** — Developer onboarding, testing, and troubleshooting

## Architecture

```
┌─────────────┐           ┌─────────────┐           ┌─────────────┐
│ agentctl CLI│──HTTP────▶│   Daemon    │──spawns──▶│    Codex    │
│  (client)   │           │  (server)   │           │   Process   │
└─────────────┘           └─────────────┘           └─────────────┘
                                 │
                                 ▼
                          ┌─────────────┐
                          │ Filesystem  │
                          │    State    │
                          └─────────────┘
```

## Commands

| Command | Description |
|---------|-------------|
| `agentctl daemon` | Start the daemon (required for all other commands) |
| `agentctl start <prompt> --workdir <path>` | Start a new agent thread |
| `agentctl list [--status <filter>]` | List all threads (default: plain grep-friendly lines; `--json` → JSON array; `--jsonl` → NDJSON) |
| `agentctl status <id>` | Get thread status |
| `agentctl await <id>` | Wait for thread completion |
| `agentctl stop <id>` | Stop a running thread |
| `agentctl self` | Detect current agent identity |
| `GET /health` | Daemon health check endpoint |

Add `--json` to any command for machine-readable output.

## Requirements

- **Node.js**: v18+
- **Platform**: Linux (macOS/Windows supported for most features, but `agentctl self` requires Linux `/proc` filesystem)

## Development

See [AGENTS.md](./AGENTS.md) for:
- Building from source
- Running tests
- Troubleshooting
- Contributing

## License

ISC
