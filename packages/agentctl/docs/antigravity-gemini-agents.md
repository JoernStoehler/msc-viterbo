# AntiGravity Gemini Agents

This document provides specific guidance for **AntiGravity agents powered by Gemini 3 Pro** working on this project.

## Canonical Onboarding

**`AGENTS.md`** (at the repository root) is the canonical location for onboarding material. Read that file first to understand:
- Project overview and architecture
- Repository layout
- Development environment
- Workflows and conventions
- Universal standards

This file supplements that information with Gemini-specific tool capabilities.

## Agent Identity

You are an **AntiGravity agent** running in the AntiGravity VS Code fork, powered by **Gemini 3 Pro**. You work alongside:
- **Codex agents** (GPT-5 series, managed via `agentctl`)
- **Claude agents** (Claude Sonnet 4.5, also in AntiGravity)
- **Jörn Stöhler** (Human project owner)

## Available Tools

As a Gemini-based AntiGravity agent, you have access to tools similar to Claude agents, but there may be differences in implementation or naming. 

*(TODO: A Gemini agent should expand this section with the complete tool list and any Gemini-specific capabilities)*

### Expected Tool Categories
- Code understanding & navigation
- Code modification
- Command execution
- Web & research
- Asset generation
- Resources & integrations

### Gemini 3 Pro Specific Capabilities
- **1 million token context window**: You can process entire codebases and large documents
- **Multimodal understanding**: Advanced visual understanding for images, diagrams, UI screenshots
- **Agentic workflows**: Optimized for complex, multi-step coding tasks
- *(TODO: Document any Gemini-specific tool features)*

## Tool Usage Best Practices

*(TODO: A Gemini agent should document best practices based on their actual tool set)*

## Differences from Other Agents

### vs. Claude Agents
- Both run in AntiGravity IDE
- May have different tool implementations or capabilities
- *(TODO: Document specific differences)*

### vs. Codex Agents
- Codex agents use `agentctl` and different SDK tools
- Codex uses `functions.apply_patch` vs. your file editing tools
- *(TODO: Document other key differences)*

## Spawning Sub-Agents

You can use `agentctl` to spawn Codex sub-agents for parallel work:

```bash
# Start a Codex agent in a specific worktree
agentctl start --workdir /path/to/worktree --prompt "Task description"

# Check status
agentctl status <thread-id>

# Wait for completion
agentctl await <thread-id>
```

See the root `AGENTS.md` for detailed workflows on worktree management and agent delegation.

## Integration with Project Workflows

- **Worktree discipline**: Work in dedicated git worktrees for feature branches
- **PR-driven**: All work culminates in a PR against `main`
- **Testing**: Run relevant tests before pushing (no CI/CD, all validation is local)
- **Documentation**: Update docs alongside code changes
- **Provenance**: Add agent attribution to GitHub issues/PRs

## Further Reading

- `/workspaces/msc-viterbo/AGENTS.md`: Root onboarding (READ THIS FIRST)
- `/workspaces/msc-viterbo/packages/agentctl/SPEC.md`: `agentctl` architecture and API
- `/workspaces/msc-viterbo/packages/agentctl/AGENTS.md`: `agentctl` development guide
- Package-specific `AGENTS.md` files in `packages/*/AGENTS.md`

---

**TODO**: This file should be completed by a Gemini 3 Pro agent who has direct access to their tool catalog. Please expand the "Available Tools" section with the complete list of tools and their usage patterns, and document any Gemini-specific capabilities.
