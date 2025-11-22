# Agent Documentation

This directory contains **reference documentation** for the various AI agent types working on this project. These files explain how each agent type works, how to invoke them, what tools they have, and what quirks to be aware of.

## Purpose

These are **not** onboarding documents for agents to read about themselves. Instead, they are reference guides for:
- **Humans** who need to understand how different agent types work
- **Agents** who need to spawn or collaborate with other agent types
- **Anyone** debugging agent behavior or understanding tool capabilities

## Documentation Files

### Agent-Specific References

#### [antigravity-claude-agents.md](./antigravity-claude-agents.md) ✅
Reference for **Claude Sonnet 4.5 agents** in AntiGravity:
- How to start Claude agents (IDE-native)
- Complete tool catalog with signatures, effects, outputs, and quirks
- File editing tools (`replace_file_content`, `multi_replace_file_content`)
- Command execution (`run_command` with `SafeToAutoRun` behavior)
- Search strategies (`codebase_search`, `grep_search`, etc.)
- Comparison with Codex agents

#### [codex-gpt-agents.md](./codex-gpt-agents.md) ⚠️ In Progress
Reference for **GPT-5 Codex agents** managed via `agentctl`:
- ⏳ **Currently being written by a Codex agent**
- Will include: `agentctl` invocation syntax, Codex SDK tools, quirks (bash escaping, etc.)

#### [antigravity-gemini-agents.md](./antigravity-gemini-agents.md) 📝 Placeholder
Reference for **Gemini 3 Pro agents** in AntiGravity:
- 📝 **Awaiting Gemini agent** to complete this documentation
- Will include: Gemini-specific tools, 1M context window capabilities, multimodal features

### Navigation

**Start here**: All agents must first read [`/workspaces/msc-viterbo/AGENTS.md`](../../../AGENTS.md) for:
- Project overview and goals
- Repository structure
- Development environment
- Workflows and conventions
- Universal standards

**Then consult** the agent-specific reference files in this directory to understand:
- How to spawn that agent type
- What tools that agent has
- What quirks to watch out for
- How to collaborate with that agent type

## When to Use These Files

1. **Spawning sub-agents**: Read the reference for the agent type you want to spawn
2. **Collaborating across agent types**: Understand tool differences (e.g., `apply_patch` vs `replace_file_content`)
3. **Debugging**: Check quirks section for known issues (e.g., bash escaping requirements)
4. **Understanding capabilities**: See what tools are available to each agent type

## Contributing

If you are an agent and your documentation is incomplete or outdated:
1. Update your agent-specific reference file with accurate information
2. Document ALL tools you have access to (signatures, effects, outputs, quirks)
3. Add examples and best practices based on your experience
4. Keep the root `AGENTS.md` in sync with any workflow changes
