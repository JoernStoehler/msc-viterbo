# Agent Workflow Design

Notes from environment modernization review (2026-01-29). Captures decisions about agent orchestration, focus management, and development workflows.

**Audience:** Jörn and PM agents. Regular dev/plan/review agents don't need this - they follow their prompts.

**Scope:** Workflow design and rationale. Project context (Viterbo's conjecture, deadline, codebase layout) lives in CLAUDE.md.

---

## Claude Code Context

Terms used throughout this document:

- **Claude Code**: Anthropic's CLI/IDE extension for working with Claude as a coding agent
- **Plan mode**: Agent can read/search/run commands but cannot edit files (except designated plan files). Used for investigation and planning. Can run git commands to commit/push the plan file. Agent writes a plan file and exits for approval.
- **Bypass mode**: Agent can edit files and take actions. Used for implementation.
- **Task() subagents**: Claude Code feature to spawn focused sub-agents that complete a specific task and return results to the parent agent. Useful for boxing off work that would otherwise expand focus cost.
- **Spawning an agent**: Starting a new Claude Code session (via IDE extension or CLI) with a specific prompt. Only Jörn spawns full sessions; agents cannot spawn other sessions, only Task() subagents.
- **Skills**: Markdown files in `.claude/skills/` with YAML frontmatter. Claude Code loads skill bodies when the description matches the current task.
- **Context compaction**: When Claude Code transitions from plan mode to bypass mode (or runs low on context), it summarizes prior conversation. This clears some focus-consuming discussion from context.

---

## Focus Budget Model

*This is a working hypothesis based on observed agent behavior, not a verified theory.*

Agents appear to have a limited "focus budget" X that measures how diverse their work can be. When exceeded, agents become confused (observed symptoms):
- Pay less attention to their task, more to ad-hoc actions
- Neglect aspects or misinterpret them and stick with misinterpretations
- Hallucinate novel goals and pursue them
- Switch from "how do I achieve X" thinking to impulsive next-action output
- Plan for shorter-term or incomplete goals
- **Hack acceptance criteria downwards** - redefine success to match what they've done

### Estimating Focus Cost

*Hypothesis:* Focus cost correlates with how "unrelated" subtasks are - i.e., how different the cognitive pathways and actions involved are.

**Subadditivity:** Similar tasks cost less than the sum of their individual costs. E.g., writing Rust + writing Python involves similar thought patterns and actions, so combined focus cost < (Rust cost) + (Python cost).

**Two types of focus erosion:**
1. **Jarring transitions**: Switching between unrelated tasks (e.g., issue writing → implementation) - high immediate cost
2. **Cumulative mass**: Many similar small actions (reading, writing, testing in a loop) slowly erode focus over time

| Stage | Focus Cost (estimated) | Notes |
|-------|------------|-------|
| Issue description | High | Abstract reasoning, long-term planning, stepping back into broad context |
| Detailed planning | Medium-high | Search, reading, breaking down requirements, coming up with actionable steps that are coarse enough (not overspecified, not too long) |
| Implementation | Low-high | Reading, writing, testing, debugging in a loop. These actions are similar/"trained in", so agent does them smoothly. Cost increases when reinterpreting/correcting the plan, or debugging across modules. Cumulative mass effect. |
| QA/Review | Medium | Stepping back, clarifying criteria, asking critical questions. Critical questions differ from agent's usual "just do things that look good enough" mode. Higher if criteria are underspecified or very custom (e.g., proof checking requires novel thought chains). |

**Why 5 stages work:** The stages are sufficiently different cognitive tasks. Not splitting them means adding up their focus costs, likely exceeding budget.

### Mitigations (proposed)

- **Stage separation**: Split work into issue → plan → dev → review stages, each in separate sessions. Prevents jarring transitions within a session.
- **Frozen specs**: Dev agents implement against specs they cannot change. Prevents criteria hacking - agent can't redefine success when focus degrades.
- **Task() subagents**: Box off focused subtasks (e.g., refactoring all references to a symbol). The subagent reports back in a format that doesn't expand the parent's frame - parent doesn't need to read unrelated code.
- **Escalation**: Agents escalate out-of-scope issues rather than making difficult decisions themselves. Jörn has more focus for out-of-scope decisions than a degraded agent.

---

## Agent Pipeline

Five agent types with distinct roles. Agent prompts are skills in `.claude/skills/agent-*` (invoke with `/agent-developer`, `/agent-planner`, etc.).

| Agent | Purpose | Mode | Key Actions |
|-------|---------|------|-------------|
| **PM** | Orchestration | bypass | Write issues, write prompts, merge PRs, clean up, track milestones |
| **Plan** | Investigation & specification | plan | Investigate codebase, produce SPEC.md, submit PR |
| **Plan-review** | Spec quality check | plan | Check plan clarity, actionability, blockers |
| **Dev** | Implementation | bypass | Implement against frozen spec, escalate blockers |
| **Review** | Implementation quality check | plan (read-only review) or bypass (if pushing fixes) | Review code, verify against spec, push minor fixes |

### Full Pipeline (complex tasks)

1. Jörn discusses idea with PM agent
2. PM agent writes GitHub issue
3. PM agent writes prompt for planning agent
4. Jörn spawns planning agent
5. Planning agent investigates, asks Jörn for clarification, produces SPEC.md, submits PR
6. Jörn spawns plan-review agent (same worktree)
7. Plan-review agent checks clarity, submits comments/commits
8. PM merges plan PR, writes prompt for dev agent
9. Jörn spawns dev agent (new worktree)
10. Dev agent implements, escalates out-of-scope issues (including spec mistakes/contradictions)
11. Dev agent submits PR (referencing issue via "fixes #X"), fixes CI, marks ready for review
12. Jörn spawns review agent (same worktree as dev)
13. Review agent works through branch, leaves comments, pushes minor fixes. For major issues, Jörn returns to dev agent to continue work.
14. PM merges PR (issue auto-closes via PR link), cleans up branches/worktrees, proposes next actions

**Issue lifecycle:** Issues are closed when PR merges (via "fixes #X" in commit/PR description), or PM agent closes manually if obsolete/superseded. Dev agents reference issues, they don't explicitly close them.

**Communication paths:** Dev agents escalate to Jörn directly (in chat). Jörn may consult PM agent for long-term decisions. Structure: Dev ↔ Jörn ↔ PM. Agents don't communicate directly with each other except via worktree files and PR comments.

**Follow-up discovery:** Dev agents note "discovered X, out of scope" in PR description/comments. After PR merge, PM agent reads these notes and creates follow-up issues.

### Shortcuts

- **Skip plan-review**: When Jörn is familiar with the spec from talking with plan agent
- **Skip review**: When Jörn trusts dev agent on simple tasks
- **Manual prompts**: When PM agent's prompt isn't needed
- **Skip issue**: Put description directly in plan agent prompt
- **Combined session**: For simple tasks, combine issue+plan+dev+review in one Claude Code session using plan mode → bypass mode transition. Context compacts at the transition, clearing focus-consuming planning discussion so agent can focus on implementation.

### Expected Distribution (estimated)

- ~30% simple tasks (single combined session)
- ~30% full pipeline (all 5 agent types)
- ~30% partial pipeline (skip plan-review or other stages)
- ~10% other combinations / messier flows

### Failure Rates (estimated)

- ~16% of simple tasks: Jörn rejects output and restarts (faster than fixing)
- ~25% of full/partial pipeline tasks: fail due to blockers/dead ends, restart from scratch

---

## Progressive Disclosure

### What Goes Where

| Content | Location | Audience | Notes |
|---------|----------|----------|-------|
| Project context | CLAUDE.md | All agents | Minimal: topic, deadline, priority, layout |
| Agent protocol | CLAUDE.md | All agents | Simplified: work in directory, read skills, do work, commit, escalate |
| Quick commands | CLAUDE.md | All agents | Essential 6-8 commands |
| Domain skills | .claude/skills/ | Agents (pulled) | Loaded when skill description matches task |
| PM knowledge | `.claude/skills/agent-project-manager/SKILL.md` | PM only | Worktree management, issue triage, prompt writing |
| Jörn workflows | `docs/project-owner/` (to be created if needed) | Jörn only | Filename signals agents shouldn't read |

### Skills Are Pulled, Not Pushed

- Agent sees task → skill description matches → agent reads skill body
- This is already just-in-time context loading
- *Observation:* Problem is skill length, not skill existence
- *Observation:* Can't cut explanations without making commands cryptic
- *Observed failure modes without skills:* Agents know too much (focus loss) or too little (violate conventions)

**Known limitation:** Agents working in worktrees see CLAUDE.md and skills from main branch, not their worktree. Mitigating factors: edits to skills/CLAUDE.md are rare, info is loaded at session start (not affected by later main branch changes), branches usually stay close to main.

### Commands Are User-Invoked Shortcuts

- Commands do something when Jörn types `/command`
- Commands are NOT instructions for agents to follow
- Wrong pattern: `/create-worktree` that tells agent what to do
- Right pattern: PM agent has procedural knowledge in its prompt

---

## Environment Configuration

### Why Two Dockerfiles

Local and Codespace Dockerfiles are intentionally separate:
- Different TeX package requirements
- Different CLI tools installed
- Different cache strategies
- Editing one shouldn't require thinking about effects on the other

### Why Two devcontainer.json Files

Local and Codespace configs have genuinely different needs:
- Local has bind mounts for cache persistence
- Codespace has no mounts
- devcontainer spec doesn't support conditionals well
- Explicit separation is clearer

### Worktree Management

- Scripts (`.devcontainer/local/worktree-new.sh`, `worktree-remove.sh`) are for PM agent and Jörn
- Dev agents are told their worktree path in the prompt
- Dev agents use `cd /workspaces/worktrees/<task> && command` pattern
- VS Code Claude Code extension always sets main repo as cwd; agents adapt by using `cd &&` for all commands

---

## Process Practices

### Best-of-N Pattern

- Spawn multiple agents with prompt variations
- Compare results to gather coarse feedback on which approach works better
- Agent prompts can have A/B variations (e.g., `dev-a.md`, `dev-b.md` with different instructions)

### Blameless Post-Mortems

After agent sessions, ask agents:
- What was friction in the session?
- Did any phrases in skills require extra thought?
- What could have been better (no default expectation to compare against)?

Identifies: knowledge gaps, frequent friction, frequent mistakes, longer-than-necessary chains.

### Session Log Retention

Local devcontainer retains all agent session logs (stored in `~/.claude/` inside the container, persisted via bind mount). Potential two-week reflection to analyze patterns. Decision made ad-hoc when the time comes.

### Escalation Principle

Agents should escalate to Jörn when:
- Task is ambiguous
- Tests pass but behavior seems wrong
- Acceptance criterion can't be verified
- Spec has a mistake or contradiction
- Any out-of-scope decision needed

A brief interruption to answer a question beats agent running into a dead end.

---

## Key Decisions (2026-01-29)

| Decision | Rationale |
|----------|-----------|
| Local is primary environment | Jörn's desktop, bind mounts for cache persistence |
| Keep separate Dockerfiles | Maintenance is easier without cross-environment thinking |
| Delete `/create-worktree` command | Wrong pattern; PM agent has procedural knowledge |
| Simplify CLAUDE.md protocol | Remove worktree/cleanup instructions, add escalation |
| Create 5 agent prompts as skills | Explicit, controllable; invoke with `/agent-*` |
| YAGNI on workflow docs | Write them once workflows are established |
| Skills stay | Progressive disclosure works; cutting them causes problems |
