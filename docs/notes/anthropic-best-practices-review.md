# Anthropic Best Practices Review

Comparison of this project's agent workflow against Anthropic's official Claude Code best practices (https://code.claude.com/docs/en/best-practices). Reviewed 2026-01-31.

**Audience:** Jörn and PM agents.

---

## Summary

The project adheres to most Anthropic best practices, often implementing them more rigorously than the baseline recommendations. Key deviations are intentional and documented, arising from the unique constraints of a multi-agent academic thesis project with mathematical correctness requirements.

| Category | Adherence | Notes |
|----------|-----------|-------|
| Verification | ✅ Strong | Tests verify mathematical properties, not just "no crash" |
| Stage separation | ✅ Strong | 5 stages vs Anthropic's 4; frozen specs prevent criteria hacking |
| Context management | ✅ Strong | Session separation + worktrees + focus budget model |
| CLAUDE.md | ✅ Good | Concise, uses progressive disclosure |
| Skills/Subagents | ⚠️ Deviation | Uses commands instead of skills (documented reason) |
| Permissions | ✅ Good | Deny rules for secrets; non-interactive git |
| Hooks | ✅ Good | SessionStart hook for file index |

---

## Detailed Comparison

### 1. Verification ("Give Claude a way to verify its work")

**Anthropic says:** Include tests, screenshots, or expected outputs so Claude can check itself. This is the single highest-leverage thing you can do.

**Project practice:**
- ✅ `rust-testing.md` mandates tests verify **mathematical propositions**, not just runtime behavior
- ✅ Tests check: symplectomorphism invariance, monotonicity, scaling laws, literature values
- ✅ Cross-algorithm agreement (HK2017 vs Tube) serves as mutual verification
- ✅ Local CI (`scripts/ci.sh`) mirrors GitHub CI exactly
- ✅ Agent prompts require waiting for CI green before declaring done

**Assessment:** Exceeds Anthropic's recommendations. The mathematical verification requirements are more rigorous than typical software testing.

---

### 2. Stage Separation ("Explore first, then plan, then code")

**Anthropic says:** Separate research and planning from implementation using Plan Mode. Four phases: Explore → Plan → Implement → Commit.

**Project practice:**
- ✅ Five explicit agent roles: PM → Planner → Spec-Reviewer → Developer → Reviewer
- ✅ Each stage runs in a separate Claude Code session (clean context)
- ✅ **Frozen specs:** Developer agents cannot modify SPEC.md
- ✅ Worktrees enable parallel work without context pollution
- ✅ Context compaction happens at stage transitions

**Deviation:** Project uses 5 stages instead of 4.

| Anthropic 4-Stage | Project 5-Stage | Rationale |
|-------------------|-----------------|-----------|
| Explore | PM + Planner | PM handles orchestration; Planner does investigation |
| Plan | Planner + Spec-Reviewer | Explicit spec review catches ambiguity before dev |
| Implement | Developer | Same |
| Commit | Reviewer + PM | Explicit code review; PM handles merge |

**Documented in:** `docs/notes/agent-workflow-design.md` explains the focus budget model and why stages are separated. Quote:

> **Why 5 stages work:** The stages are sufficiently different cognitive tasks. Not splitting them means adding up their focus costs, likely exceeding budget.

**Assessment:** Adheres to the principle, extends it with additional safeguards. The frozen-spec pattern addresses a failure mode Anthropic doesn't explicitly mention (criteria hacking).

---

### 3. Context Management ("Manage context aggressively")

**Anthropic says:** Run `/clear` between unrelated tasks. Use subagents for investigation. Context is the fundamental constraint.

**Project practice:**
- ✅ Session separation inherently clears context between stages
- ✅ Worktrees allow parallel agents without shared context pollution
- ✅ Focus budget model explicitly tracks context as a scarce resource
- ✅ Task() subagents recommended for focused subtasks
- ✅ File index at session start provides orientation without exploration overhead

**Additional project-specific practices:**
- Agents escalate rather than accumulate failed approaches
- "Out of scope" notes defer work to fresh sessions
- PM agent, not dev agent, creates follow-up issues

**Documented in:** `agent-workflow-design.md` has extensive "Focus Budget Model" section describing observed failure modes and mitigations.

**Assessment:** Strong adherence. The focus budget model is a more explicit formulation of Anthropic's "context is the fundamental constraint" principle.

---

### 4. CLAUDE.md Configuration

**Anthropic says:**
- Keep it short and human-readable
- Only include things that apply broadly
- Ask "Would removing this cause Claude to make mistakes?"
- Don't include anything Claude can figure out by reading code
- Check into git

**Project practice:**
- ✅ CLAUDE.md is ~150 lines (concise for a multi-package thesis project)
- ✅ Uses progressive disclosure: CLAUDE.md has essentials, `docs/conventions/` has details
- ✅ Checked into git
- ✅ Quick commands section lists only essential commands
- ✅ Agent prompts live in `.claude/commands/`, not bloating CLAUDE.md

**Content comparison:**

| Anthropic ✅ Include | Project |
|---------------------|---------|
| Bash commands Claude can't guess | ✅ Quick commands section |
| Code style rules differing from defaults | ✅ Referenced in conventions |
| Testing instructions | ✅ Referenced in `rust-testing.md` |
| Repository etiquette | ✅ Agent protocol section |
| Architectural decisions | ✅ Key locations table |
| Developer environment quirks | ✅ `environments.md` reference |

| Anthropic ❌ Exclude | Project |
|---------------------|---------|
| Anything Claude can figure out from code | ✅ Not included |
| Standard language conventions | ✅ Not included |
| Detailed API documentation | ✅ Not included (links to papers/thesis) |
| Long explanations | ✅ Moved to conventions docs |

**Assessment:** Good adherence. The progressive disclosure pattern (CLAUDE.md → conventions → specs) is a clean implementation of "keep it concise."

---

### 5. Skills and Subagents

**Anthropic says:**
- Create `SKILL.md` files in `.claude/skills/` for domain knowledge
- Define specialized assistants in `.claude/agents/` for isolated tasks

**Project practice:**
- ⚠️ No `.claude/skills/` directory (empty)
- ⚠️ No `.claude/agents/` directory (empty)
- Uses `.claude/commands/agent-*.md` instead

**Deviation documented in:** `docs/notes/agent-workflow-design.md`:

> **Why commands, not skills:** Skills auto-load based on description matching, but this fails for multi-line invocations. Commands with `$ARGUMENTS` reliably load the full prompt with task context in one message.

**Assessment:** Intentional deviation with documented rationale. The commands approach works for this project's orchestration model where Jörn explicitly invokes agent roles.

**Potential improvement:** Consider using `.claude/agents/` for subagent definitions (security-reviewer style) that dev agents could invoke via Task(). Currently, subagent usage is ad-hoc rather than predefined.

---

### 6. Permissions Configuration

**Anthropic says:** Use `/permissions` to allowlist safe commands. Deny sensitive files.

**Project practice:**
- ✅ `.claude/settings.json` denies: `.env`, `.env.*`, `**/secrets/**`
- ✅ Non-interactive git environment variables set
- ✅ No overly permissive `--dangerously-skip-permissions` usage documented

**Assessment:** Good adherence. The permission model is conservative and appropriate for a thesis project.

---

### 7. Hooks

**Anthropic says:** Use hooks for actions that must happen every time with zero exceptions.

**Project practice:**
- ✅ SessionStart hook runs `session-start.sh`
- ✅ Hook prints compressed file index for immediate context
- ✅ Hook installs `gh` CLI in web environments

**Assessment:** Good adherence. The file index hook is a nice implementation of "give Claude immediate orientation."

**Potential improvement:** Consider hooks for:
- Post-edit linting (as Anthropic suggests)
- Blocking writes to certain directories (e.g., preventing accidental thesis chapter modifications by dev agents)

---

### 8. CLI Tools

**Anthropic says:** Tell Claude Code to use CLI tools like `gh`, `aws`, `gcloud` when interacting with external services.

**Project practice:**
- ✅ `gh` CLI is primary interface for GitHub (issues, PRs, checks)
- ✅ CLAUDE.md documents `gh` usage patterns
- ✅ Session-start hook ensures `gh` is available
- ⚠️ Known issue documented: `gh issue view` GraphQL deprecation workaround

**Assessment:** Good adherence. The `gh` CLI is well-integrated.

---

### 9. MCP Servers

**Anthropic says:** Run `claude mcp add` to connect external tools.

**Project practice:**
- No MCP servers configured
- Not documented as an explicit decision

**Assessment:** Neutral. MCP servers don't appear necessary for this project's workflow (code + thesis + experiments). No external services like Figma, Notion, or databases are used.

---

### 10. Avoiding Common Failure Patterns

**Anthropic lists these failure patterns:**

| Pattern | Anthropic Fix | Project Practice |
|---------|---------------|------------------|
| Kitchen sink session | `/clear` between unrelated tasks | ✅ Session separation by stage |
| Correcting over and over | After 2 failures, `/clear` and rewrite prompt | ✅ Escalation principle: "A brief interruption beats agent running into a dead end" |
| Over-specified CLAUDE.md | Ruthlessly prune | ✅ Progressive disclosure to conventions docs |
| Trust-then-verify gap | Always provide verification | ✅ Mandatory CI, mathematical property tests |
| Infinite exploration | Scope investigations or use subagents | ✅ Planner stage is bounded; Task() subagents encouraged |

**Additional project-specific mitigations:**
- **Frozen specs** prevent criteria hacking (not mentioned by Anthropic)
- **Explicit escalation triggers** prevent agents from drifting

**Assessment:** Strong adherence plus additional mitigations.

---

### 11. Automation and Scaling

**Anthropic says:** Use headless mode (`claude -p`), multiple sessions, fan-out patterns.

**Project practice:**
- ✅ Multiple parallel sessions via worktrees
- ✅ PM orchestrates, Jörn spawns (clear division)
- Headless mode not explicitly used (agents are interactive with Jörn)

**Assessment:** Good adherence for the interactive thesis workflow. Headless mode would be relevant for automated experiment pipelines but isn't documented.

---

### 12. Prompting Practices

**Anthropic says:**
- Reference specific files, mention constraints, point to example patterns
- Let Claude interview you for larger features
- Ask codebase questions like you'd ask a senior engineer

**Project practice:**
- ✅ Agent prompts include specific file references (SPEC.md, FFI bindings, etc.)
- ✅ Planner agent is designed to investigate and ask clarifying questions
- ⚠️ Interview pattern (`AskUserQuestion` loop) not explicitly documented

**Assessment:** Good adherence. The interview pattern could be documented as a technique for ambiguous tasks.

---

## Deviations Summary

| Deviation | Documented? | Rationale Provided? | Location |
|-----------|-------------|---------------------|----------|
| Commands instead of skills | ✅ Yes | ✅ Yes | `agent-workflow-design.md` |
| 5 stages instead of 4 | ✅ Yes | ✅ Yes | `agent-workflow-design.md` |
| Frozen specs | ✅ Yes | ✅ Yes | `agent-workflow-design.md` |
| External orchestration (Jörn spawns) | ✅ Yes | ✅ Yes | `agent-workflow-design.md` |
| No MCP servers | ❌ No | N/A | N/A |
| No predefined subagents | ❌ No | N/A | N/A |

---

## Recommendations

### High Value (consider implementing)

1. **LSP plugins for code intelligence** ✅ Implemented
   - `rust-analyzer-lsp` and `pyright-lsp` provide automatic diagnostics after edits
   - Claude sees type errors, missing imports immediately without running compiler/linter
   - Requires one-time interactive installation: `/plugin install rust-analyzer-lsp@claude-plugins-official --scope project`
   - Binaries (`rust-analyzer`, `pyright-langserver`) installed in devcontainer
   - **Trial period:** Postmortem asks agents to report friction/noise from LSP plugins

2. **Predefined subagents from actual usage**
   - Don't speculatively create subagents (YAGNI)
   - Postmortem now asks agents to report successful Task() prompts
   - Create `.claude/agents/` entries only for patterns that emerge from real usage

### Medium Value (consider documenting)

3. **Document MCP decision**
   - Either "not needed because X" or "planned for Y use case"
   - Prevents future agents from wondering

4. **Interview pattern for ambiguous specs**
   - Add to planner agent prompt: "For ambiguous requirements, use AskUserQuestion tool to interview Jörn"

### Low Value (already handled differently)

5. **Skills vs commands**
   - Current approach works well for explicit orchestration
   - Skills would only help if agents needed to self-select behaviors

---

## Conclusion

The project demonstrates strong adherence to Anthropic's best practices, with several extensions addressing academic/mathematical correctness requirements not covered in the general guidance. The documented deviations (commands over skills, frozen specs, 5-stage pipeline) are well-reasoned adaptations to the thesis project's unique constraints.

The focus budget model documented in `agent-workflow-design.md` is a notable contribution that formalizes observations about agent context degradation. This could be valuable feedback for Anthropic's best practices documentation.
