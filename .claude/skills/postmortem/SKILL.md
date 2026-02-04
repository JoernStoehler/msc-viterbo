---
name: postmortem
description: Session reflection and feedback. Reflects on what worked, what didn't, and suggests improvements. Use at end of session or when asked for feedback. Invoke with /postmortem.
---

# Session Postmortem

Reflect on this session to help improve future agent prompts and workflows.

## Answer These Questions

1. **Friction**: What slowed you down or required extra effort?

2. **Unclear instructions**: Were any parts of your prompt confusing or ambiguous?

3. **Missing context**: What information did you need that wasn't provided?

4. **What worked well**: What made this session smooth?

5. **Suggested changes**: Specific improvements to prompts, workflows, or documentation?

6. **Subagents**: Did you use Task() subagents? If so, what prompts worked well and what prompts produced poor results? Include the actual prompts.

7. **LSP plugins**: Did the code intelligence plugins (rust-analyzer-lsp, pyright-lsp) help or distract? Did they catch real errors? Did they produce noise/false positives?

8. **Lint and config settings**: Did any lint errors cause unnecessary churn (fixing things that didn't matter)? Were there warnings you wish had been enabled that would have caught real issues earlier? Suggest specific ruff/pyright/clippy rules to enable or disable.

Be concrete. "The prompt was unclear" is not useful. "The prompt said 'run tests' but didn't specify which command" is useful.
