# Knowledge Base Audit

**Status:** inbox
**Priority:** P2

## Goal

Scan the procedural knowledge base for issues (incorrect, unclear, duplicate, contradictory, missing content) and produce a clustered list of findings for systematic follow-up.

## Motivation

Agents follow the knowledge base very well when it's high quality, so improving it directly improves agent workflow execution quality. We recently compressed most of our codebase into learnings due to drift into chaos, and are still rebuilding with more robust workflows. A clean knowledge base = faster progress + less churn.

## Approach

1. **Full scan** using fresh agent with full context window (or Sonnet 4.5 1M model for lower intelligence + full visibility)
2. **Intermediate deliverable:** Long list of findings, sorted into clusters:
   - Incorrect content
   - Unclear/ambiguous content
   - Duplicate content
   - Contradictory content
   - Missing content / gaps
3. **Follow-up:** Work through clusters one-by-one in focused sessions

## Scope

Procedural knowledge base includes:
- `/CLAUDE.md` (root)
- `<dir>/CLAUDE.md` files
- `.claude/skills/*/SKILL.md` files
- File comments that serve as knowledge

## Notes

Detection (finding issues) is easier than resolution (choosing fixes), so separate the phases.
