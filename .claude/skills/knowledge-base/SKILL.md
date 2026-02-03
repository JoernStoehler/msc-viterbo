---
name: knowledge-base
description: How to extend the project knowledge base. Where knowledge lives, what goes where, and how to add new information. Use when documenting learnings, creating skills, or improving existing docs.
---

# Knowledge Base

This project uses explicit documentation so agents can work autonomously. This skill explains where knowledge lives and how to extend it.

## Knowledge Locations

| Location | Auto-loaded? | Content Type |
|----------|-------------|--------------|
| `CLAUDE.md` (root) | Always | Project context, agent protocol |
| `<dir>/CLAUDE.md` | On first read in dir | Rules/conventions for that directory |
| `.claude/skills/<label>/SKILL.md` | Description at startup | Procedures, workflows, how-to |
| File comments | When file is read | Context for that specific file |
| `docs/investigations/<date>-<desc>.md` | Never | One-off research reports |
| `docs/papers/` | Never | Downloaded academic papers |
| `tasks/` | Never | Tracked tasks, and per-task-only domain knowledge, plans, goals |

**Forbidden locations for CLAUDE.md:** `.claude/` (handled by root CLAUDE.md and system prompt)

## Decision Tree: Where Does It Go?

- Relevant for historical analysis: commit message, PR comments, `tasks/` notes, `docs/investigations/` report, etc.
- Relevant for the current session: chat messages, reasoning traces, session plan file, session todos, temporary files, etc.
- Relevant for future agents following up on this task: `tasks/` notes, PR description+comments, `docs/investigations/` report, etc.
- Relevant to all (most) agents working on the project at all: root `CLAUDE.md`
- Relevant to all (most) agents who read files in some directory: folder `<dir>/CLAUDE.md` (triggered on read)
- Relevant to agents who read a specific file: comments in that file (or reference to external doc)
- Relevant to some topic: `.claude/skills/<label>/SKILL.md`
- Relevant to some topic, related to some folder: reference the `<label>` skill in `<dir>/CLAUDE.md`

## References, Duplicates, Large files

Often a file (+section/lines) reference beats maintaining duplicate content.
Large CLAUDE.md or SKILL.md files hint that there's knowledge in them that isn't needed for all agents who read the CLAUDE.md/SKILL.md file, and so content should be moved out and referenced instead to let agents pick what they need.

SKILL.md descriptions are already loaded, so references only need to mention the label, not explain again when to read the skill.

## Adding New Knowledge

### Workflow

1. Identify who needs what parts of the new knowledge when
2. Check if there's already canonical locations that are read by those agents and (approximately) not by agents who don't need the knowledge
3. Choose where to put references to the knowledge, and where to put the actual content
4. Write the content, look up formatting conventions depending on location type, e.g. `[proposed]` markers
5. Update references to point to the new content
6. Do quality control

### Quality Checklist

Before committing knowledge base changes:

- [ ] **Findable**: Would an agent discover this when they need it?
- [ ] **Actionable**: Does it tell agents what to DO, not just what IS?
- [ ] **Current**: Did you remove/update any outdated content it replaces?
- [ ] **Minimal**: Is there redundant content that could be consolidated?
- [ ] **Cross-referenced**: Are pointers updated (root CLAUDE.md, skill descriptions)?

## Format Reference

### CLAUDE.md Files

```markdown
# <directory>/CLAUDE.md

[proposed]

<One-line description>

## <Section>
<Content>

## See Also
- `<self-explanatory filepath>`
- `<path>#<section>` for <reasons-to-read>
- Skill `<name>` (no need to repeat the auto-loaded description)
```

Keep CLAUDE.md files focused on:
- What somebody who reads files in this directory is statistically likely to need to know.
- Navigation help, what-goes-where style knowledge.
- How to do frequent elementary tasks in this directory, quick commands, the simple conventions we follow.
- Pointers to situationally useful further readings, especially skills or docs with more complex conventions or difficult workflows that are useful in this folder.

### SKILL.md Files

For detailed SKILL.md format, see the `skill-creator` skill.

Key points:
- YAML frontmatter with `name` and `description`
- Description is auto-shown at startup (agents know skill exists)
- Body can be read on-demand by agents

### Investigation Reports

```markdown
# <Title>

Collected <YYYY-MM-DD>.

## Conclusion

**<One-line finding>**

<Brief explanation>

---

## <Evidence sections>
...
```

Put conclusion first. Agents often read the whole file at once, but Jörn reads the top first.

## Anti-Patterns To Avoid

- **README.md for agent knowledge** - README.md is for humans; use CLAUDE.md for agents.
- **Duplicating content** - Point to the one source you want to maintain, don't copy.
- **Friction from Indirection** - Don't move small, simple pieces of knowledge behind references; duplicate if needed.
- **Orphan knowledge** - If it's not discoverable, it doesn't exist.
- **Over-nesting** - Aim for zero, one, or two hops to obtain knowledge.
