---
name: knowledge-base
description: How to extend the project knowledge base. Where knowledge lives, what goes where, and how to add new information. Use when documenting learnings, creating skills, or improving existing docs.
---

# Procedural Knowledge Base

This project uses explicit documentation so agents can work autonomously. 
This skill explains where knowledge that is about working on the project (procedural knowledge) lives and how to extend it.

Object-level domain knowledge (code, code docs, configs, material, literature) goes in the usual places in the repository, and we do not deviate from common conventions.

## Knowledge Locations

| Location | Side-Loaded? |
|----------|-------------|
| `CLAUDE.md` (root) | Always |
| `<dir>/CLAUDE.md` | On Read() below the folder |
| File comments | Never |
| `.claude/skills/<label>/SKILL.md` | Description field at startup |
| `docs/investigations/<date>-<desc>.md` | Never |
| `docs/papers/` | Never |
| `tasks/` | Never |
| `/tmp/` | Never |

**Note:** Do not create `.claude/CLAUDE.md`, it just overrides root `CLAUDE.md`.

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
- **Speculative workflows** - Don't write workflows and procedural knowledge that hasn't been used and evaluated yet.
- **Broadcasting Too Wide** - Don't put knowledge in root CLAUDE.md, or folder CLAUDE.md, if only some and not most agents who operate in the repo/folder need it. References and common+short conventions are okay to broadcast, since they do not distract agents who don't need them much.
- **Complexity** - Don't invent new custom workflows and conventions, stick to combining or building upon standard ones.
- **Reexplaining Trained Knowledge** - Don't reexplain knowledge that agents already have been trained on, i.e. don't reexplain conventions and workflows that are common among public github repositories, educational literature, or that are traced in logs on public servers. Reminders to get agents to recall their trained knowledge and to activate it into working memory are entirely different and not discouraged.
- **Repeating Already Loaded Knowledge** - Don't repeat knowledge that is already loaded automatically, e.g. skill descriptions, the agent system prompt, or CLAUDE.md content in parent folders. That's just creating duplication in the agent's context window at the cost of having multiple copies to maintain. Reminders or commentary about already loaded knowledge are entirely different and not discouraged.
- **Overloading Agents** - Don't provide too much knowledge targeted at one agent. If too much custom procedural knowledge (!= domain knowledge) is needed for an agent to carry out its task, the task is likely too complex and will fail even with the extra knowledge. Split such tasks into smaller tasks, and write the knowledge base material to target agents with handleable scopes. Agents can compact their context window and "unload" skills, so even if the subtasks are handled in sequence, the agent still only has to focus on the currently relevant skills.
