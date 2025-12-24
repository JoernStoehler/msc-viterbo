---
name: skill-authoring
description: Create or update repo skills under .codex/skills. Use when adding new skills, editing SKILL.md, or deciding what should be a skill vs a spec/doc.
---

# Skill Authoring (repo conventions)

## When to use a skill

- Use skills for procedural workflows and package conventions that are not always‑on.
- Keep specs/APIs/algorithms in conventional docs; reference them from skills.

## Where skills live

- Repo skills are committed under `.codex/skills/<skill-name>/SKILL.md`.
- Do not modify `~/.codex/skills` (global).

## Authoring guidance

- Follow `$skill-creator` for general skill design and front‑matter rules.
- Keep SKILL.md lean; move large details into `references/`.
- Avoid extra docs like README.md inside skills.

## Naming

- Use lowercase letters, digits, and hyphens.
- Name the folder exactly after the skill name.
