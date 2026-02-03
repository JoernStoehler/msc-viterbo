# docs/CLAUDE.md

Project documentation and reference materials.

## Structure

```
docs/
  investigations/                       # Agent-written reports on investigations e.g. troubleshooting, literature review
    <YYYY-MM-DD>-<description>.md
  papers/                               # Downloaded academic papers
    README.md                           # Download workflow and paper index
    <Initials><Year>-<ShortTitle>/      # Per-paper folder
      *.tex                             # .tex sources for easier reading and searching
```

## See Also
- Skill `knowledge-base` for creating investigation reports and adding knowledge across the project.
- Skills `.claude/skills/<label>/SKILL.md` contain topic/task-specific domain knowledge and procedural knowledge.
- Files `CLAUDE.md`, `<dir>/CLAUDE.md` contain folder-related knowledge.
- See `papers/README.md` for download workflow and paper index.
