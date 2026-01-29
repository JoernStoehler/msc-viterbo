---
name: skill-creator
description: Guide for creating effective skills. This skill should be used when users want to create a new skill (or update an existing skill) that extends Claude's capabilities with specialized knowledge, workflows, or tool integrations.
---

# About Skills

Skills are modular, self-contained packages that extend Claude's capabilities with:
- Specialized workflows
- Tool integrations
- Domain expertise
- Bundled resources (scripts, references, assets)

# Core Principles

## Concise is Key

Only add context Claude doesn't already have:
- Challenge each piece: "Does Claude really need this?"
- Prefer concise examples over verbose explanations
- Remove redundant information

## Set Appropriate Degrees of Freedom

**High freedom (text-based)**
- Multiple valid approaches exist
- Context-dependent decisions required
- Example: "Review code for maintainability"

**Medium freedom (pseudocode/scripts)**
- Preferred patterns exist
- Some variation acceptable
- Example: "Use pytest for tests, prefer fixtures over setup methods"

**Low freedom (specific scripts)**
- Operations are fragile
- Consistency is critical
- Example: "Run `scripts/deploy.sh --env prod`"

## Anatomy of a Skill

```
skill-name/
├── SKILL.md (required)
│   ├── YAML frontmatter metadata (required)
│   │   ├── name: (required)
│   │   └── description: (required)
│   └── Markdown instructions (required)
└── Bundled Resources (optional)
    ├── scripts/ - Executable code (Python/Bash/etc.)
    ├── references/ - Documentation for context as needed
    └── assets/ - Files used in output (templates, icons, fonts)
```

# Bundled Resources

## Scripts (`scripts/`)

Executable code for deterministic, repeatedly-used tasks.

**Example:** `scripts/rotate_pdf.py`

## References (`references/`)

Documentation loaded into context as needed.

**Examples:**
- `references/finance.md` - Domain-specific terminology
- `references/api_docs.md` - API specifications

**Best practice:** Keep SKILL.md lean, move detailed info to references

## Assets (`assets/`)

Files for output (not context).

**Examples:**
- `assets/logo.png`
- `assets/template.pptx`
- `assets/boilerplate/`

## What NOT to Include

Don't add files meant for human readers:
- README.md
- INSTALLATION_GUIDE.md
- QUICK_REFERENCE.md
- CHANGELOG.md

**Don't duplicate live state.** Skills should contain stable workflows, not information that changes with the codebase. Examples of what belongs in code, not skills:
- Which functions are currently exposed via FFI → check `.pyi` stub
- Current test coverage → run tests
- List of implemented features → read the code

Skills document *how* to work, not *what* currently exists.

Only include files essential for AI agent execution.

# Progressive Disclosure Design Principle

Skills use a three-level loading system:

1. **Metadata** (name + description) - Always in context (~100 words)
2. **SKILL.md body** - When skill triggers (<5k words)
3. **Bundled resources** - As needed by Claude (unlimited)

## Pattern Examples

**High-level guide with references:**
```
SKILL.md: "Use references/api_spec.md for API details"
references/api_spec.md: Full API documentation
```

**Domain-specific organization:**
```
SKILL.md: Overview and common patterns
references/advanced.md: Complex edge cases
references/glossary.md: Domain terminology
```

**Conditional details:**
```
SKILL.md: Basic content + "See references/advanced.md for X"
```

# Skill Creation Process

## Step 1: Understanding with Concrete Examples

Gather usage patterns and concrete examples:
- Ask user for specific examples of when they'd use the skill
- Validate understanding with user feedback
- Ensure the skill addresses real, recurring needs

## Step 2: Planning Reusable Contents

Analyze examples for reusable resources:
- Identify common patterns across examples
- Determine what scripts, references, and assets are needed
- Consider what information Claude already has vs. needs

## Step 3: Initializing the Skill

```bash
scripts/init_skill.py <skill-name> --path <output-directory>
```

Creates the skill folder structure with template SKILL.md.

## Step 4: Edit the Skill

### Learn Proven Design Patterns

Study existing skills to understand effective patterns.

### Implement Reusable Skill Contents

Create scripts, references, and assets as planned.

### Update SKILL.md

**Frontmatter:**
- `name`: Skill identifier (lowercase, hyphens)
- `description`: When to use this skill (primary triggering mechanism)

**Body:**
- Instructions for using the skill
- How to use bundled resources
- Examples and patterns

**IMPORTANT:** The description field is the primary way Claude determines when to use your skill. Include all "when to use" information in the description, NOT in the body.

## Step 5: Packaging a Skill

```bash
scripts/package_skill.py <path/to/skill-folder>
scripts/package_skill.py <path/to/skill-folder> ./dist
```

This command:
- Validates skill structure and requirements
- Creates distributable `.skill` file (zip format)

## Step 6: Iterate

- Use the skill on real tasks
- Notice struggles and inefficiencies
- Update SKILL.md and bundled resources accordingly
- Refine based on actual usage patterns

# Key Writing Guidelines

- Use **imperative/infinitive form** in instructions
- **Frontmatter description** is the primary triggering mechanism
- Include all "when to use" information in description, NOT in body
- Keep SKILL.md body under 500 lines
- Keep file references one level deep from SKILL.md
- For reference files >100 lines, include table of contents
- Remove information Claude already knows
- Use concrete examples over abstract explanations
