# project-metadata Experiment

**Status:** Blocked (claude -p not working in environment)
**Issue:** #146

## Research Question

What can we learn about productivity patterns from project metadata?

1. How is time distributed across categories (infra, algorithm, experiment, thesis)?
2. What fraction of effort was "wasteful" (reverted, superseded, failed)?
3. How did agent parallelization change productivity?

## Background

The project has 460 commits over 77 days. Commit timestamps can be weighted via KDE
to estimate effective hours, but raw commit counts don't distinguish between:
- Quick fixes vs deep work
- Productive vs wasteful effort
- Categories of work

## Method

### Stage 1: Collect (`stage_1_collect.py`)
Fetch full commit history from GitHub API.

**For each commit, collect:**
- `hash`: commit SHA
- `timestamp`: ISO timestamp
- `message`: commit message
- `author`: author name
- `files_changed`: list of files
- `insertions`, `deletions`: line counts

**Output:** `data/project-metadata/commits.json`

### Stage 2: Classify (`stage_2_classify.py`)
Use `claude -p --model haiku` to classify each commit.

**Categories:**
- `infrastructure`: CI, devcontainer, tooling, env setup
- `algorithm`: Rust algorithm implementation
- `experiment`: Python experiment code
- `thesis`: LaTeX writing
- `documentation`: CLAUDE.md, README, docs/
- `bugfix`: fixing broken code
- `refactor`: restructuring without behavior change
- `other`: doesn't fit above

**Classification prompt:**
```
Classify this git commit into ONE category: [infrastructure, algorithm, experiment, thesis, documentation, bugfix, refactor, other].

If the commit message clearly indicates the category, output just the category name.
If uncertain, I will provide the diff for more context.

Commit: {message}
```

**Caching:** Store classifications in `data/project-metadata/classifications.json`.
On re-run, only classify commits not in cache.

**Output:** `data/project-metadata/classifications.json`

### Stage 3: Analyze (`stage_3_analyze.py`)
Compute productivity metrics.

**Metrics:**
1. KDE-weighted hours per category
2. Hours per milestone (using issue references in messages)
3. Wasteful effort identification:
   - Commits later reverted
   - Commits superseded by subsequent work
   - Commits for ultimately-failed experiments

**Output:**
- `data/project-metadata/analysis.json`
- `FINDINGS.md`

## Blockers

`claude -p --model haiku` produces no output in current environment.

**Alternatives if blocked:**
1. Manual classification of sample commits
2. Regex heuristics from commit message prefixes (feat:, fix:, docs:, etc.)
3. Defer until environment fixed

## Expected Outputs

- `data/project-metadata/commits.json`
- `data/project-metadata/classifications.json`
- `data/project-metadata/analysis.json`
- `FINDINGS.md` with wasteful effort % for Kai report
