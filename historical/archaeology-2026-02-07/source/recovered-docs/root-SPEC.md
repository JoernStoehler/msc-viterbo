# Specification

This document specifies the high-level scaffolding for my MSc math thesis project.

## Agents First

We use ai agents (codex cli) to carry out 99% of the thesis work. The project owner (Jörn) only does high-level strategy, e.g. writing this spec, writing issues and reviewing feature PRs before merging into main.

Designing a project in an agents-first way has several implications / best practices. Overall a good approximation to agent-first design is to design the project so that many human developers can swiftly onboard themselves, contribute to whatever feature they are interested in, and then leave again. High quality standards are essential to prevent degradation of the project due to the many hands that will touch it. Clear, modular and cherry-pickable onboarding materials are essential for developers to get to work quickly all on their own. Up-to-date onboarding documentation and up-to-date code is essential to enable trustable abstraction boundaries that developers can simply rely on without looking behind the hood.

For ai agents there's also a few implications that go against what would be considered best practice for human developers.

1. AI agents are trained on ~all of the internet, including all of github. Therefore they are deeply familiar with any common patterns, libraries, frameworks, tools, conventions, styles, workflows, project managament practices, etc. A name-drop is often enough to make the agent recall their knowledge about some pattern and apply it if useful, or skip it if not useful, while they work.
2. Custom conventions, tools, and finally custom code and comments and documentation of course aren't something agents are familiar with from their training data. Therefore they have to actually read the content they need to know. Agents are capable of using hints such as file names, references, overview pages, and text search to discern which files to read and which to skip at the moment while they work. Unlike human developers however agents can spend relatively little time reflecting on the read contents, and importantly cannot pause between/allocate time to different sentences. The best knowledge transfer therefors happens when files can be read from top to bottom, with clear, precise, specific, unambiguous, professional language and terminology that states explicitly everything that is intended to be conveyed, instead of relying on the agent to fill in gaps with deductions or worse with unreliable fast guesses.
3. Onboarding is responsible for quite some fraction of a single agent's total work time, and thus all agents' cumulative work time. Therefore we should design onboarding to be fast and efficient. The three main strategies are:
3a. Pick architectures and workflows that are fast to onboard to. Importantly: use common patterns that require a reminder / a statement that when are used, but no further elaboration for what the common pattern is. E.g.: use standard commands like `uv run pytest` instead of custom wrappers. When no good-enough common pattern exists, try to design custom patterns that are as simple and straightforward as possible, and which have as few moving parts as possible. It is often best to produce tools/code for canonical paths only (KISS, YAGNI) and provide merely further readings for what to do when deviating from the canonical path. For example, a complex build script for the canonical path is okay since its usage is quickly explained (`bash build.sh`), the model is quickly explained (wraps cargo build with a custom caching layer and emits readable benchmark reports to `docs/assets/benchmarks/` as json files), the deviation path is infrequent but well-known (read the file, understand the steps, modify the steps in your head, run them one by one manually), and development / maintainance is infrequent but well-known (edit a bash file, no further onboarding needed).
3b. Do progressive disclosure over several files using references. Tell agents what files contain what kind of situationally useful knowledge, and let the agents triage which files to read and which to skip. The root AGENTS.md file is the always-used entry point for onboarding, all agents read it automatically. The package AGENTS.md files are read only if the agent has to read about or modify content (code, docs, tools) of that package in more detail. They mostly onboard the agent to package-level relevant expectations for reading, e.g. folder layout, architecture, conventions, and reference further onboarding materials such as writing conventions, tool usage docs, etc.
3c. For the concrete knowledge-transfer files, where one can assume that the reading agent decided after triage that they may need the file's content, make those files efficient to read. As previously mentioned, use clear, precise, specific, unambiguous, professional language and terminology that states explicitly everything that is intended to be conveyed, without relying on the agent to fill in gaps with deductions or unreliable fast guesses. Use name-dropping of common patterns, such as tool commands, libraries, architecture components, etc. Split files that are too long (>250 lines or >10kB) into smaller files, so that agents can still easily read, edit and write them with single tool calls.

## Single Owner, Single Clone

The project is used and developed by a single project owner (Jörn) and many ai agents who do 99% of the work. The project does not have any external dependents or users. It does have very little public facing content:
- README.md: github landing page for interested external researchers; it states the thesis topic, how to reproduce the thesis in its entirety, and then simply points at AGENTS.md for developer onboarding if anyone wants to continue the project. We don't support nor plan for contributions from external human developers.
- the gh-pages site, which hosts the package's documentations, including their generated api docs. We use different static site generators for different packages.

Similarly we only have one clone of the repository, which uses the one canonical devcontainer environment, and several git worktrees for the agents' to work in parallel on different features. There is no need to reason about alternative environments, or about concurrency issues with other clones, or about transferring work between clones.

We don't use github CI, we build, test, benchmark and run our project locally in the devcontainer.

Since we do not have any contributor management, we only reserve the following actions for the project owner (Jörn). Everything else is handled by ai agents.
- Review and merge feature PRs on github into origin/main.
- Create the first drafts of feature-level issues in the repo.
- Trigger devcontainer rebuilds.

## Monorepo

We pick the right language for the right job. Therefore we have multiple packages in different languages in the same monorepo. Each package has its own toolchain, scripts, onboarding material, documentation, build system, source code and tests.
We provide minimal glue to keep the packages working together:
- The devcontainer installs the packages' toolchains and setups their caching solutions.
- The top-level git worktree provision script prepares the worktree so the agents can start working right away using any package.
- The top-level docs-build script gathers the documentations from the different packages and builds them into a single gh-pages site.
- The top-level AGENTS.md file points at the different packages' AGENTS.md files for package-level onboarding.

The packages we concretely have in this project are:

- Rust + cargo package with several crates for the high-performance math code.
- Python + uv package with a single python namespace for orchestration, data pipelines, e2e tests, and general data science and machine learning code since that's the natural language.
- Lean4 + lake + elan package for formalization and verification of our proofs and algorithms.
- A package `agentx` with custom bash- and python-based tools the ai agents and project owner can use, including scripts to monitor, start and stop autonomous agents, manage their worktrees, manage the issue board, merge worktree branches locally and submit final feature PRs to github, etc.

As glue to keep the packages working together we have
- The .devcontainer/ folder with the devcontainer.json and Dockerfile to setup the single canonical development environment.
- A top-level scripts/ folder with bash- and python-based tools to manage the monorepo, e.g. to build all documentations into a single gh-pages site, or to finish installation of toolchains in the devcontainer's postCreateCommand lifecycle hook.
- PyO3 in the Rust package and maturin in the Python package to build python bindings for the Rust code.
- a gitignored `.persist/` folder that persists across devcontainer rebuilds. We use symlinks to point more standard locations into this folder, e.g. for the cargo registry or the worktrees, so that they don't get deleted on devcontainer rebuilds.
- a symlink `issues/` to `.persist/issues/` to share among all worktrees the issue files that the agents work on.

The concrete structure of the monorepo is:
```
msc-viterbo/
- .devcontainer/
  - devcontainer.json
  - Dockerfile
- .persist/ [gitignored]
- scripts/
  - docs-deploy.sh
  - devcontainer-post-create.sh
  - provision-worktree.sh
- packages/
  - agentx/
  - rust_viterbo/
  - python_viterbo/
  - lean_viterbo/
- issues/ [symlink]
- AGENTS.md
- README.md
- LICENSE
```

## Issue-Driven Development

We use markdown files with yaml headers in the shared `issues/` folder to manage the thesis project. From features to bugs to chores, we create standalone issue files define the task and track freeform metadata such as `status`, `owner`, `assignees`, `labels`, `created_at`, `updated_at`, `closed_at`.
The advantage of a file-based issue tracker is that ai agents already know how to work with files.
A template for new issues is provided in `scripts/issue-template.md`.
Searching issues by filename and metadata instead of full text is easy via `bash scripts/print-issue-metadata.py | rg <search-term>`.
The project owner (Jörn) creates initial drafts of issues, and uses an ai agent to first refine them into a well-defined specification, and then ai agents to work through the issues, test and review their work, and submit once done the feature branch as a PR to github for the final review and merge / reject decision by Jörn.

The repo is driven overall by the issues. The decision flow is from issue drafts (usually high-level ideas by Jörn) to the refined issues (specification) to the plans & implementation & tests (done by one or more ai agents) to the final PR (reviewed and merged by Jörn).
Frequently the goal is to first get a rough proof or feature sketch from Jörn that is converted into a proper actionable specification that's then handed off to an fully autonomous ai agent. Latter investigates, plans, defines sub-issues and starts agents to work on them, merges sub-branches into the feature branch, gathers static and runtime feedback via testing/verification/reviews done by agents, and iterates on the plan and implementation until either it's done and submitted as PR, or the implementation attempt failed and the issue is better escalated back to Jörn for high-level guidance and potential refinement.

## Try Autonomously First

Since ai agents work nicely in parallel and are far cheaper than human developers, we generally try to first hand off issues to a fully autonomous ai agent and then evaluate the PR, or failure report, that comes out of it.
Only on failure do we retry with more human guidance, e.g. by fixing the issue specification, adding learnings and best guesses from the project owner about what he would try first, or by breaking down the issue into smaller parts that AI agents may be able to handle each on their own.
Using git and git worktrees makes it trivial to roll back a failed or rejected attempt and retry. The cost of rolling back is zero, the cost of trying again is low.
We sometimes may even let multiple agents work on exact copies of the same issue in parallel, and then pick the best PR among them to merge.

## High Quality Standards

Since many different ai agents will touch the codebase over time, we need to constantly push the project towards excellence. This includes:
- High code quality: readable, maintainable, self-explanatory, simple and boring code is best.
- Correctness: code should not make false claims, i.e. failing tests have to be clearly marked as expected-to-fail, known bugs have to be marked as TODOs or be resolved on the spot, outstanding tasks have to be marked in the issue tracker AND the code so that future agents who read the files are aware of the state of the project and don't make wrong assumptions.
- Reliability: we use manual, automated static and automated runtime checks to ensure that the environment, our custom tools, and the code itself work as intended. As static checks we use for example linters and type checkers. As runtime checks we use unit tests, property-based tests, end-to-end tests of data pipelines and tools. We run benchmarks to track performance and resource usage over time, since we set explicit or implicit expectations on performance for our tools and code, so that agents can use them smoothly without getting stuck or loosing too much time. For manual tests we do code reviews, let agents comment freely when they notice small issues they cannot fix on the spot, and let agents compare the specifications with the (in-code-file) documentation with the actual code to find discrepancies.
- Documentation: our code is readable and uses comments to explain both non-obvious implications that should be stated so future agents don't have to rederive them, as well as rationales behind design decisions that are not obvious from common knowledge that agents have due to their training. Concretely, architecture choices and finicky bug-fixes are very much worth documenting in code comments. We use comment headers for files to explain the file's purpose and high-level structure. Similarly we maintain docstrings for functions and structures. The documentation is kept in sync with the code. We colocate it since that makes both reading and maintainance easier for agents. Cross-file decisions and rationales are documented usually in their folder's module code file. Framework-level decisions go into package toolchain setup files. The docs/ folder can serve as a place for documentation that isn't tied to a clear code location, though most documentation can be colocated with what it documents.
- Onboarding materials: we maintain up-to-date onboarding materials at the root level and package level in AGENTS.md files, and reference as further readings files that are only situationally useful, e.g. more detailed tool usage docs, specific situational workflows, and custom knowledge about the master thesis topic itself that agents may need in order to understand issues and code better.
- Ergonomics: we design the whole project for smooth usage by ai agents. Feedback from the agents is appreciated and incorporated to make custom tool usage low-friction, to pick canonical workflows that cover more of the frequent use cases so that agents have to deviate less often, and to document and refactor code to be easier to read and maintain.

## Reproducibility
We design the project for full reproducibility from scratch. Anyone who clones the repo and opens the devcontainer should be able to build, test, benchmark, and run all code, tools, and data pipelines from scratch, without any deep knowledge about the project.
We don't strictly enforce full reproducibility for every commit, not even every commit on main, since that would slow down development too much. Instead we continuously push towards restoring full reproducibility, and reach it every once in a while.
Reproducibility includes:
- The devcontainer fully defines the development environment.
- The packages' toolchains are fully defined in their setup files and scripts folders.
- The code can be built / linted / type-checked / tested / benchmarked from scratch successfully.
- The code achieves a working coherent feature set.
- The code comments and other documentation describes the current commit state correctly.
- The onboarding describes the current commit state and the established best workflows for the future correctly.
- All data artifacts can be deleted and re-generated using documented or even automated data pipelines.

