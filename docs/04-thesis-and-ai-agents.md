# Thesis and AI Agents
<!-- Style: literal, explicit, rigorous; mark assistant additions with <proposed>. -->

## Thesis

The thesis is structured as follows:
- A classical self-contained printable thesis PDF
- A github repository with all code, data, artifacts, and interpretations. With documentation and trivial instructions to reproduce all data and artifacts from scratch.
- A github pages website that hosts the thesis formatted for web, with interactive instead of static visualizations in some places, and with links to the code repository and data artifacts. In addition we include extracted documentation from the code, and finally the repository's own documentation of development workflows and project management.

The github repository minimizes the amount of implicit knowledge held by the author Jörn. It contains the literature bibliography, notes and writeups, and workflows and conventions that were used during development. Most code, proofs, and documentation are written by AI agents, based on sketched high-level instructions from Jörn and verifiable feedback from static and runtime analysis tools and agentic reviewers. In fact, we strongly suggest not to attempt to work through the repository without AI assistance, since we use a variety of languages, frameworks and tools that AI agents are familiar with all at once, but that we don't expect a human researcher to acquire knowledge of just to work through the repository.

The thesis writeup is not detailed on a level where the codebase can be rederived from scratch, since we abstract over a lot of numerical details in the thesis itself.
The Lean4 code serves as a more detailed writeup that gives us guarantees for a simplified algorithm without floating point arithmetic, and the Rust code serves as a more detailed writeup that is efficiently executable in practice for common/most scenarios.

We make reproduction easier by defining a `.devcontainer` environment. While it is not frozen perfectly, it should be fixable even in the near future.

## AI Agents

We use modern AI agents extensively for:
- turning my short notes into full detailed writeups
- maintaining writeups, documentation, code, code comments, tests, data and artifacts across refactorings and fixes
- writing code, tests, and code comments / documentation for typical software engineering tasks
- writing Lean4 formalizations of my less formal and perhaps less rigorous mathematical reasoning
- maintaining the project's development workflows, environment, and overall project management roadmap
- aiding in idea generation and result interpretation beyond code execution

Above has mostly become feasible since the GPT-5 model series, and the upcoming Gemini 3 Pro and Opus 4.5 models will likely push even further what envelope of tasks can be delegated reliably, or delegated on a trial-and-error basis where the cost of failure notably is tiny since it only requires a rollback and a retry with additional planning help from me as the project owner and research expert.

The main tool this project has been configured for is `codex cli` from OpenAI.
We provide a custom script `scripts/worktree-prepare.sh` so we can prepare multiple independent development environments for agents via git worktrees, and we provide extensive ai-focused onboarding documentation in `AGENTS.md` and `packages/*/AGENTS.md` files.
The environment is a `.devcontainer` so agents can see the full environment definition, and it includes all necessary tools pre-installed and pre-configured that ai agents are used to working with.

We also pay attention to how useful/harmful AI agents were during the thesis project, as a single but moderately large data point on the impact of AI on mathematical research.
