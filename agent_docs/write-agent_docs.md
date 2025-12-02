# Writing Agent Docs
- Goal: Provide onboarding and reference docs for agents working on the project. Write in a way that is maximally helpful for agents.
- Onboarding knowledge goes into `agent_docs/` and `AGENTS.md`.
- Documentation and thesis writeup are also used for onboarding and follow similar principles. See `write-latex.md` for style guidance.

- Agents have zero prior context about the project, but are already familiar with all popular toolchains, frameworks, patterns and domain knowledge.
- Instead of explaining such familiar concepts, we just need to tell the agent which ones we are using when there are multiple popular options.
- We also name-drop familiar concepts to help the agent consider them as available options, IF agents demonstrate the need for such reminders.
- We have to introduce custom concepts, code architecture, and custom math domain knowledge from scratch for each agent. That is why we prepare high quality onboarding docs in `agent_docs/` and provide docstrings and comments in code next to the relevant code. The colocation helps agents find the relevant docs precisely when they need them.

- Agents use command line tools and text files; no IDE, no interactive GUIs; they can view image files, so plots and diagrams are possible.
- Agents read files and command output in one go without pause, so it is important to use digestible, clear, unambiguous language with low cognitive overhead.
- Agents don't have the time to cross-check every single claim in the repo; we must ensure that all claims are kept up to date and are literally correct and unambiguous to rule out misunderstandings.

- Agents can draft and edit these docs, but the project owner reviews and must approve any changes to `AGENTS.md` or `agent_docs/` (policy, expectations, onboarding); treat these files as high-cost.

- Agents can report about the frictions they experience while working on the project, including with onboarding docs, with environment setup, with toolchain usage, or with current code or documentations or thesis writeup.
- Agents are less experienced in suggesting the best improvements and tradeoffs between different setups. Instead the project owner has to make the final call, and agents merely point out issues, provide feedback and propose multiple solutions.
- We should collect such feedback, and iteratively improve the repository and project conventions.
