---
title: Data Science Experiments
slug: data-science-experiments
summary: Pipeline templates and idea backlog for probing Viterbo's conjecture with datasets of 4D convex polytopes.
---

# Data Science Experiments
<!-- Style: literal, explicit, rigorous; mark assistant additions with <proposed>. -->

We collect many ideas for experiments that use data science methods to probe Viterbo's conjecture.

## Dataset Template

The main pipeline pattern for datasets is as follows:
- Generate many random convex polytopes in $4$ dimensions, using various random distributions, using enumeration of combinatorial types, using known cases of interest from the literature, and perturbations to other polytopes, etc.
- For each polytope, compute rich data, including the systolic ratio.
- Collect all the data into a large stored dataset.

## Experiment Template

On top of the dataset, we run various experiments that follow this pattern:
- load the subset of the dataset that is relevant for the experiment
- run the data science experiment's stages, e.g. pre-processing, processing, analysis, visualization
- save the data artifacts, which can be consumed by further experiments
- save the visualization assets, which are consumed by the thesis writeups

Besides code, experiments include
- writeups of the interpretation of the results, and the generating idea of the experiment
- code for visualizations, interpretation helpers, and regression tests to notice when experiment results change due to code changes upstream

## Ideas

The following is the long list of ideas. When an idea is rising to the priority queue's top, it is moved into a gh issue. Project owner and collaborating agents then make the idea concrete, measurable and actionable, and delegate it to agents for implementation, analysis, and writeup. Drafted experiments are reviewed by the project owner, usually handed back for a fresh retrial with adjusted goal and hints, or improvements to code and writeup, until the experiment is satisfactory and can be included in the thesis as an informative result.

TODO
