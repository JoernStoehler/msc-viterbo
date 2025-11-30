---
title: Ongoing Todo (Draft)
slug: thesis-todo
internal: true
summary: Short-term and milestone checklist for thesis writing and algorithms.
---

# Ongoing Todo

## Today (2025-11-25)
Focus: Milestone — writeups

- [x] move legacy/partially wrong docs to `packages/thesis/archive`
- [x] create `packages/thesis/src/internal/todo.mdx` for today
- [x] write up the project's research question
- [ ] write up a literature overview
- [ ] write up the mathematical introduction up to the point where we proved various theorems about the critical points of the action functional and in particular the existence of one point with minimum positive action
- [ ] write up the HK2019 algorithm
- [ ] write up the CH2021 algorithm (with our guesses for how to fill the unspecified gaps of their paper)
- [ ] write up our own novel algorithm

## Future Milestones (not today)

- [ ] Rust implementation of our algorithm
- [ ] Lean formalization of theorems and selected proofs to gain confidence in coverage
- [ ] Writeup of our second novel algorithm that handles Lagrangian 2-faces effectively
- [ ] Writeup of the Minkowski-Billiard algorithm similar to HK2024
- [ ] Rust implementation of the other algorithms (HK2019, CH2021, Minkowski-Billiard)
- [ ] Lean proof that our first and second novel algorithms work
- [ ] Performance optimization of the Rust implementation (benchmarks, profiling, ablation studies, writeup of insights)
- [ ] Creation of a small test dataset and a large data-science-ready dataset of polytopes via Python+Rust
