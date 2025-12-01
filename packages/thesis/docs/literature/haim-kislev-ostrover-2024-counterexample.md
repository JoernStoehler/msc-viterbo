# Haim–Kislev & Ostrover 2024 Counterexample

## Context
- Source: `packages/thesis/build/arxiv/2405.16513v2/main.tex` (TeX from arXiv v2). Avoid PDF.
- Shows Viterbo’s conjecture fails already in \(\mathbb{R}^4\) using a Lagrangian product of rotated pentagons; extends to all \(n\ge2\) via product tricks.

## Claims Checked
- Theorem (label `counterexample_thm`): Viterbo’s conjecture fails for every \(n\ge 2\).
- Proposition `counterexample_prop`: for \(K\) a unit regular pentagon and \(T=R_{90^\circ}K\),
  \[
  c_{EHZ}(K\times T)=2\cos(\tfrac{\pi}{10})(1+\cos(\tfrac{\pi}{5})),
  \]
  achieved by a 2-bounce \(T\)-billiard along a diagonal.
- Volume computation gives \(\mathrm{sys}(K\times T)=1.04721\dots>1\) (used in our literature overview).

## Key Equations / Source TeX
Source TeX (lines ~85–110):
```
\begin{theorem}
\label{counterexample_thm}
Viterbo's conjecture fails for every n \ge 2.
\end{theorem}
```

Source TeX (lines ~100–140):
```
\begin{proposition}
\label{counterexample_prop}
... K \times T ...
 c_{EHZ}(K \times T) = 2 \cos(\tfrac{\pi}{10}) (1 + \cos(\tfrac{\pi}{5})).
\end{proposition}
```

## Caveats / Scope
- Construction is specific: Lagrangian product of 2D polygons. Equality examples exist where capacities coincide; not every product gives a violation.
- Numerical value depends on the chosen normalization of the pentagon (circumradius 1 in the TeX source).

## How We Reuse
- Regression test instance for our algorithms (must reproduce the 2-bounce orbit and capacity value).
- Benchmark for pruning logic: minimum-action orbit uses a Lagrangian 2-face; keep the fallback search path.
- Documentation anchor: cite this as the canonical 4D counterexample when motivating algorithms and datasets.
