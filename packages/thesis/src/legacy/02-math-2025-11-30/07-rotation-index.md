---
title: Rotation Numbers and Indices
summary: Rotation number / CZ bounds and their polytope counterparts.
---

Smooth case
- For a nondegenerate Reeb orbit \(\gamma\) on a smooth convex \(\partial K\subset\mathbb R^4\), linearizing the Reeb flow on the contact plane yields a path in \(\mathrm{Sp}(2)\); its lift has a rotation number \(\rho(\gamma)\). Conley–Zehnder index \(\mathrm{CZ}(\gamma)=\lfloor\rho\rfloor+\lceil\rho\rceil\).
- Hofer–Wysocki–Zehnder and Hu–Long imply: for convex \(K\), every closed characteristic has \(\rho>1\); there is an action minimizer with \(\rho\le 2\); if nondegenerate, \(\mathrm{CZ}=3\) [@HoferZehnder1990; @Irie2014; @AbbondandoloKang].

Combinatorial analogue (CH2021)
- For a non-Lagrangian polytope, a Type 1 combinatorial Reeb orbit \(\gamma\) has a well-defined combinatorial rotation number \(\rho_{\mathrm{comb}}(\gamma)\) and index \(\mathrm{CZ}_{\mathrm{comb}}\) [@CH2021].
- Smoothing correspondence: any Type 1 orbit with bounded \(\rho_{\mathrm{comb}}\) is the \(C^0\)-limit of Reeb orbits on smoothings with matching rotation number; conversely, action-minimizing smooth Reeb orbits limit to combinatorial ones with \(\rho_{\mathrm{comb}}\le 2\).
- Practical bound: when searching for minimizers, restrict to combinatorial orbits with \(\rho_{\mathrm{comb}}\le 2\) and a bounded face-complexity constant (CH2021 Cor. 1.5).
