# Step 18 status

## Completed

- Added the full smoothed Dirichlet-series object for Lemma 5.7.
- Extended the paper summand by zero at `n = 0` so the finite `Icc 1 D` segment embeds directly.
- Proved the coefficient factor is nonnegative using the unconditional Step-17 theorem.
- Proved that global Gaussian nonnegativity implies nonnegativity of every full-series term.
- Proved the Step-17 finite sum is a literal finite sub-sum of the full series.
- Proved that summability + term nonnegativity makes the full series dominate the finite sum.
- Upgraded the explicit `(1/8) * D/φ(D)` arithmetic lower bound to the full series under exactly two analytic obligations.

## Remaining analytic obligations

1. Prove `ZhangGaussianWeightNonnegative D` for `D > 1` from the cumulative Gaussian formula.
2. Prove `Lemma57FullSmoothedSummable χ (zhangGaussianWeight D)`.
3. Identify the full smoothed sum with the Mellin integral
   `ζ(1+s) L(1+s,χ) D^(4s) ω₁(s) / s`.
4. Shift the contour and bound the shifted integral under hypothesis (A).

## Audit

- `spec_audit_step18.txt`: 38 findings, all legacy high-risk candidates.
- `spec_sorry_step18.txt`: empty.
- `syntax_step18_recursive.txt`: 94 modules, bad=0.
- legacy `lean_syntax_review.py` remains non-recursive and reports 77 top-level modules.

## Kernel status

Not kernel-verified: Lean/Lake are unavailable in the current container.
