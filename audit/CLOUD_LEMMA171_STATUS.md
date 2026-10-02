# Cloud milestone: original Lemma 17.1

Verified 2026-10-02 on Linux x86_64, pinned Lean 4.30.0 / mathlib v4.30.0.

`lemma171_proved : Lemma171Target` and `lemma171_original_uniform` prove the original absolute asymptotic sum for 1 <= n < D^4: the actual nu(n)^2/n sum equals a+o(1), with a=(6/pi^2)L'(1,chi)^2 product_{p|D}p/(p+1). The actual real-axis derivative, original normalized(A), strict cutoff, and uniform quantifier order forall epsilon>0, exists D0, forall D>=D0, forall chi are retained. This is an absolute o(1), not a relative-error assertion.

## Proved mathematical inputs

- Exact nu-squared local Euler factors, actual convergent global Dirichlet identity, and holomorphic correction C_D(s)=zeta(2s)^-1 product_{p|D}(1+p^-s)^-1 on Re(s)>1/2
- Actual Gaussian Mellin inversion with absolute summability, right-line integrability, and justified infinite sum/integral interchange
- Exact cubic principal part and residue, plus residue-minus-a bound by an absolute constant times(log D)^-2018
- Genuine finite rectangle formula, horizontal decay, integrability on both infinite vertical lines, infinite contour shift, and uniform left-line o(1) bound
- Uniform Gaussian unsmoothing, using proved Lemma3.1 and a separately controlled infinite tail; inclusive-to-strict cutoff correction exactly D^-4

No contour, residue, left-integral, or tail error estimate remains as an extra hypothesis of the final target.

## Checks and scope

- 20 new modules, 143 theorem interfaces, 30 definitions, 15 expanded semantic regression examples
- Central focused dependency build PASS (3875 jobs), central regression PASS, all20 source hashes equal the independently reviewed frozen package
- All143 theorem axiom reports contain only propext, Classical.choice and Quot.sound
- Independent paper-to-Lean review ACCEPT against arXiv:2211.02515v1, printed p96 and pp108–109
- Fresh full `lake build` PASS (4910 jobs), including Spec and full-project aggregates
- Import coverage:658 Spec modules and923 full-project imports; placeholder and structure checks PASS for1017 Lean files
- Strict semantic heuristic audit:360 candidates, exit1 preserved. The three new hits are reviewed local facts: ContourFinite:159 returns continuity already proved by finite summation; LeftIntegral:33 returns the real-part norm lower bound just derived; LeftIntegral:75 supplies the proved Re(z)=-1/4>-1/2 domain inclusion. None assumes a final estimate. The original357 candidates remain historical review items
- Source fingerprints and build-log hashes are retained in the companion reports

This does not claim a fresh independent re-elaboration of every old Spec source or traversal of every old audit regression. Formal effective extraction of thresholds remains a separate global paper obligation. Per-commit remote CI is checked after publication.

The numbered ledger advances to27/51 complete; Proposition2.1, literal5.6 and8.1 remain in progress.
