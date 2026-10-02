# Cloud milestone: original Lemma 3.6

Verified 2026-10-02, Linux x86_64, pinned Lean 4.30.0 and mathlib v4.30.0.

`lemma36_proved : Lemma36Target` proves the original condition-(3.6) exceptional-character estimate under the original normalized (A), with a positive absolute constant and uniform sufficiently large modulus threshold. The actual prime/primitive family, actual truncated convolution varsigma, actual X4 endpoint and integral, strict good threshold L^-633 and original mass normalization are retained.

## Mathematical chain

1. Exact inverse-coefficient prime-power formulas and multiplicativity prove |varsigma(n)| <= |nu(n)| tau_2(n)
2. Actual short-polynomial character orthogonality (Lemma3.3 first assertion), centered at real part 1/2, reduces the X4 mean to the original Lemma3.2 weighted energy
3. The D^4-to-D^8 reciprocal integral equals 4 log D; proved integrability and weighted Cauchy give loss at most 34(log D)^2
4. L^-2007 becomes L^-2005, then division by the squared bad threshold L^-1266 gives exactly L^-739
5. The actual union of the three bad families is identified and bounded, preparing the explicit Psi2 complement bridge for Proposition2.1

No final arithmetic, mean, integral or counting bound is supplied as an additional assumption to the completed target. The paper's misnumbered references are documented in the dependency map.

## Verification

- Six new modules, 45 theorem interfaces, 16 regression examples across three files
- Focused dependency/build check: `lake build +ZhangLS.Spec.Lemma36GoodFamily:olean` PASS, 4638 jobs
- Every public theorem's dependency axioms are contained in propext, Classical.choice, Quot.sound
- All three regression files pass without warnings; full original bad-set target and strict-threshold membership are expanded
- Independent statement-fidelity review accepted the coefficients, ranges, finite indexing, uniform quantifiers and exponents
- Source fingerprints: `cloud_lemma36_source_hashes.json`
- Fresh import coverage: 638 Spec modules, 903 full-project imports; placeholder/structure checks pass for 996 Lean files
- The strict heuristic audit retains the historical 357 review candidates and nonzero exit; it is not represented as clean

- Fresh cloud `lake build` PASS (4881 jobs), including both Spec and full-project aggregates

A fresh rebuild of the old Hasse dependency initially exited137 while several large modules ran together. The unchanged WronskianAux module passed when rebuilt alone, and the complete required original3.2 closure subsequently passed. No mathematical source change or weakened theorem was used to resolve this execution failure.

This report does not claim every old Spec file and audit regression has been independently rechecked in the cloud. The full-project rebuild passed; separate per-Spec re-elaboration and traversal of every old regression remain pending. Baseline58a9273 and the preceding Lemma11.1 commit ab3a293 GitHub CI are confirmed successful; this milestone’s remote CI is followed after publication. Build summaries retain command, exit code, job count and SHA256 of the complete unabridged local log.

The numbered ledger is now26/51 completed. Proposition2.1, literal5.6,8.1 and17.1 remain in progress. Effective extraction of all global constants/thresholds is a separate final-paper obligation, not established by this milestone's classical uniform-existence target.
