# Step 117 — Actual Gaussian inputs and cutoff errors for Lemma 6.1

The full original [Lemma61Target](../ZhangLS/Spec/Lemma61Parameters.lean)
remains **UNPROVED**. It retains the original Psi family, strict region
abs(Re s-1/2)<2alpha and abs(Im s-Im s0)<L^405+2, actual L/K/N,
actual finite sum n<T^3 in E1, and uniform positive constants C,k and
a natural threshold before all D,p,psi,s. No A or Psi1 restriction is added.
Original completion ledger: **18 complete, 2 in progress, 31 unstarted**.
The goal still covers all 51 numbered results. Full Lemma5.9 completed at Step116.
Faithful Lemma5.6 q=1 and the full Lemma6.1 remain in progress.

## Proved actual inputs

The original g-star is g above 1/2 and zero at and below 1/2.
Both weighted series have finite support and exactly equal actual finite
Dirichlet polynomials. P4*T^2=P*t0 exactly. K/N and the strict n<T^3
short polynomial are entire. E1 has a continuous, interval-integrable
nonnegative integrand and is strictly positive. Its Gaussian factor is
exactly the original omega1(iv).

For the actual character L(s+w,psi), absolute convergence proves the
right Gaussian Mellin identity and the exchanges of summation/integration.
The actual right integral is K plus an explicit infinite cutoff correction.
At the cutoff n>=2x, the Gaussian endpoint dominates L^10+2log n when
L>=3 and log x<=2L^9. The real weight is therefore <=exp(-L^10)n^-2.
For Re s>=0, the actual correction is summable and its norm is at most
the absolute inverse-square mass times exp(-L^10). Both actual scales
P4 and T^2 satisfy the logarithmic budget, giving the actual K and
dual N(1-s,psi-inverse) cutoff errors on the original region.

Remaining work: full finite contour shift, reciprocal finite sum truncation,
and the uniform actual Z-difference estimate giving the original E1 integral.
No contour, Gamma error or approximate functional equation is assumed.

## Verification

Four modules build. All 32 new interfaces depend only on standard Lean
axioms. Three expanded actual-object regressions pass. All 514 sources
pass placeholder and structure checks. Strict static audit keeps its
nonzero exit with the same 124 reviewed candidates; no new candidates.
See [manifest](step117_interface_manifest.json), [build](step117_promoted_build.log),
[axioms/regressions](step117_regression_axioms.txt) and [static audit](step117_spec_audit.txt).

Repository-wide kernel verification is **PASS**: 367 trusted modules,
445 imports and 66 regressions. All 514 Lean sources are frozen in
[fingerprints](step117_source_fingerprints.json). Fresh Step117 terminal PASS and all unchanged fingerprints have been checked.
Interval: 2026-10-02 03:01:07–2026-10-02 03:32:21 Asia/Shanghai. See [kernel report](step117_kernel_verification.txt). See [coverage](step117_coverage.json)
and [full log](step117_full_verification.log).
