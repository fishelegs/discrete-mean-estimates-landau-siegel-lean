# Verified eighth-order decay of the actual Delta Mellin transform

This is a genuine stronger analytic prerequisite for Propositions7.1 and14.1, not a proof of either proposition. It prevents using the finite-height5.6 cancellation theorem outside its valid range.

For the original delta(s)=Mellin(Delta)(s), `lemma54_eighth_mellin_frequency_bound` proves, for D>1 and logD>=2000 and every real t,

||delta(1+it)|| <= C8 (logD)^7200 / (1+t^2)^4.

C8 is a proved positive absolute explicit expression in pi, exp19, exp20 and17!, independent of D, character, coefficient sequences and t. An explicit mathematical threshold ceil(exp2000)+2 is provided. No(A), prime cancellation theorem, or assumed higher derivative estimate is used.

## Actual proof, with no substitute transform

The weighted oscillatory integrals I_n use the existing genuine kernel and exact derivative factor[-2pi i(exp(u)-1)]^n. I0 equals the original Delta on x>0. For n<=8, real Gaussian domination, integrability and the actual shifted-contour tails are proved. Dominated differentiation gives I_n'=I_(n+1). Every Mellin integration-by-parts endpoint vanishes by the proved bounds, and the full product s(s+1)...(s+7) is retained.

The genuine moment integral of x^8||I8(x)|| is finite and bounded by C8(logD)^7200. Its small-x range and both large-x tails are integrated separately. At Re(s)=1, each shifted denominator has norm at least||s||, and ||1+it||^8=(1+t^2)^4 exactly.

The additional `lemma54_eighth_window_and_tail` theorem retains separate actual global B and central-window C bounds for a continuous amplitude f:

integral ||f(t)||(1+t^2)^(-4) dt <= C*pi + 2B/H^7.

Thus H=D/2 leaves the explicit256B/D^7 before outer arithmetic sums. The generic amplitude hypotheses are explicit; the full prime-kernel and conductor-sum applications still require their own proofs and are not hidden in this component.

## Central verification

2026-10-02, Lean4.30.0/Linux x86_64: seven frozen production sources and one self-contained audit match their hashes exactly. All65 public declarations use only the standard axioms; four actual-kernel/constant/threshold regressions pass. Focused3713-job and full5158-job builds PASS. Coverage904 Spec/1169 project imports; placeholder and structure guards pass for1277 Lean files. Strict heuristic audit remains nonzero,388 candidates, with one reviewed return of a derived central-window inequality. Harmless proof-style warnings remain in components; the regression/axiom audit is clean.

Evidence: [regressions/axioms](CloudEighthMellinRegression.lean), [axiom output](cloud_eighth_mellin_axioms.log), [source hashes](cloud_eighth_mellin_source_hashes.json), [verification/log fingerprints](cloud_eighth_mellin_verification.json).

The original7.1/14.1 conclusions, full conductor averages and outer l-tails remain open. Numbered ledger unchanged:34 original statements plus2 repaired statements,36/51.
