# Unconditional prime-mass prerequisite for original Lemma 8.1

## Verified result

For all sufficiently large natural D, the original actual mass in the strict prime window satisfies

`(1/4) P(D)^2 / L(D)^77 <= lemma33ActualPrimeMass D`.

Consequently, for every fixed C>=0 and every epsilon>0, a uniform D0 makes

`C P(D)^2 L(D)^(-78) <= epsilon * lemma33ActualPrimeMass D`.

The statements contain **no character, Assumption(A), assumed prime asymptotic, or assumed zero-free region**. The strict original prime window and actual weighted prime sum are unchanged. This proves the normalization needed after the aggregate replacement-error estimate in8.1; it does **not** finish8.1 or establish the full asymptotic(2.9). The numbered ledger remains **28/51**.

## Proof and source review

The actual Mangoldt series gives classical3–4–1 positivity. Actual finite local zeros and their multiplicities give the zero-detection inequality, hence the explicit high-height zeta strip of width1/(10^7 logD). The low-height compact collar uses the actual pole-removed zeta factor, with value1 at the pole, not a totalized ordinary-zeta pole value. Uniform threshold assembly supplies the complete thin strip. The ordinary-zeta statement explicitly excludes s=1.

The actual principal Perron/Mellin rectangle is shifted to1−1/(2·10^7L), with heightD/2 and smoothing width exp(L/3). Explicit left, horizontal and tail budgets give the actual sharp prime-log prefix estimate; proved unsmoothing, prime-power removal and strict-endpoint arithmetic give the mass lower bound. The final bridge identifies the exact mass already used by the faithful8.1 target. Central source review checked all eight modules and this chain, including the absence of(A).

The compactness step supplies existence of a fixed low-height collar. No separate formal effective-computability certificate is asserted; that global obligation remains visible.

## Verification

2026-10-02, Linux x86_64, pinned Lean4.30.0:

- Eight frozen modules re-elaborated independently, without warnings
- Required dependency build PASS:3921 jobs
- Four original-object/quantifier/pole semantic regression examples PASS
- All36 new lemma/theorem interfaces checked by `#print axioms`: only propext, Classical.choice, Quot.sound
- Complete integration `lake build` PASS:4919 jobs
- Coverage667 Spec/932 full-project imports, placeholder/structure checks PASS for1028 Lean files
- All1017 old nonaggregate Lean files unchanged from the preceding full snapshot; two aggregate import lists intentionally updated
- Strict heuristic audit has361 candidates and nonzero exit. One new candidate is a locally derived elementary norm bound, documented in the verification JSON; no surrogate assumption is introduced

This is a focused eight-module extension of the [full cloud snapshot PASS](CLOUD_FULL_RECHECK_STATUS.md), not another fresh traversal of every old source. Evidence: [expanded regressions and all36 axiom checks](CloudLemma81MassRegression.lean), [axiom output](cloud_lemma81_mass_axioms.log), [source hashes](cloud_lemma81_mass_source_hashes.json), and [verification/log fingerprints](cloud_lemma81_mass_verification.json).
