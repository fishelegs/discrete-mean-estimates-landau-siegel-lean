# Completed original Lemma 8.3

`lemma83_original : Lemma83Target` proves the complete original statement on p46 of arXiv:2211.02515v1, using the actual Section7 coefficients. For every fixed positive paper shift constant c, C>0 and D0 are chosen before D, chi, j, d, r and s. Positive d,r satisfy the original strict dr<PT^-2 cutoff. The constructed correction is analytic for Re(s)>9/10, obeys the original finite-prime growth bound, and differs from the exact Pi(d,r) by at most C L^-8 on the **closed** 5alpha disc. No(A) is assumed. The same beta definitions from2.13/5.2 are used.

## Genuine arithmetic and continuation

Kappa is the actual Moebius convolution of three shifted power coefficients. Modified kappa remains the actual supported infinite sum; xi remains the Section7 divisor sum. Supported-series identities, multiplicativity, absolute prime-power convergence and a proved converse-Euler convergence theorem establish the genuine global series on Re(s)>1. A separately normally convergent product is holomorphic on Re(s)>9/10 and satisfies the exact cross-multiplied L/xi identity there on the convergence half-plane. This is an actual analytic continuation, not a totalized quotient assumed analytic through zeros.

All three local cases are proved: primes outside dr, primes dividing r, and primes dividing d but not r. Ramified factors are1. The zero-shift product equals the original Pi exactly. When chi(2)=1,2 divides d and2 does not divide r, Pi vanishes; the proof and regression preserve the **additive** error and never divide by Pi.

The regular product has a summable O(alpha) perturbation. Finite exceptional factors use division-free product perturbation and proved Rankin bounds, giving O(alpha(1+log y)^(K+2)) for log(dr)<=y. The actual cutoff gives y=L^9; fixed polylog absorption yields the original L^-8 rate. The growth constant constructed is independent even of c; only the threshold uses its fixed value.

The AppendixA proof has inconsistent xi/d/h/h1 notation and an extra printed lambda(dh) factor. The proof reconstructs the exact Section7 definitions and the original p46 statement, rather than importing that inconsistent auxiliary display. This is completion of the original numbered **statement**, not a substituted repaired conclusion.

## Central verification

Linux x86_64, pinned Lean4.30.0, 2026-10-02:

-33 new source modules:32 for8.3 plus one shared generic divisor-kernel theorem; the latter assumes no unfinished15.2 result
-Only local import paths changed during promotion; original and promoted source hashes are recorded
-Focused dependencies build PASS:3910 jobs
-All275 public declaration interfaces (including definitions and regression declarations) have only standard axioms
-Five regression statements in four required groups pass without warnings: full target expansion; actual series/continuation; exact zero shift; actual prime2 zero and its additive bound
-Complete integration build PASS:4955 jobs
-Coverage701 Spec/966 full-project modules; placeholder/structure checks PASS for1064 Lean sources
-Strict heuristic audit has367 candidates and nonzero exit; six new candidates were reviewed as local derived facts/generic summability transport. Harmless style warnings remain in some components, while capstone/regressions are clean

Evidence: [expanded regressions and axiom checks](CloudLemma83Regression.lean), [axiom output](cloud_lemma83_axioms.log), [source fingerprints](cloud_lemma83_source_hashes.json), [verification and log hashes](cloud_lemma83_verification.json).

The ledger is now **29/51 original statements completed**. No repaired numbered statement has yet passed central acceptance. Downstream8.4 and the full paper remain unproved, and final effective-computability certificates remain separate.
