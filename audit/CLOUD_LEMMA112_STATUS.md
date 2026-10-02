# Completed original Lemma 11.2

`lemma112_proved : Lemma112Target` proves the original p65 estimate for the actual Gaussian-smoothed J-tilde functions. One positive absolute constant and one modulus threshold work for every real primitive chi, every primitive psi in the original ambient Psi, and every point on the critical line in the strict height window. There is no assumption(A) or Psi1 restriction.

## Original objects and ranges

The J-tilde functions are the original infinite sums of chi(n)psi(n)n^-s with the integrated Gaussian weights from p62. Their summability and the exchanges with finite z integrals are proved. The dual weight retains D*t0, and the actual product character has proved primitive conductor Dp. The inverse-character functional equation and all conjugations use this actual product.

The conclusion bounds `norm(J1(s)-Z(chi*psi,s) J2(1-s,psi^-1))` by C times the original E2. E2 is exactly L^-68 times the norm integral of the strict n<P^.504 polynomial over the original closed interval[-L^20,L^20], with the actual omega1(iv). No auxiliary error floor is added. Instead, Fourier recovery of the n=1 coefficient proves a lower bound for this same integral, allowing tiny Gaussian contour errors to be absorbed.

The strict height bound, strict coefficient cutoff, both closed z endpoints, and the exact adjacent-interval cancellation are retained. The printed E/E2 discrepancy is resolved by using the exact displayed definition, without altering the statement's content.

## Proof and independent review

Actual Mellin inversion and absolute convergence supply the infinite sums. A removable dslope representation proves regularity of the true Z-difference kernel at the contour origin. The conductor-Dp bounds, exact reciprocal-series split, finite short Mellin model, left contour, horizontal sides and reciprocal tails are all proved. The variable-scale approximation is integrated over the two adjacent original z intervals; its L-term cancels exactly.

The separately conducted [semantic review](CLOUD_LEMMA112_SEMANTIC_REVIEW.md) accepts the original statement, all objects and quantifiers, and the key analytic bridges. No additional result-shaped hypothesis or substitute coefficient is introduced.

## Central verification

2026-10-02, Linux x86_64, Lean4.30.0:

-19 frozen modules promoted with import-path changes only; hashes recorded
-Focused dependencies build PASS:3816 jobs
-All144 public declaration interfaces, including definitions, use only propext, Classical.choice and Quot.sound
-All12 expanded-target, endpoint, conductor, conjugation, Gaussian and error-integral regressions pass without warnings
-Complete integration build PASS:4974 jobs
-Coverage720 Spec/985 full-project imports; placeholder/structure checks PASS for1084 Lean sources
-Strict heuristic audit retains370 candidates and nonzero exit; three new candidates are reviewed local consequences. Some component style warnings remain; the capstone/regressions are clean

Evidence: [regressions and axiom commands](CloudLemma112Regression.lean), [axiom output](cloud_lemma112_axioms.log), [source hashes](cloud_lemma112_source_hashes.json), [verification/log fingerprints](cloud_lemma112_verification.json).

The ledger is **30/51 original statements completed**, with no repaired numbered statement centrally accepted yet. Repaired15.2 remains in integration. The main theorems and their formal effectivity certificates remain unfinished.
