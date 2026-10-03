# Structured covariance: bounded representation audit

2026-10-03. Accepted at the source-and-algebra level, under the stated hypotheses and coefficient/support conditions:

    H(GA,FB) = [R(υ_D*a,ν_D*b) + conjugate(R(ν_D*b,υ_D*a))]/(aM)
                 + O(a⁻¹L⁻⁴⁵).

The symbol a in the denominator is the source normalization; a and b inside convolution denote the coefficient sequences of A and B. R retains the exact inherited gamma branch and the full additive arithmetic sum. The error is the exceptional-family extension error with the stated negligible contour/tail terms. The original bounds for A and B must be fixed uniformly and independent of p and ψ; both supports are at most P^.504. The family includes both ψ parities and every primitive real χ of sufficiently large conductor, without a squarefreeness restriction. Assumption (A), L(1,χ)<L⁻²⁰²², is unchanged.

This is a bounded representation, not an evaluated main sum, a signed L⁻⁸ gain, a Lean theorem, or a completed repair. The mixed entry D_AB and actual target calibration remain unresolved. The initial C₁-completion overclaim is explicitly retracted: C₁ and T₁ still need their own family-completion, tail, and contour-shift ledgers in this reviewed scope. No subsequent unfinalized C₁/T₁ work is included.

Read [DERIVATION.md](DERIVATION.md), [INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md), and the explicit [correction record](CORRECTIONS.md). The [revision log](REVIEW_REVISIONS.md), [immutable source citations](SOURCES.md), and [edition provenance](EDITION_NOTES.md) complete the record.

Run `python run_checks.py` from this directory, or invoke that file from any working directory. It verifies bundle hashes and local links, runs both finite-check scripts, and compares their outputs with the saved results. See [REPRODUCING.md](REPRODUCING.md). All checks were rerun successfully; they are finite/symbolic regressions, not proofs of the uniform analytic estimates. No Lean compilation or publication was performed.
