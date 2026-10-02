# Section 18 numerical model audit

A standard-library Python rational interval certificate establishes a numerical
obstruction in twelve explicitly specified finite Hermitian models associated
with Section 18 of [arXiv:2211.02515v1](https://arxiv.org/abs/2211.02515v1):

- At the paper coefficients (2.26), every model has Q > 0.05
- With the H11 coefficient fixed to 1 and iota2, iota3, iota4 free over C,
  every model has global minimum > 0.024

The target Q < 0.001 therefore cannot be reached by changing only those three
complex coefficients in these fixed models. This does not rule out other
analytic corrections, parameters, mollifiers, constructions, or proofs, and
it does not disprove the main theorem. Equality to actual normalized character
means is not certified; no vacuity argument about assumption (A) is used.

## Representative branch

For `.5:exact:upstream`, which combines the preceding log(P2)log(P3) denominator,
the symbolic Section 12 high-residue model, and Appendix B's terminal tail
expression, the certified enclosures are:

- Paper-coefficient Q:
  [0.0553415395252549996131, 0.0553415395252549996132]
- Global minimum with H11 coefficient 1:
  [0.0249294244390953127716, 0.0249294244390953127717]

The twelve branches distinguish two denominator formulas, two high-range
formulas, and three tail/cancellation formulas. Every branch uses κ2 in the
Section 17 coefficient expansion in place of the undefined κ4. The derivations,
exact interval endpoints, and full matrices are in the
[audit package](audit/section18_numerical/README.md).

## Source and certification limits

The Appendix B branch is a symbolic terminal-expression model, not a repaired
actual Lemma 15.1. Coefficient-basis reconstruction remains pending: (15.1)
writes B in the χψ basis, while the convolution before (15.5) is written in the
ψ basis. The interpretation and propagation of b, and the tail endpoints, need
separate verification. This package makes no confirmed-error claim about that
pending reconstruction. The analytic asymptotics, error bounds, uniformity, and
identification with actual character means remain unproved here.

All three +0.004 shifts in each Section 8 cross-term display (8.21), (8.22) are
present in the official source and retained. There is no missing-shift finding.

This is a reproducible rational computer-assisted certificate with documented
symbolic model identities, not Lean-certified arithmetic asymptotics. Positivity
of interval LDL pivots and the final Schur complement establish the global
minimum over all three free complex coefficients. Stored independent 70-digit
quadrature values and every matrix entry lie inside the certified intervals.

## Scope clarification: the full contradiction ratio

The certified minimum above excludes only reaching the chosen Q<0.001 budget
in the stated fixed-normalization models. It does **not** exclude every
coefficient-only repair of the complete argument: changing coefficients also
changes the mixed moment in Proposition2.4. That moment must be recomputed,
rather than held at its original lower bound by assumption.

Normalize the nonnegative weighted sums by N=mathfrak(a)P. Let ell=Xi1*/N,
Q be the normalized squared norm of H1+Z conjugate(H2), R the squared norm of
J1, S that of H2, and E that of J1-Z conjugate(J2). The exact identity in(2.17)
and Cauchy's inequality in(2.18)-(2.20) give

    |ell| <= sqrt(Q R) + sqrt(S E).

Thus a repaired contradiction needs estimates violating this full inequality.
When S stays bounded and E tends to zero, the scale-invariant limiting target
is |ell|^2/(Q R)>1, with a strict margin. With the original lower bound5 and
upper bound3000, a fixed limiting Q<25/3000=1/120 would suffice;0.001 is a
stronger chosen budget. The certificate's0.024 lower bound alone is not a
certificate about the ratio after ell changes.

No repaired ratio or admissible modified parameter family is established in
this report. Support, duality, uniform error estimates and the actual-character
identification must all be preserved and rechecked for any proposed family.
The finite-model certificate and all its exact numerical conclusions remain
unchanged by this clarification.

## Replay and provenance

From the repository root:

    sha256sum -c audit/section18_numerical/SHA256SUMS
    python -S audit/section18_numerical/check_replay.py

The replay and containment check pass using only the Python standard library.
A relocated-directory replay also passes. Numerical outputs are byte-for-byte
unchanged from the frozen original; only the two script output paths and
publication documentation were adjusted. Original artifacts are preserved under
[audit provenance](audit/section18_numerical/provenance/README.md).
The [manifest](audit/section18_numerical/integration_manifest.json) records source
hashes, intended repository paths, and file identities. No Lean run or theorem
certification is claimed by this audit publication.
