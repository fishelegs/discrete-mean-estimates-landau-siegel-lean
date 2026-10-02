# Independent Section 18 quadratic form audit

## Certified result and scope

This frozen package audits twelve explicitly specified finite Hermitian models
associated with Section 18 of Yitang Zhang's arXiv:2211.02515v1. For every model,
at the paper's coefficients (2.26), Q = c1 + c2 + 2 Re(c3) > 0.05. With the
coefficient of H11 fixed to 1, its global minimum over all three remaining
complex coefficients iota2, iota3, iota4 is > 0.024. The target is Q < 0.001.

For the source-derived comparison branch `.5:exact:upstream`:

- c1 = 7.05010466979205041964393903214…
- c2 = 6.98709229778193001759470409477…
- c3 = −6.99092771402436271881273463731… − 0.02031059081994386174945506766… i
- Q is in [0.0553415395252549996131, 0.0553415395252549996132]
- Global constrained minimum is in
  [0.0249294244390953127716, 0.0249294244390953127717]

Changing only these three complex coefficients therefore cannot achieve the
target within these twelve fixed models and this normalization. This does not
rule out other analytic corrections, other parameters, other mollifiers,
different constructions, or other proofs, and it does not disprove the main
theorem. No character satisfying (A) is constructed; no vacuity argument is used.

## Model definitions and outstanding source reconstruction

Every branch uses the κ2 expression obtained by expanding the previously defined
B and H2 in place of Section 17's undefined κ4. The branch key is
`denominator:high:tail`:

- denominator `.504`: literal (9.5), (9.6); `.5`: the limit obtained from the
  preceding log(P2)log(P3) denominator and (2.21)
- high `printed`: 2e2*; `exact`: the specified symbolic high-residue model A+conj(B)
- tail `printed`: displayed Lemma 15.1 e1j''; `collapsed`: Section 18's asserted
  cancellation treated as exact for comparison; `upstream`: the symbolic value
  e1j'' = −iπj b* obtained from Appendix B's terminal residue expression

The names `exact` and `upstream` label formulas, not certified arithmetic
asymptotics. The collapsed branches are comparisons, not assertions that the
paper cancellation is exact. Equality of these matrices to actual normalized
character means is not certified. Analytic mean-value, contour, error,
uniformity, and character-theoretic bridges remain outside this package.

In particular, Lemma 15.1 coefficient-basis reconstruction remains pending:
(15.1) displays B in the χψ basis, while the convolution before (15.5) is in the
ψ basis. The interpretation and propagation of b, and the tail endpoints, need
a separate audit. This package does not publish a confirmed-error finding about
that pending reconstruction and cannot claim a repaired actual Lemma 15.1.

All three +0.004 shifts in each Section 8 cross-term display (8.21), (8.22) are
present in the official source and retained. No missing-shift allegation is made.
The printed-model cancellation fails the 10^-5 budget, while the Appendix B
terminal-expression model meets that local budget; this is a model comparison,
not an arithmetic repair theorem. See DERIVATION.md for formulas and locators.

## Portable replay

From the repository root (or the publication staging root):

    sha256sum -c audit/section18_numerical/SHA256SUMS
    python -S audit/section18_numerical/check_replay.py

The second command reruns the exact rational interval certificate, checks all
twelve branch bounds and positive interval LDL pivots, and checks every stored
independent matrix entry and reported scalar for interval containment. It uses
only Python's standard library; `-S` disables site-package initialization.
It writes deterministic `certified.json` and `certified.txt` alongside the scripts.
A successful replay prints:

    PASS: exact certificate replay and independent 70-digit results agree in all 12 branches

To run the certifier alone:

    python -S audit/section18_numerical/certify_independent.py

For an optional fresh, non-certifying 70-digit quadrature and eigensystem check:

    python audit/section18_numerical/explore_independent.py

The optional check requires mpmath and writes `exploratory.json` alongside its
script. Stored independent results are included, so mpmath is unnecessary for
the certified replay and containment check. Both output paths are based on
Path(__file__).with_name and do not depend on the current working directory.
The global minimum is certified by interval LDL and completion of squares, not
by floating-point eigenvalues. The scripts do not invoke Lean, Lake, caches,
network, or GitHub. Python integer arithmetic, the interval implementation, and
the documented symbolic reductions form the trust boundary.

## Files and provenance

- DERIVATION.md: source-to-model formulas, conjugations, and scope
- CERTIFICATE_METHOD.md: exact arithmetic, Taylor enclosures, and interval LDL
- source-excerpts.txt: original numbered frozen TeX excerpts
- source-caveat-excerpts.txt: supplementary coefficient-basis and shift locators
- certify_independent.py / certified.json / certified.txt: rational interval certificate
- explore_independent.py / exploratory.json / exploratory.txt: independent numeric check
- check_replay.py: exact replay plus stored independent-output containment
- validation.json: publication verification results
- integration_manifest.json: source hashes, original identities, portable path map
- SHA256SUMS: current publication hashes, using repository-root-relative paths
- provenance/original/: byte-for-byte original package, including its historical
  nonportable paths and superseded scope wording; do not execute these copies

Source: [arXiv:2211.02515v1](https://arxiv.org/abs/2211.02515v1),
[official PDF](https://arxiv.org/pdf/2211.02515v1). The supplied TeX and PDF hashes
were verified against the original manifest. This publication is a numerical
model audit, not a Lean kernel certificate of the integrals or analytic lemmas.
