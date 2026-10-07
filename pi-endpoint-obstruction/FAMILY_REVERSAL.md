# Third checkpoint: reversal for one explicit polynomial family

This source-only additive checkpoint proves an eventual **unfavorable** magnitude
comparison for the explicitly defined polynomial family

    Q_N(z) = (-1)^N N^2 z^nu_N [289 z^2 + 764(4N^2 - 1)]
    nu_N = 2(N+1)(2(N+1)^2 + 1)/3.

`N` is a natural number. The exponent is defined using natural division, and
`three_mul_exponent` proves that multiplying it by 3 recovers the numerator for
every N. There is no truncation ambiguity. The residual coefficient's subtraction
is in the reals. Both a complex polynomial object and its evaluated function are
defined, and `familyPolynomial_eval` proves they agree.

## Kernel-checked conclusions

For every N >= 3:

    norm(Q_N(2*pi*i)) < norm(Q_N((44/7)*i))
    log(norm(Q_N(2*pi*i)) / norm(Q_N((44/7)*i))) < 0.

The actual constant `Real.pi` is used. `actual_period_bounds` uses mathlib's
certified `Real.pi_lt_d4`, together with positivity, to prove
`0 < 2*pi < 44/7 <= 7`. Both compared norms are proved positive. The logarithmic
claim therefore does not rely on Lean's totalized logarithm or division at zero.
`eventually_signedGain_neg` states the resulting atTop tail theorem, with explicit
cutoff 3; `not_positive_signedGain` excludes positive gain at every N >= 3.

The reusable comparison `radial_strict` proves that for A >= 26740 and any natural
n >= 4, `t^n (A - 289 t^2)` is strictly increasing on `(0,7]`. Its proof is purely
algebraic: first compare the exponent-four expressions by factorization and exact
bounds, then multiply by the monotone positive factor `t^(n-4)`. No floating-point
calculation or unverified numerical pi approximation enters the proof.

## Verification and boundary tests

- Fourteen declarations, including every supporting lemma, receive exact type
  and axiom audits; the five definitions are printed too
- Only `propext`, `Classical.choice`, and `Quot.sound` appear in those audits
- No `sorry`, custom axioms, `admit`, `unsafe`, or `native_decide` are used
- Positive regressions check nu_0=2, nu_1=12, nu_2=38, nu_3=88, nu_4=170,
  the coefficients at N=2 and N=3, the exact N=2 polynomial, the N=3 norm comparison,
  and logarithmic negativity at N=3 and N=4
- The intentional `ExpectedFailureFamilyAtTwo` attempts to apply the N>=3 theorem
  at N=2. It fails on the impossible precondition with `False`, and creates no
  output artifact. This tests the excluded precondition; it does not certify the
  numerical value or sign of the N=2 gain
- Warnings are errors. Every compiler invocation uses `-j1 -M4096`

## Scope boundary

This is a theorem about **one displayed polynomial family**. It does not formalize:

- The identification with the growing full-packet matrix determinant
- The source's sufficient separated-weight and eventual-H hypotheses
- The optional finite N=2 gain interval or residual-root location
- The normalized asymptotic limit of the gain
- Any universal statement about admissible or rank-selected minors
- Bad approximability of pi, or a disproof of bad approximability

The family formula motivating this checkpoint was independently reviewed in exact
mathematical and rational-computation research. That identification remains a
separate, non-Lean result. The formal statement does not assume it as an axiom.

## Portable replay, using an existing cache

Add these files to the existing `pi-endpoint-obstruction` directory, preserving all
31 earlier files. The existing `dependency-pins.json` and `lean-toolchain` remain
unchanged. With an already populated project matching those pins:

    python3 scripts/replay-family-reversal.py \
      --lean /path/to/lean-4.34.1/bin/lean \
      --existing-mathlib-project /path/to/pinned/project \
      --out /path/to/fresh/private-output

Coordinate exclusive compiler access before replaying. Output must be outside the
source and dependency trees. The script checks source hashes, Lean's version, all
package revisions, the direct-import source hashes, cached imports, expected test
results, and all fourteen axiom audits. It writes only to the requested output.
It invokes no Lake hooks, installs, network requests, or dependency builds.

The trust boundary is the pre-existing Lean executable and precompiled dependency
cache. Recorded executable, manifest, source, and direct-cache hashes attest the
original run; this checkpoint does not independently rebuild or verify all
transitive mathlib dependencies. `verification/family-reversal-*` contains the
source receipts, exact type/axiom output, pin/cache attestation, and expected-failure
log. Compiled binaries are intentionally excluded from publication.
