# Prescribed-point gap for an anchored bounded polynomial family

This additive checkpoint formalizes one narrow logical gap from the THIRD153
normal-family trial. It does not depend on earlier project modules or alter them.

For every natural number n (including zero), define the actual complex polynomial

    P_n(X) = -1 + X + (4/9 - 1/(n+1)) X²,
    p_n(z) = P_n.eval(z),     lambda = 3/4.

All divisions in this formula are field divisions; n+1 is strictly positive.
The n+1 indexing is the reindexing of the report's positive-integer family.

## Formal result

The 15 theorem/lemma declarations in `src/NormalFamilyPointwiseGap.lean` prove:

- P_n has constant coefficient -1 and every nonconstant coefficient has norm at
  most 1, with the bound quantified over all natural coefficient indices
- p_n is analytic on a neighborhood of every point of the complex plane
- p_n(0) = -1, and for every fixed R >= 0 and every |z| <= R,
  |p_n(z)| <= 1 + R + R², uniformly in n
- lambda is real and strictly inside the unit disk
- p_n(lambda) = -9/[16(n+1)] as an equality in C
- p_n(lambda) is nonzero for every n, and these complex values tend to zero
- for every c > 0 some n has |p_n(lambda)| < c; hence no common positive
  pointwise lower bound exists

The function is defined by evaluating `Polynomial C`, not by substituting a
standalone real sequence for the polynomial family. The formal holomorphic and
fixed-disk statements certify the analytic premises relevant to this example.

## Exact boundary

Anchoring, uniform fixed-disk boundedness, and individual nonvanishing at a
prescribed point do not imply a positive uniform bound there. This is a
counterexample to that implication inside the literal coefficient-bounded source
class. It is not identified with any pi determinant family. It is not a
bad-approximability theorem, an endpoint signed-gain estimate, a selected-minor
rule, or a refutation of the THIRD153 interval-supremum lemma. A large value
somewhere in an interval is compatible with small nonzero values at its prescribed
endpoint. No claim is made about all possible determinant-selection methods.

No normal-family compactness theorem, interval-supremum bound, or locally uniform
limit theorem is newly formalized here; the explicit global analytic and uniform
fixed-disk hypotheses, and the pointwise convergence, are formalized directly.

## Audit and regression

`NormalFamilyPointwiseGapAudit.lean` prints all four definitions, explicit theorem
types, and the axioms of all 15 declarations. Only `propext`, `Classical.choice`,
and `Quot.sound` occur. No extra hypotheses assert the desired conclusion.

`NormalFamilyPointwiseGapRegression.lean` checks the first coefficients, the
actual first polynomial, exact target values, a concrete small value, the entire
family's coefficient/analytic/disk conditions, convergence, and the final
negated bound. `ExpectedFailureUniformPointwiseBound.lean` deliberately tries
the false positive-uniform-bound conclusion. It must fail with exactly one
unsolved `False` goal and produce no olean. It is excluded from successful builds.

## Replay

Use an already installed Lean 4.34.1 and an existing project with the exact
package pins in `verification/normal-family-gap-dependency-pins.json`:

    python3 scripts/replay-normal-family-gap.py \
      --lean /path/to/lean-4.34.1/bin/lean \
      --existing-mathlib-project /path/to/pinned-project \
      --out /path/to/fresh-private-output

Coordinate exclusive access to the compiler before replay. The script performs
four sequential invocations with `-j1 -M4096`, disables implicit variables, and
treats warnings as errors. It requires a fresh private output directory outside
the source, dependency, and toolchain trees. It neither downloads nor installs
anything, invokes no Lake hook, and builds no dependencies.

When replayed in the combined repository tree, the script also verifies that the
unchanged existing `dependency-pins.json` agrees with this stage’s pinned copy.
The script checks the exact package set/revisions, toolchain version, hashes of
this stage's sources and replay files, and source hashes of direct mathlib
imports. It records current compiler and direct-import olean hashes in its
receipt. The supplied attestation records the exact provider used for the
published verification. Trusted precompiled dependencies are not independently
rebuilt, and the complete transitive binary cache is not re-audited. A matching
version or manifest is not represented as a full dependency build certificate.

The archived compiled-source receipt records the successful clean portable replay.
The source-hash manifest binds all four Lean files, this README, the portable
script, dependency pins, dependency attestation, and analysis-input hashes.
The input reports are contextual provenance, not Lean dependencies. The raw
printed-type/axiom log and exact expected-failure log are archived separately.

This package is additive to PR head
`319c792c442b55730c99d8dd59ed384941a65d36`; it makes no change to that baseline's
42 files. Publication and independent review are separate from this build.
