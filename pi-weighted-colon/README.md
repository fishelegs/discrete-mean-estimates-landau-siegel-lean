# Weighted colon lemma for the π all-scale algebraic argument

This checkpoint proves the weighted colon milestone for the actual
endpoint-generated ideals. It does **not** prove the full staircase intersection
theorem, a determinant parity statement, an analytic lower bound, or that π is
badly approximable.

## Exact proved statement

Work in `Plane = Polynomial (Polynomial (ZMod 2))`. The outer variable is `t`
(or `x` after a coordinate change) and the inner variable is `y`.
The two values of `Bool` encode precisely the endpoints ε=0 and ε=1.

```text
z = t + y
d_false = 1, d_true = 3
Q = (t² + t + y)² = t⁴ + t² + y²
J_ε = (z − ε, y^(d_ε))
K_ε = ((z − ε)², y^(d_ε))
I_N = J_0 K_0^N ∩ J_1 K_1^N
```

The main declaration is `PiWeightedColon.intersection_colon`:

```lean
theorem intersection_colon (N : ℕ) :
  (dataIntersection (N + 1)).colon {globalQ} = dataIntersection N
```

`intersection_colon_pred` gives the requested `(I_N : Q) = I_(N−1)` with the
explicit hypothesis `1 ≤ N`. The colon is by the singleton `{Q}`, so its elements
are exactly the polynomials `f` for which `f*Q` belongs to the data ideal.

The generators are defined explicitly, and their connection to the weighted
coefficient model is proved, rather than supplied as a hypothesis.

## Proof components

- `src/WeightedColon.lean`: defines `weight d k c = k + 2*(c/d)`, the predicate
  that all coefficients below a threshold vanish, and the actual local
  multiplication by `x⁴+x²+y⁴`. For `d=1,3`, multiplication raises that threshold
  by exactly two. The proof recovers input coefficients by strong induction on
  weight and then on a bound minus their x exponent. At output `(k+2,c)`, the x⁴
  contribution comes from a strictly lower weight; the y⁴ contribution has a
  lower weight or the same weight and larger x exponent. This proves the
  non-cancellation step over any commutative ring, even with zero divisors.
- `src/DataIdealPresentation.lean`: proves that the coefficient-vanishing
  predicate defines an ideal and that `(x,y^d)*(x²,y^d)^N` is exactly the ideal
  of coefficients of weight at least `2N+1`, for every positive `d`. This uses
  the polynomial's actual finite coefficient expansion and a generator
  factorization of each eligible monomial. It then proves the local colon
  identity for `d=1,3`.
- `src/EndpointColon.lean`: implements the invertible change `t ↦ x+y+ε`,
  proves the transformed Q is `x⁴+x²+y⁴`, transports the explicit endpoint
  generators, and proves the intersection colon identity.

## Scope and verification

The positive regressions check an input with two lowest-weight terms,
`x²+y⁴` at `d=3`. Its mixed output term really cancels in F₂, while its vanishing
threshold still increases by exactly two, not three. A further regression proves
that the colon ideal at scale zero is not the original ideal. The two negative
tests must fail on the false hypotheses `1 ≤ 0` and `5=1 ∨ 5=3`.

The reproducible check compiles three proof modules, the positive regressions,
the type/definition/axiom audit, and the two expected failures. All 58 new
declarations, including definitions and regression theorems, are audited.
Only the standard axioms `propext`, `Classical.choice`, and `Quot.sound` are
permitted. The proof sources contain no `sorry`, `admit`, `native_decide`,
custom axiom or unsafe declaration. Warnings are treated as errors.

The full `V_N ∩ I_N = {0}` theorem has not been formalized here: the monic
division, remainder restrictions, degree bounds and final induction remain.
The binary matrix equivalence and the integer determinant/residual-polynomial
bridge also remain unformalized. None of these algebraic statements alone gives
a uniform archimedean estimate or proves the π badly-approximable statement.

## Pins and replay

This directory is an additive, source-only checkpoint based on PR #4 head
`d45ce78882dfc9cee8fb8ea78d2aa75d191ee31d`. It preserves all earlier files and
dependency pins. It is deliberately separate from the root `ZhangLS` Lake
library and from `pi-endpoint-obstruction/`.

- Lean: `leanprover/lean4:v4.30.0`
- mathlib: `c5ea00351c28e24afc9f0f84379aa41082b1188f`
- All package revisions: `dependency-pins.json`
- Direct dependency source/cache hashes: `verification/dependency-attestation.json`
- Exact checkpoint source hashes: `verification/source-hashes.json`
- Compiler commands, exit codes, hashes, and full axiom sets:
  `verification/replay-receipt.json`

From the repository root, on KEYISHEN-MC6 the checked command is:

```sh
python3 pi-weighted-colon/scripts/replay.py \
  --lean /Users/keyishen/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean \
  --existing-mathlib-project /Users/keyishen/Documents/Codex/2026-10-04/task/mc6-proof \
  --out /tmp/pi-weighted-colon-replay
```

For another machine, substitute the compiler and existing project paths with
matching pins. The script checks actual dependency Git heads and cleanliness,
not just manifest labels. It runs Lean serially with `-j1 -M4096`,
`-DautoImplicit=false` and `-DwarningAsError=true`. It never invokes Lake, hooks,
downloads or dependency builds. The existing compiler and dependency cache
remain trusted inputs; replay records their hashes and does not rebuild them.
Binary Lean outputs remain outside the source tree and are not committed.

The older π checkpoints use Lean 4.34.1 and another mathlib revision. That
toolchain is not installed on this computer, so their old regression suites
were **not rerun**. They are preserved byte-for-byte; the verification receipt
covers the new 4.30.0 checkpoint only. No full containing-repository build is
claimed.
