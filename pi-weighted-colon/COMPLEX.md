# Pointwise complex specialization of the actual Hermite matrix

This stage proves evaluation and determinant compatibility for the actual
Hermite coefficient matrix, and nonvanishing at **every complex number
transcendental over Q**, for all natural N and every proved original-column
ordering. It also proves that, for a real r, 2*r*i is transcendental over Q
if and only if r is. The requested unconditional specialization at 2*pi*i
is **blocked by a precise theorem gap in the pinned library** and is not
asserted by this checkpoint.

## Actual complex matrix and determinant identity

The polynomial matrix is exactly the monic-remainder construction from
[HERMITE.md](HERMITE.md). No entries, original frequency labels or row profile
are changed. `hermiteComplexEval x` is the ring homomorphism underlying
`Polynomial.aeval x : Q[x] →ₐ[Q] C`, using the rational algebra map into C.
`complexHermiteCoefficientMatrix N x` maps every actual polynomial entry
through that homomorphism. Rows remain `RowIndex N` and columns remain
`OriginLabel N`. `squareComplexHermiteCoefficientMatrix N e x` uses the same
proved equivalence `e : RowIndex N ≃ OriginLabel N` as the polynomial matrix.

The proved determinant map identity is:

```lean
theorem complexHermiteCoefficientMatrix_det_aeval (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) (x : ℂ) :
  aeval x ((squareHermiteCoefficientMatrix N e).det) =
    (squareComplexHermiteCoefficientMatrix N e x).det
```

The general pointwise theorem, with its necessary explicit transcendence
hypothesis, is:

```lean
theorem complexHermiteCoefficientMatrix_det_ne_zero (N : ℕ)
    (e : RowIndex N ≃ OriginLabel N) (x : ℂ)
    (hx : Transcendental ℚ x) :
  (squareComplexHermiteCoefficientMatrix N e x).det ≠ 0
```

`hermite_determinant_aeval_ne_zero` gives the evaluated-polynomial form.
Both use the already proved polynomial determinant nonvanishing and
`transcendental_iff`: a polynomial over Q vanishing at a transcendental point
must be zero. A canonical proved indexing equivalence is also provided.

## Proved scalar transport and exact pi gap

`complex_I_isAlgebraic` proves i algebraic over Q with the explicit polynomial
X²+1. `complex_transcendental_mul_iff` proves multiplication by a nonzero
algebraic complex number preserves and reflects transcendence; its proof uses
the algebraic inverse to recover the original number. Algebraicity is also
transported and reflected through the injective real-to-complex algebra map.
This proves the unconditional equivalence:

```lean
theorem imaginaryRealParameter_transcendental_iff (r : ℝ) :
  Transcendental ℚ (imaginaryRealParameter r) ↔ Transcendental ℚ r
```

Here `imaginaryRealParameter r = 2*(r : C)*Complex.I`. The real-parameter
matrix theorem `complexHermiteCoefficientMatrix_det_ne_zero_imaginaryReal`
therefore follows under the explicitly stated hypothesis `Transcendental Q r`.
This is a general conditional theorem, not a claim about a known pi proof.

`piHermiteParameter` is exactly 2*pi*i. The only new pi-related transcendence
statement is an **equivalence**, which supplies neither side:

```lean
theorem piHermiteParameter_transcendental_iff :
  Transcendental ℚ piHermiteParameter ↔ Transcendental ℚ Real.pi
```

There is no unconditional pi nonvanishing theorem or an assumed pi axiom.
The missing established theorem is `Transcendental ℚ Real.pi` in mathlib
revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`:

- `Mathlib/Analysis/Real/Pi/Irrational.lean` proves `Real.irrational_pi`,
  which is weaker than transcendence and cannot fill this input.
- The Lindemann directory contains `AnalyticalPart.lean`, with analytic
  identities and estimates, but no completed Lindemann-Weierstrass theorem
  or pi-transcendence corollary.
- A source scan of all 38 files containing `Transcendental`, `transcendental`,
  `Lindemann` or `lindemann` found no occurrence of `Real.pi`, word `pi`, or π.
  `verification/pi-transcendence-gap.json` records the query and all candidate
  source hashes, plus the irrationality and Lindemann source hashes. Replay
  checks these hashes against the actual pinned source checkout.
- An expected-failure compiler diagnostic rejects the candidate name
  `Real.transcendental_pi` as an unknown constant. This name check alone is
  not treated as evidence that no equivalent theorem exists; the source scan
  and incomplete Lindemann module provide the broader evidence.

Completing the requested pi specialization thus requires a separately verified
pi-transcendence theorem. This stage preserves the toolchain and dependency
pins and does not introduce an unproved replacement.

## Regressions, audit and reproduction

Positive regressions evaluate the actual nonconstant entry at x=i, obtaining
i+2, and identify it as a genuine original row and column at N=0. The actual
N=0 complex matrix at x=0 has determinant two. Other regressions check the
parameter 2*i, prove that 4*i is not transcendental, and check the exact
2*pi*i definition. Expected failures reject an incorrect i+3 entry,
transcendence of the algebraic parameter 4*i, and the unavailable pi theorem.

The cumulative replay compiles 39 positive modules and requires 20 expected
failures, with exact source/log hashes. It audits all 443 named declarations;
only `propext`, `Classical.choice`, and `Quot.sound` are permitted. Proof sources
contain no `sorry`, `admit`, `native_decide`, custom axioms or unsafe declarations,
and warnings are treated as errors.

From the repository root on KEYISHEN-MC6:

```sh
python3 pi-weighted-colon/scripts/replay.py \
  --lean /Users/keyishen/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean \
  --existing-mathlib-project /Users/keyishen/Documents/Codex/2026-10-04/task/mc6-proof \
  --out /tmp/pi-complex-replay
```

The exact compiler commands, exit codes, dependency/source/cache/log hashes,
axiom sets and pi-gap record are in `verification/replay-receipt.json`.
The dedicated Linux CI runs this same checkpoint verifier. No containing-root
build or rerun of older Lean 4.34.1 pi checkpoints is claimed.

## Limits

Pointwise nonvanishing supplies **no uniform analytic lower bound** and no
badly-approximable conclusion. The derivative-jet x^nu determinant factor,
Schur-compressed residual identity and the unconditional 2*pi*i specialization
remain unformalized. These statements concern the actual Hermite coefficient
matrix only, with its original row and column labels, for all N.
