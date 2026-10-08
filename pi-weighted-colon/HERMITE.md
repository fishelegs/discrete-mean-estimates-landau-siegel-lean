# Actual Hermite coefficient determinant over Q[x]

This stage proves that the determinant of the **actual Hermite coefficient
matrix** is a nonzero polynomial in x, for every natural N. The entries are
constructed from monic polynomial remainders, not by lifting the origin matrix
as a constant polynomial. The specialization at x=0 is proved equal to the
rational origin matrix from [RATIONAL.md](RATIONAL.md).

## Definitions and proved bridge

`HermiteParameter = Polynomial ℚ` uses the inner variable x, and
`HermiteBivariate = Polynomial HermiteParameter` uses the outer variable z.
The definition `hermiteModulus n` is z^n(z-x)^n and is proved monic, including
n=0. The coefficient

```text
r(n,d,a;x) = coeff_z^a (z^d %ₘ [z^n(z-x)^n])
```

is exactly `hermiteRemainderCoefficient n d a`, using Lean's monic remainder
operation. No high-degree closed binomial remainder formula is assumed or
claimed to be formalized.

The row multiplicity is defined as

```text
n_s = N+1                         if s<2
n_s = N - floor((s-2)/4)          otherwise.
```

`hermite_row_profile_iff` proves that the actual original staircase condition
`a≤2N+1, s≤4(N-floor(a/2))+1` is equivalent to
`s≤4N+1, a<2n_s`. Thus all existing original rows satisfy the required
remainder-coefficient bound, and their multiplicities are positive.

The actual polynomial entry is

```text
H(s,a;h,c;x) = sum_{ell=0}^{min(s,c)}
  binom(c,ell) h^(s-ell)/(s-ell)! * r(n_s,c-ell,a;x).
```

Constants in this expression are embedded into Q[x]. Columns are the exact
original `(h,c)` labels and frequency profile already proved in
[NEWTON.md](NEWTON.md). The rectangular matrix is
`hermiteCoefficientMatrix N`; `squareHermiteCoefficientMatrix N e` reindexes
columns using any proved equivalence `e : RowIndex N ≃ OriginLabel N`.
No arbitrary or unproved indexing function is supplied.

The coefficient proof maps monic division along evaluation x↦0. The modulus
becomes z^(2n), whose monomial remainder is z^d for d<2n and zero otherwise.
For a<2n, the evaluated coefficient is therefore one exactly when a=d.
The finite coefficient sum then has at most one nonzero summand, yielding
exactly the previously defined guarded rational entry.

The central Lean declarations are:

```lean
theorem hermiteCoefficientMatrix_eval_zero (N : ℕ) :
  (hermiteCoefficientMatrix N).map (evalRingHom (0 : ℚ)) =
    rationalOriginMatrix N

theorem hermiteCoefficientMatrix_det_eval_zero
    (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
  ((squareHermiteCoefficientMatrix N e).det).eval 0 =
    (squareRationalOriginMatrix N e).det

theorem hermiteCoefficientMatrix_det_ne_zero
    (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
  (squareHermiteCoefficientMatrix N e).det ≠ 0
```

The final theorem follows from the already proved nonzero rational origin
determinant. A canonical choice of a proved equivalence is also supplied;
no lexicographic ordering is claimed.

## Regressions and verification

`HermiteRegression.lean` proves the exact division of z² by z(z-x), with
quotient one and remainder xz. Consequently the actual entry
`hermiteCoefficientEntry 1 1 1 2 1` is **x+2**, its x coefficient is one,
and its evaluations at x=0 and x=1 are two and three. The entry is explicitly
identified as an original row and original column of `hermiteCoefficientMatrix 0`.
The actual square matrix at N=0 has determinant evaluation two at x=0 and
nonzero determinant polynomial. The existing rational N=0 determinant
computation is reused with its proved explicit ordering.

Two negative checks reject a zero x coefficient and an evaluation of one at
x=0. The cumulative replay compiles 36 positive modules and requires 17
expected failures. It audits all 420 named declarations, including definitions
and regressions. Only `propext`, `Classical.choice`, and `Quot.sound` are
allowed. It checks source hashes and dependency pins and treats warnings as
errors; no proof source uses `sorry`, `admit`, `native_decide`, custom axioms,
or unsafe declarations.

The checked local command, run from the repository root, is:

```sh
python3 pi-weighted-colon/scripts/replay.py \
  --lean /Users/keyishen/.elan/toolchains/leanprover--lean4---v4.30.0/bin/lean \
  --existing-mathlib-project /Users/keyishen/Documents/Codex/2026-10-04/task/mc6-proof \
  --out /tmp/pi-hermite-replay
```

The compiler is Lean 4.30.0 and mathlib is pinned to
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. Full commands, exit codes,
source/cache/log hashes and axiom sets are in
`verification/replay-receipt.json`. The checkpoint's dedicated Linux CI runs
the same source verifier. This does not claim a containing-repository build
or rerun of the older Lean 4.34.1 π checkpoints.

## Remaining application bridges

The derivative-jet determinant factor x^ν, the Schur-compressed residual
identity, the integer collision quotient, and the π specialization remain
separate and unformalized. This stage proves only the specified actual
Hermite coefficient determinant nonvanishing. It gives no archimedean lower
bound, no arbitrary-weight theorem, and no badly-approximability theorem for π.
