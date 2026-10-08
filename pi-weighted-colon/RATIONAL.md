# Actual rational origin matrix: all-scale nonzero determinant

This milestone proves the exact factorial row/column scaling bridge for the
actual guarded rational origin entry, and nonzero rational determinant for
every N≥0 and every proved ordering of the original frequency columns.
It does not define a residual polynomial, prove its determinant identity,
or prove any π specialization.

## Entry, guard and exact rational casts

```lean
def rationalOriginEntry (s a c : ℕ) (h : ℚ) : ℚ :=
  if a ≤ c ∧ c ≤ s + a then
    (c.choose a : ℚ) * h ^ (s + a - c) / ((s + a - c).factorial : ℚ)
  else 0

def rationalRowScale (s a : ℕ) : ℚ := (a.factorial : ℚ) * (s.factorial : ℚ)
def rationalColScale (c : ℕ) : ℚ := 1 / (c.factorial : ℚ)
```

The guard is precisely a≤c≤s+a. The denominator and exponent are used only
in that guarded branch; outside it the entry is zero. rational_origin_guard
proves equivalence with the integer entry's a≤c and c-a≤s guard.
rational_origin_exponent proves s+a-c=s-(c-a) under the guard, so truncated
natural subtraction cannot create a spurious power or factorial. The 0^0
boundary remains one.

All factorials cast to Q are proved nonzero, as are each row and column
scale and both finite scale products. The binomial cast theorem gives
binom(c,a)=c!/(a!(c-a)!) and binom(s,c-a)=s!/((c-a)!(s-(c-a))!).
After guard/exponent alignment, these are exact rational identities; field
simplification clears only the proved nonzero factorial denominators.

```lean
theorem rationalOriginEntry_scaled (s a c : ℕ) (h : ℤ) :
    rationalRowScale s a * rationalOriginEntry s a c (h : ℚ) * rationalColScale c =
      (originEntry s a c h : ℚ)
```

The identity holds for every integer node h. In the actual matrices the
original natural-number frequency h is cast through Z and Q exactly.

## Actual matrices and determinant scaling

rationalOriginMatrix uses the unchanged RowIndex N and OriginLabel N,
with the same actual staircase and frequency-length profile as
[ORIGIN.md](ORIGIN.md). It evaluates the displayed rational entry at each
original natural frequency. There is no assumed abstract equivalent matrix.

rationalOriginMatrix_scaled proves the full rectangular matrix equality

```text
diag(row a!s!) * rationalOriginMatrix N * diag(column 1/c!)
  = originalIntegerMatrix N mapped by the exact Z→Q cast.
```

squareRationalOriginMatrix N e makes the actual matrix square with the
supplied proved bijection e : RowIndex N ≃ OriginLabel N. Its scaled matrix
identity and determinant multiplicativity prove

```lean
theorem rationalOriginMatrix_det_scaling (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    (∏ r : RowIndex N, rationalRowScale (rowS r) (rowA r)) *
      (squareRationalOriginMatrix N e).det *
        (∏ c : RowIndex N, rationalColScale (e c).val.2) =
          ((squareOriginalIntegerMatrix N e).det : ℚ)

theorem rationalOriginMatrix_det_ne_zero (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    (squareRationalOriginMatrix N e).det ≠ 0

theorem canonicalRationalOriginMatrix_det_ne_zero (N : ℕ) :
    (canonicalRationalOriginMatrix N).det ≠ 0
```

The original integer determinant is nonzero by the unchanged all-scale
integer theorem. Its exact cast to Q remains nonzero. The scaled rational
determinant is therefore nonzero, so its determinant factor is nonzero.
The row/column scale products have independently proved nonzero declarations.
There are no extra degree, divisibility, determinant or factorial hypotheses.

The theorem permits every proved original-column ordering. The canonical
matrix uses the existing equal-cardinality choice matrixIndexEquiv followed
by the explicit originalIndexEquiv; no lexicographic ordering is silently
claimed. All original row/column labels and counts are retained, including N=0.

## Explicit numerical and determinant regressions

RationalRegression.lean checks E(3,0,0,3)=9/2, E(3,1,2,3)=9,
E(1,1,2,1)=2, E(0,1,1,0)=1 and the guarded zeros, including c>s+a at
(0,0,1,0), where unguarded truncated subtraction would give a false nonzero
entry. It checks the actual factorial-scaled entry 6·9·(1/2)=27.

The N=0 determinant regression enumerates all actual rows in the order
(s,a)=(0,0),(1,0),(0,1),(1,1), and all original columns
(h,c)=(0,0),(1,0),(1,1),(1,2). Both enumerations have kernel-checked
bijections. The actual matrix is proved to have the entries

```text
1 1 0 0
0 1 1 0
0 0 1 0
0 0 1 2
```

Its determinant is proved to equal 2 by column expansion. Simultaneous
row/column reindexing then proves

```lean
theorem actual_rational_scale_zero_det :
    (squareRationalOriginMatrix 0 rationalScaleZeroOrdering).det = 2
```

This is the actual origin matrix with a proved ordering, rather than a toy
matrix. Negative checks reject the entry value 27 in place of 9/2 and the
actual rational determinant value 1 in place of 2. Regression proofs use
ordinary kernel-checked arithmetic, not native_decide.

## Cumulative verification and preserved pins

The cumulative replay compiles 33 positive modules and checks fifteen expected
failures (48 compilation checks), auditing exactly 388 declarations. All
previous 43 Lean sources and all toolchain/dependency pins are unchanged.
The added direct imports Choose.Cast, FieldSimp and FinCases are cached and
source-attested at the same pinned mathlib revision. Only propext,
Classical.choice and Quot.sound are permitted by the full declaration audit.
The replay rejects sorry, admit, native_decide, custom axioms and unsafe proof
constructs, and treats warnings as errors. Source hashes, exact compiler
commands, type/definition/axiom output and logs are preserved under verification/.
Use the README replay command with --out /tmp/pi-rational-replay.

No full containing-repository build is claimed. The old Lean 4.34.1 checkpoints
are preserved but were not rerun. This stage ends at the actual rational
origin matrix. A residual polynomial, its identity and π specialization,
integer collision-quotient, archimedean estimate, arbitrary arithmetic weights
and π badly-approximability remain outside the formalized scope.

The subsequent [Hermite stage](HERMITE.md) constructs the actual coefficient
matrix over Q[x] from monic remainders and proves its evaluation at x=0 is
this matrix, hence its determinant polynomial is nonzero for every N.
