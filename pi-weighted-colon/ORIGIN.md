# Original integer evaluation determinant: all N

The global integer bridge is Lean-proved. The later [RATIONAL.md](RATIONAL.md)
milestone supplies exact factorial scaling and proves nonvanishing of the actual
rational origin determinant using these unchanged integer Lean sources. The actual original integer evaluation
matrix for the fixed weight-2 frequency profile has nonzero determinant for
every N≥0 and every proved original-column reindexing. The proof uses an
explicit integer matrix multiplication and determinant factorization.
It never cancels an even factor in F₂.

## Original rows, columns and entries

The unchanged RowIndex and rowLabelEquiv identify the rows with (s,a) satisfying
0≤a≤2N+1 and 0≤s≤4(N-floor(a/2))+1. Both inequalities start at zero because
these coordinates are natural numbers.

The unchanged OriginLabel consists precisely of (h,c) with 0≤h≤4N+1 and
0≤c<L_h, where n_0=N+1, n_j=N-floor((j-1)/2) for 1≤j≤2N, L_(2j)=n_j and
L_(2j+1)=3n_j. The proved originalIndexEquiv transports the existing binary
column indices to these labels by (epsilon,c,k) ↦ (2k+epsilon,c).
The original labels have cardinality 4(N+1)², including N=0.

The originalIntegerMatrix definition retains these original labels. Its entry is
binom(s,c-a) h^(s-(c-a)) if a≤c and c-a≤s, and zero otherwise. Under the guard
the exponent equals the requested nonnegative integer s-c+a; 0^0=1.
No frequency/profile equivalence is supplied as an unproved hypothesis.

## The explicit global integer multiplication

IntegerOriginNonvanishing.lean defines the square factor U on ColIndex N:

```text
U[i,j] = product_{ell<k_i} (node(epsilon_i,k_j)-node(epsilon_i,ell))
         if epsilon_i=epsilon_j and c_i=c_j; otherwise zero.
node(epsilon,k)=2k+epsilon in Z.
```

The entries D of integerNewtonMatrix are the integral synthetic Newton
coefficients from the unchanged [NEWTON.md](NEWTON.md) helpers. Their exact
reduction modulo two is the concrete invertible binary matrix, so det(D) has
nonzero reduction modulo two and is nonzero over Z.

```lean
theorem originalIntegerMatrix_factorization (N : ℕ) :
    (originalIntegerMatrix N).submatrix id (originalIndexEquiv N) =
      integerNewtonMatrix N * integerEvaluationFactor N
```

This equality is for the actual finite matrices. The proof injects each prefix
node into the original finite column index set via columnPrefix. It proves
all summands outside that image are zero, then transports the exact integer
Newton expansion using a finite-sum image identity. This avoids an assumed
abstract factorization or an unproved basis correspondence.

## Triangularity and nonzero factor determinant

integerEvaluationFactor_triangular proves U is block triangular with block
index colK, the difference order. Within each fixed k, the diagonal block is
an actual diagonal matrix: matching epsilon and c together with the fixed
k forces identical columns, by the proved col_ext coordinate injectivity.
Every diagonal entry is product_{ell<k}(node(epsilon,k)-node(epsilon,ell)),
which is nonzero over Z by the proved distinctness of these integer nodes.
The k=0 product is one, and empty fiber blocks also have determinant one.
The library's block-triangular determinant formula therefore proves

```lean
theorem integerEvaluationFactor_det_ne_zero (N : ℕ) :
    (integerEvaluationFactor N).det ≠ 0
```

The formal proof uses the finite image of colK; it does not need a linear order
on the original label type or a closed factorial formula for the product.

## Exact ordering-dependent and final statements

```lean
def squareOriginalIntegerMatrix (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    Matrix (RowIndex N) (RowIndex N) ℤ :=
  (originalIntegerMatrix N).submatrix id e

theorem originalIntegerMatrix_det_factorization (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    (squareOriginalIntegerMatrix N (e.trans (originalIndexEquiv N))).det =
      (squareIntegerNewtonMatrix N e).det * (integerEvaluationFactor N).det

theorem originalIntegerMatrix_det_ne_zero (N : ℕ) (e : RowIndex N ≃ OriginLabel N) :
    (squareOriginalIntegerMatrix N e).det ≠ 0

theorem canonicalOriginalIntegerMatrix_det_ne_zero (N : ℕ) :
    (canonicalOriginalIntegerMatrix N).det ≠ 0
```

The factorization transports the integer identity through the supplied
bijection e and uses determinant multiplicativity. Simultaneous reindexing
of U preserves its determinant. The final theorem allows every proved
row-to-original-column ordering, rather than silently declaring a lexicographic
ordering. The canonicalOriginalIntegerMatrix definition uses the previous
matrixIndexEquiv followed by the explicit originalIndexEquiv. The former is
a noncomputable library choice from proved equal cardinalities; the all-orderings
theorem makes that choice harmless for nonvanishing. Neither the nonzero
integer determinant nor its factor U is claimed to be a unit over Z.

## Cumulative verification and reproducibility

The integer-origin milestone compiled 30 positive modules and checked thirteen expected
failures (43 compilation checks), auditing exactly 354 declarations. See
[RATIONAL.md](RATIONAL.md) for the current cumulative counts. The new
regressions check a real original matrix entry 27 at N=1, its global matrix
product entry, the even diagonal factor 2, a below-diagonal zero and a zero
between different endpoint blocks. They prove the entire U matrix is the
identity at N=0 and the original grouped matrix then equals D. Negative
checks reject replacing the integer diagonal factor 2 by 1 and omitting U
(the actual entry 27 differs from its Newton entry 13).

All previous 38 Lean sources and every toolchain/dependency pin are unchanged.
The sole added direct external import, Mathlib.LinearAlgebra.Matrix.Block,
is source-attested at the same existing mathlib revision. All declaration
axioms are audited, allowing only propext, Classical.choice and Quot.sound.
The replay rejects sorry, admit, native_decide, custom axioms and unsafe
proof declarations, and treats warnings as errors. Exact compiler commands,
source/dependency hashes, declarations and logs are retained under verification/.

Use the README replay command with --out /tmp/pi-origin-replay. The source-only
checkpoint is separate from the root ZhangLS library. No full containing-repository
build is claimed; old Lean 4.34.1 checkpoints are preserved but were not rerun.

## Scope still outside this milestone

This completes the actual unnormalized integer-origin determinant nonvanishing
bridge for the fixed weight-2 profile. It does not formalize a multivariate
integer collision-quotient, residual-polynomial bridge, uniform archimedean
estimate, arbitrary arithmetic weights or a π badly-approximability theorem.
The later [RATIONAL.md](RATIONAL.md) milestone separately formalizes the requested
factorial scaling and actual rational origin matrix.
