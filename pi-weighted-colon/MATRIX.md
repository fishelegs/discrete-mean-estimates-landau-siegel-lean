# Concrete binomial-entry matrix over F₂

This milestone proves the concrete binary-matrix bridge for every natural N,
using the previously verified polynomial theorem V_N∩I_N={0}. No equivalence
with an unspecified map, independent basis assertion, dimension assertion,
or determinant nonvanishing is assumed.

## Actual indices and dimensions

The finite grouped types are:

```lean
abbrev RowIndex (N : ℕ) := BlockIndex N 2 4 2
abbrev ColIndex (N : ℕ) := Σ e : Bool, BlockIndex N (endpointD e) 2 1
abbrev BlockIndex (N d p q : ℕ) :=
  Σ j : Fin (N + 1), Fin d × Fin (p * (N - j.val) + q)
```

A row has a=2j+r and the given s. A column has ε=e, c=d_ε j+r and the
given k. `rowLabelEquiv` and `colLabelEquiv` are proved bijections with the
original natural-number label sets:

```text
Rows (s,a): a≤2N+1, s≤4(N−floor(a/2))+1.
Columns (ε,c,k): c<d_ε(N+1), k≤2(N−floor(c/d_ε)); d_false=1,d_true=3.
```

The definitions `RowLabel` and `ColLabel` carry precisely these bounds.
Both label types have proved finite instances and cardinality 4(N+1)², as do
both grouped index types. `row_vector_dimension` and `col_vector_dimension`
also prove that the two corresponding F₂ vector spaces have finrank 4(N+1)².
The count is a proved all-N finite sum recurrence, not a guessed dimension.

## Displayed entries and the actual coefficient map

```lean
def binaryEntry (s a : ℕ) (e : Bool) (c k : ℕ) : F2 :=
  if k ≤ s ∧ a ≤ c ∧ c - a ≤ s - k then
    (s.choose k : F2) * ((s - k).choose (c - a) : F2) *
      endpoint e ^ (s - k - (c - a))
  else 0

def binaryMatrix (N : ℕ) : Matrix (RowIndex N) (ColIndex N) F2 :=
  fun r c => binaryEntry (rowS r) (rowA r) (colE c) (colC c) (colK c)
```

Under the guard, `entry_exponent_integer` proves that the grouped natural
exponent equals the nonnegative integer s−k−c+a. Grouping is essential:
iterated truncated natural subtraction would fail, for example at s=k=0,
a=c=1. The actual exponent there is zero, so 0^0=1.

`coordinate_bimono_coeff` proves the entry formula for every s,a,k,c, every
endpoint and every F₂ coefficient b, using the actual old `coordinate` map.
It includes all guard cases. `binaryMatrix_coefficient` identifies every
matrix entry with the coefficient of x^k y^c in (ε+x+y)^s y^a.

`rowPolynomial N v` is the actual finite sum of the staircase monomials with
row coefficients v. Its membership in V_N and exact recovery of each row
coefficient are proved. `rowPolynomial_columns` then proves, for every v,
that the actual data coefficients equal `v ᵥ* binaryMatrix N`.
`dataIntersection_iff_columns` proves that vanishing of precisely the finite
column coefficients is exactly membership in the actual ideal intersection.
Applying V_N∩I_N={0}, and recovering the row coefficients, proves the zero
kernel of this explicit matrix.

## Square matrix, ordering and determinant

```lean
def squareBinaryMatrix (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    Matrix (RowIndex N) (RowIndex N) F2 :=
  fun r s => binaryMatrix N r (e s)

theorem squareBinaryMatrix_det_ne_zero (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
  (squareBinaryMatrix N e).det ≠ 0

theorem squareBinaryMatrix_isUnit (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
  IsUnit (squareBinaryMatrix N e)

theorem squareBinaryMatrix_inverse (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
  squareBinaryMatrix N e * (squareBinaryMatrix N e)⁻¹ = 1 ∧
    (squareBinaryMatrix N e)⁻¹ * squareBinaryMatrix N e = 1

theorem canonicalBinaryMatrix_det_ne_zero (N : ℕ) :
  (canonicalBinaryMatrix N).det ≠ 0
```

Here `matrixIndexEquiv N` is constructed by `Fintype.equivOfCardEq` from the
proved cardinality equality, and `canonicalBinaryMatrix N` uses that chosen
bijection. This is a noncomputable library choice, not a claimed lexicographic
ordering of the tuples. The general determinant and inverse theorems hold for
**every** proved row-to-column bijection e, making the ordering dependence
explicit. Their matrix entries remain exactly the displayed binomial formula.

## Verification and remaining bridges

The cumulative replay now compiles 22 positive modules and checks nine intended
failures, auditing all 260 declarations. All previous proof/regression/audit
sources and all toolchain/dependency pins are unchanged. Only `propext`,
`Classical.choice` and `Quot.sound` are permitted; proof sources contain no
`sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration.
Warnings are errors. Full types, definitions, compiler commands, source hashes
and exact axiom sets are saved under `verification/`.

New regressions directly check actual row/column counts at N=0,1,2; guard
zeros; binomial parity; 0^0; a real transformed monomial coefficient; a real
explicit matrix entry; and original-label round trips. The two new negative
checks reject the wrong 0^0 boundary entry and the wrong choose(4,2) parity.
Every previous cumulative check still runs. The existing dedicated GitHub
workflow uses the same expanded replay script. Use the README command with
`--out /tmp/pi-matrix-replay` on MC6.

This proves invertibility and nonzero determinant **over F₂** of the concrete
matrix. It does not prove the subsequent integer collision-quotient,
rational/integer determinant normalization or parity, or residual-polynomial
bridge. The arithmetic application remains the fixed weight-2 family; no
arbitrary-weight extension, archimedean bound or π badly-approximability theorem
is claimed. Older Lean 4.34.1 checkpoints are preserved but were not rerun.
No full containing-repository build is claimed.
