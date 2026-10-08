# Integral Newton helper milestone

This stage uses actual integer polynomials and monic synthetic division.
It proves integral Newton coefficients, their reduction to the previously
proved concrete F₂ matrix, the original frequency profile and column reindexing,
and every entry of the proposed integer evaluation factorization. The helper milestone did
not yet prove nonvanishing of the original integer evaluation determinant.
[ORIGIN.md](ORIGIN.md) now completes that global bridge using these unchanged
Lean sources.

## Coefficients over the original ring

`NewtonIntegral.lean` defines, over any commutative ring R,

```text
q_0 = p
q_(k+1) = q_k /ₘ (X - nodes(k))
D_k = q_k.eval(nodes(k))
P_k = product_{i<k} (X - nodes(i))
```

Division is by a monic polynomial in R[X], not by node differences.
`newton_step` proves q_k = C(D_k) + (X-nodes(k))q_(k+1).
`newton_expansion` proves the finite polynomial identity

```text
p = sum_{k<n} C(D_k) P_k + P_n q_n.
```

`newton_evaluation` proves p(nodes(j)) equals
sum_{k≤j} D_k product_{i<k}(nodes(j)-nodes(i)).
These definitions stay over Z for integer inputs, including repeated nodes.
No rational denominator or invertibility of an even element in F₂ is used.

Monic division commutes with ring homomorphisms (`newtonQuotient_map`).
When all nodes map to a common a, `newtonCoefficient_collision` proves

```lean
theorem newtonCoefficient_collision (f : R →+* S) (p : R[X]) (nodes : ℕ → R)
    (a : S) (hnodes : ∀ i, f (nodes i) = a) (k : ℕ) :
    f (newtonCoefficient p nodes k) = (p.map f |>.comp (X + C a)).coeff k
```

Thus the reduced coefficient is the actual Hasse coefficient. This stage
uses synthetic division; an identity with separately defined complete
homogeneous symmetric polynomials is not claimed or needed by these proofs.

## Actual integer entries and the Newton determinant

`IntegerNewtonMatrix.lean` defines the actual origin entry as

```text
binom(s,c-a) h^(s-(c-a)), if a≤c and c-a≤s; otherwise zero.
```

The grouped natural exponent gives the requested integer s-c+a under the
guard and preserves 0^0=1. `originPolynomial_eval` realizes each entry as
an evaluation of an explicit polynomial in Z[X].

The ordered nodes are `frequencyNode e k = 2*k + epsilon` over Z.
Their reduction modulo two is the endpoint epsilon. `originPolynomial_hasse`
proves every guarded binomial entry, including all zero cases, using the
proved binomial interchange identity. Therefore

```lean
theorem integerNewtonEntry_mod_two (s a c k : ℕ) (e : Bool) :
    (integerNewtonEntry s a c k e : F2) = binaryEntry s a e c k
```

`integerNewtonMatrix_mod_two` and `squareIntegerNewtonMatrix_mod_two` prove
this equality for the actual finite matrices, with the same row and column
indices as the binary milestone. Consequently, for every column bijection e,

```lean
theorem integerNewton_det_mod_two_ne_zero (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    ((squareIntegerNewtonMatrix N e).det : F2) ≠ 0

theorem integerNewton_det_ne_zero (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    (squareIntegerNewtonMatrix N e).det ≠ 0
```

This is the Newton determinant. The original determinant is proved in the later
[ORIGIN.md](ORIGIN.md) milestone. No factorial-normalized rational/integer
determinant is formalized here.

## The exact frequency profile and local factorization

`FrequencyProfile.lean` defines n_0=N+1 and n_j=N-floor((j-1)/2) for j>0,
with L_(2j)=n_j and L_(2j+1)=3n_j. Original labels are actual pairs (h,c)
with h≤4N+1 and c<L_h.

`pair_prefix_iff` and `frequency_prefix_iff` prove that a block (epsilon,c)
contains exactly the nodes epsilon+2k with

```text
c < d_epsilon (N+1), k ≤ 2(N-floor(c/d_epsilon)).
```

The special first pair is included in the definitions and proofs, also at N=0.
`originalIndexEquiv` is a proved bijection from the previous column indices
to these original labels. `originLabel_card` proves their count is 4(N+1)².
The actual matrix `originalIntegerMatrix` uses exactly these labels and the
integer origin formula, not an assumed equivalent abstract map.

`columnPrefix` constructs every earlier node in an actual block as an actual
column. `originalIntegerMatrix_block_factorization` proves for every row r
and original column with node j the finite entry formula

```text
B_group[r,j] = sum_{k≤j} integerNewtonMatrix[r,k] U[k,j]
U[k,j] = product_{i<k} (frequencyNode(e,j)-frequencyNode(e,i)).
```

The D entries in this formula are entries of the actual finite Newton matrix.
`newtonEvaluationFactor_above` proves U[k,j]=0 for j<k.
`newtonEvaluationFactor_diagonal_ne_zero` proves every diagonal product is
nonzero over Z from the distinct integer nodes. The helper milestone left
global matrix multiplication and determinant factorization as remaining work.
The later [ORIGIN.md](ORIGIN.md) milestone now assembles them and proves
original determinant nonvanishing using these unchanged helpers.

## Verification

The Newton-helper milestone compiled 27 positive modules and checked eleven expected
failures (38 compilation checks), auditing exactly 329 declarations. The current
cumulative counts are documented in [ORIGIN.md](ORIGIN.md). All earlier
Lean sources and every dependency/toolchain pin remain byte-for-byte unchanged.
Only propext, Classical.choice and Quot.sound are permitted. Warnings are errors,
and the replay rejects sorry, admit, native_decide, custom axioms and unsafe
proof declarations. Use the README command with `--out /tmp/pi-newton-replay`.

New regressions verify the actual length profile at N=0 and N=1, original-column
counts at N=0,1,2, a boundary-label round trip, guards and 0^0, and exact integral
Newton coefficients 13 and 9 for X³ at nodes 1,3,5. These integer values are
proved from the evaluation expansion over Z. They also check reduced binomial
parity and integer diagonal factors 1,2,8,48. Negative tests reject replacing
the exceptional odd first length 3 by 1 and replacing the integer coefficient
13 by 12. Exact compiler commands, source hashes and axiom sets are preserved
under verification/; compiled files stay outside the repository.

No full containing-repository build is claimed. The old Lean 4.34.1 checkpoints
are preserved but were not rerun. The integer collision-quotient, rational
factorial normalization, residual-polynomial and analytic bridges remain
outside the proved scope. No arbitrary-weight result or π badly-approximability
theorem follows from the formalized declarations.
