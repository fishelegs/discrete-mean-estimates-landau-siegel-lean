# Full fixed-family staircase intersection theorem

This records the polynomial-core milestone. [MATRIX.md](MATRIX.md) now
completes the explicit binomial-entry binary-matrix bridge and invertibility.
Every proof and regression source from this milestone is preserved.

The all-scale algebraic theorem is now proved in Lean 4.30.0 for the actual
F₂ monomial span and explicit endpoint-generated ideals. The result uses
Q=t⁴+t²+y², d₀=1 and d₁=3, exactly as in the earlier colon and bridge files.
All earlier proof, regression, negative-check and audit sources remain
byte-for-byte unchanged. The dependency pins are unchanged.

## Exact final definitions and theorem types

In `src/StaircaseNonvanishing.lean`, namespace `PiWeightedColon`:

```lean
def V_N (N : ℕ) : Submodule F2 Plane :=
  Submodule.span F2 {f | ∃ s a, a ≤ 2 * N + 1 ∧
    s ≤ 4 * (N - a / 2) + 1 ∧ f = mono s a}

theorem V_N_membership (N : ℕ) (f : Plane) :
  f ∈ V_N N ↔ StairBound (4 * N + 1) f

theorem V_N_bounded_division (N : ℕ) (f : Plane) (hf : f ∈ V_N N) :
  ∃ h : Plane, ∃ A B : Line,
    f = globalQ * h + linearRemainder A B ∧
    (if N = 0 then h = 0 else h ∈ V_N (N - 1)) ∧
    A.natDegree ≤ 4 * N + 1 ∧ B.natDegree ≤ 4 * N + 1

theorem V_N_dataIntersection_zero (N : ℕ) (f : Plane)
    (hf : f ∈ V_N N) (hI : f ∈ dataIntersection N) : f = 0

theorem V_N_inf_dataIntersection (N : ℕ) :
  V_N N ⊓ (dataIntersection N).restrictScalars F2 = ⊥
```

`restrictScalars F2` views the actual ideal I_N as an F₂ subspace; it does
not change its underlying elements. The last statement is precisely
V_N∩I_N={0}. There is no degree, decomposition, quotient, local divisibility,
noncancellation, matrix-invertibility or determinant hypothesis in the final
intersection theorem.

In `src/StaircaseDivision.lean`:

```lean
def stairWeight (s a : ℕ) : ℕ := s + 4 * (a / 2)
def StairBound (M : ℕ) (f : Plane) : Prop :=
  ∀ s a, M < stairWeight s a → coeff f s a = 0
def QuotBound (M : ℕ) (h : Plane) : Prop :=
  ∀ s a, M < stairWeight s a + 4 → coeff h s a = 0
```

`V_N_eq_bound` proves equality of the actual span with the subspace defined
by that coefficient condition. `staircase_index_iff` verifies that the
floored-weight condition is exactly the given staircase, including a≤2N+1.
The reverse span inclusion uses the actual finite nonzero-coefficient
expansion and scalar multiples of the stated monomials.

## Bounded division and induction

Division is constructed by a strong induction on a for each actual monomial
`bimono s a b = t^s y^a b`, retaining its F₂ coefficient b. The checked identity is

```text
t^s y^(a+2) b = Q t^s y^a b + t^(s+4) y^a b + t^(s+2) y^a b.
```

For a=0,1 the term is already a linear remainder and its quotient is zero.
In the recursive case the last two terms have a lower y exponent. The first
recursive term has the same staircase weight as the original term, and the
second has weight two less. The new direct quotient term has weight four
less. Adding the two recursive decompositions therefore preserves the exact
`QuotBound M` and the bounds deg A,deg B≤M. Closure under addition and finite
sums gives `staircase_division` for every polynomial satisfying `StairBound M`.
This is a proved finite polynomial decomposition, not a presumed output of an
unverified division algorithm.

At N=0, `QuotBound 1 h` forces every coefficient of h to vanish, hence h=0.
At N+1, `QuotBound (4*(N+1)+1) h` gives h∈V_N. Applying the already proved
`dataIntersection_factor_Q` to f∈I_(N+1) gives f=Qh. The colon identity then
puts h in I_N. The induction hypothesis makes h, and therefore f, zero.
The base case applies the same actual-ideal remainder theorem with h=0.

## Verification and boundaries

The cumulative replay compiles 17 positive modules and checks seven expected
failures. It audits all 195 definitions, instances and theorems, including
regression declarations. Every axiom report is checked; only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. The proof sources contain no
`sorry`, `admit`, `native_decide`, custom axiom or unsafe declaration.
Warnings are errors. Full types, definitions, audit logs, source hashes and
compiler commands are committed under `verification/`.

The new positive regressions include both parities on the top staircase edge,
the explicit y⁴ division with quotient Q and remainder t⁸+t⁴, the sharp
four-unit quotient loss, a nonzero z(z−1)∈I₀ outside V₀, and properness of I_N.
The new negative tests reject dropping the staircase hypothesis and incorrectly
placing that quotient Q in V₀. Every prior regression and negative test still runs.
Use the `README.md` replay command with `--out /tmp/pi-all-scale-replay`.
The dedicated existing GitHub workflow runs that same expanded script.

This completes the stated fixed-family polynomial intersection theorem. The
subsequent explicit coefficient-map/binomial-entry and dimension/invertibility
bridge is now proved in `MATRIX.md`. Integer collision-quotient, rational/integer
determinant normalization and parity, and residual-polynomial bridges remain
separate and unformalized. The arithmetic application is limited to
the fixed weight-2 family; this algebraic theorem does not automatically cover
arbitrary weights. No uniform archimedean lower bound or π badly-approximability
theorem follows or is claimed. The older Lean 4.34.1 checkpoint suites were not
rerun, and no full containing-repository build is claimed.
