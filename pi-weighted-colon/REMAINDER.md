# Conditional remainder vanishing

This records the earlier conditional milestone. The next milestone,
[BRIDGE.md](BRIDGE.md), derives these divisibility inputs from the actual
endpoint ideals. This file preserves the earlier theorem statements and checks.

This extends the proved colon lemma with the univariate remainder argument.
`Line = Polynomial (ZMod 2)`, `X` represents t, and `u = X+1`.
Both branch implications are proved for **every** natural N. Their names refer
to the branches in the intended application; parity itself is unnecessary once
the relevant divisibility conditions are available.

## Exact theorem types

From `src/RemainderVanish.lean`, in namespace `PiWeightedColon`:

```lean
theorem remainder_even (N : ℕ) (A B : Line)
    (hAdeg : A.natDegree ≤ 4 * N + 1) (hBdeg : B.natDegree ≤ 4 * N + 1)
    (hAt : (X : Line) ^ (N + 1) ∣ A) (hBt : (X : Line) ^ N ∣ B)
    (hAu : u ^ (3 * N) ∣ A) (hBu : u ^ (3 * N) ∣ B)
    (hAB : u ^ (3 * N + 3) ∣ A + u * B) : A = 0 ∧ B = 0

theorem remainder_odd (N : ℕ) (A B : Line)
    (hAdeg : A.natDegree ≤ 4 * N + 1) (hBdeg : B.natDegree ≤ 4 * N + 1)
    (hAt : (X : Line) ^ (N + 1) ∣ A) (hBt : (X : Line) ^ N ∣ B)
    (hAu : u ^ (3 * N + 1) ∣ A) (hBu : u ^ (3 * N) ∣ B)
    (hAB : u ^ (3 * N + 3) ∣ A + X ^ 2 * u * B) : A = 0 ∧ B = 0

theorem remainder_by_parity (N : ℕ) (A B : Line)
    (hAdeg : A.natDegree ≤ 4 * N + 1) (hBdeg : B.natDegree ≤ 4 * N + 1)
    (hAt : (X : Line) ^ (N + 1) ∣ A) (hBt : (X : Line) ^ N ∣ B)
    (hAu : if Even N then u ^ (3 * N) ∣ A else u ^ (3 * N + 1) ∣ A)
    (hBu : u ^ (3 * N) ∣ B)
    (hAB : if Even N then u ^ (3 * N + 3) ∣ A + u * B
      else u ^ (3 * N + 3) ∣ A + X ^ 2 * u * B) : A = 0 ∧ B = 0
```

These hypotheses are explicit proof inputs, not axioms and not conclusions
derived from `dataIntersection` in this batch. The full types and the dependency
sets of all 17 added declarations are printed in
`verification/RemainderAudit.log`.

## Argument

The proof establishes coprimality of X and u, combines their power divisors,
and controls the degree of the remaining factor.

In the even condition package,
`A = X^(N+1)*u^(3N)*C a` and `B = X^N*u^(3N)*b`, with `b.natDegree ≤ 1`.
Cancelling the common u power and the coprime X power from the coupled condition
shows `u³ ∣ C a*X + u*b`. The polynomial on the right has degree at most two,
so it is zero. Evaluation at t=1 gives `a=0`, and cancellation of the nonzero
factor u gives `b=0`.

In the odd condition package, `X^(N+1)*u^(3N+1)` divides A and has degree
`4N+2`, greater than A's allowed degree. Thus A is zero. Write
`B = X^N*u^(3N)*b`, with `b.natDegree ≤ 1`. The remaining coupled condition
forces `u² ∣ b`, so b and B are zero.

## Checks and boundaries

The combined replay runs eight positive compiler checks and four expected
failures, and audits all 75 declarations across both milestones. The earlier
colon proof and its regression sources remain byte-for-byte unchanged.

New positive checks cover the even N=0 boundary, the odd branch's degree
obstruction, and actual nonzero counterexamples to dropping the coupled
condition or the degree bound. The new negative checks fail only on the intended
missing condition `(X+1)³ ∣ X` and the false degree comparison `4 ≤ 1`.
The previous two negative tests and all previous axiom checks still run.

The conditional milestone did not include a quotient model or ideal image
calculation. These are now supplied in `BRIDGE.md`, and `ALL_SCALE.md` completes the
staircase-bounded division and final V_N induction. The binary matrix bridge is now proved in `MATRIX.md`; the integer/rational
determinant and residual-polynomial bridges remain unformalized. The conditional
remainder theorem alone does not give the full algebraic theorem, and no
π badly-approximability statement is proved.

## Reproduce and CI

Use the command in `README.md`; it now includes every colon and remainder check.
The dependency pins remain Lean 4.30.0 and mathlib
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. The committed receipt and source
hashes refer to the exact compiled sources, and no binary Lean files are
committed.

`.github/workflows/pi-algebraic.yml` adds one separate GitHub Actions job that
provisions the existing committed dependency manifest, verifies that no pin
file changed, and runs the same replay script. It uploads the receipt and logs.
The workflow introduces no secrets, credentials or expanded permissions, and
does not alter the existing `lean.yml` jobs. Local YAML and shell syntax checks
are recorded in `verification/workflow-validation.json`; those are not a claim
that the remote GitHub run has completed.

The older 4.34.1 π checkpoints remain preserved and were not rerun on the
4.30.0 machine. A full containing-repository build is not claimed.
