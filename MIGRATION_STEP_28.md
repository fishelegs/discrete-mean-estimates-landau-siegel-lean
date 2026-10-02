# Migration Step 28 — batch compile-risk cleanup

Step 28 is a batch source/API alignment pass against mathlib v4.30.0.  It does
not claim kernel verification: the current execution container still has no
`lean`/`lake` binary.

## Definite fixes

1. `reciprocalDivisorSum_eq_divisorSum_div` now casts the finite natural-number
   divisor sum explicitly with `Nat.cast_sum` before applying `Finset.sum_div`.
2. Natural exact division is transported to `ℝ` with the CharZero-specific
   `Nat.cast_div_charZero`, avoiding the incorrectly supplied nonzero parameter
   of the more general `Nat.cast_div`.
3. `inv_le_inv₀` is used with positivity proofs for both powers and `.2` is
   applied to the underlying reversed inequality.
4. `Finset.sum_eq_single` first proves the sum equals `χ.evalNat 1`, then uses
   `χ.evalNat_one`; the fallback side condition is proved from `1 ∈ divisors n`.
5. The square-reciprocal decomposition was corrected from `Ioo 8 N` to
   `Ioo 8 (N + 1)`.  The old interval omitted the endpoint `N`; the repaired
   interval covers exactly the intended tail `9, ..., N`.
6. `Finset.sum_union` receives an explicit `Disjoint` proof, and elementary
   inverse/product nonnegativity proofs no longer depend on fragile tactic
   inference.
7. `DirichletCharacter.norm_le_one` is invoked with its exact `ZMod D` argument.

## Verification

The authoritative command remains:

```sh
tools/verify_all_lean.sh
```

Static checks in this environment pass, but the command stops before kernel
checking because `lean` is unavailable.  Therefore Step 28 remains NOT_RUN for
kernel verification and is not called Lean-verified.
