# Migration Step 57 — completing Zhang's Lemma 5.7

This step closes the final analytic gap in the trusted reconstruction of
Lemma 5.7.

## Match the paper's scope

Zhang's §2 says that throughout the paper the conductor `D` is greater than a
sufficiently large effectively computable number. Lemma 5.7 then omits this
standing convention and states

`L'(1, χ) ≫ D / φ(D)`.

The earlier Lean specification had quantified over every `D > 1`, which was
stronger than the paper. `Lemma57AtConstant` in
`ZhangLS/Spec/Lemma57.lean` now makes the paper's uniform large-modulus
threshold explicit.

## Analytic closure

Step 55 proves Abel–Mellin estimates for zeta and the character L-function,
including the critical-line estimate `‖ζ(1/2 + it)‖ ≤ 1 + 2‖1/2 + it‖`.
Combined with the character bound, this gives the contour-shift factor an
explicit quadratic bound `288 D (1 + t²)` on the shifted strip. The complete
infinite contour-shift identity is unconditional.

Step 56 specializes the growth bound to the line `Re(s) = -1/2` and combines
it with the proved Gaussian second moment. For all sufficiently large `D`,
under normalized Assumption (A), the shifted integral and residue correction
fit the required error budget. Mellin identity, contour shift, and the
already-proved arithmetic main-term bound then give

`(1/16) · D / φ(D) ≤ L'(1, χ)`.

Step 57 packages this as `lemma57_target_proved : Lemma57Target` in
`ZhangLS/Spec/Lemma57LeftQuadraticGrowth.lean`. The statement assumes (A), as
the paper's Lemma 5.7 does in context, and carries a threshold uniform over
all characters.

## Verification

The targeted Lake build and complete `tools/verify_all_lean.sh` run both
passed after updating the statement's quantifiers. The threshold is proved to
exist via asymptotic limit theorems; the target does not separately formalize
a computable numeric encoding for that threshold. See `audit/STEP57_STATUS.md`
and `audit/lean_kernel_verification.txt`. The other paper-numbered results
remain open; completing this lemma does not prove Theorem 1 or Theorem 2.
