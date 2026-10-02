# Step 31 — Legacy compilation repairs and a false-statement regression

This step repairs the legacy modules that blocked the full repository build after
Step 30. It preserves the distinction between compiling a formal statement and
proving that statement models the paper.

## Repairs

- Add explicit Mathlib imports for ring tactics and shared real analysis objects.
- Replace obsolete finite-set folds with finite sums and Boolean-equality proofs
  with simplification using the actual inequalities.
- Use nonlinear arithmetic or explicit nonnegative product bounds where `omega`
  or unqualified `nlinarith` lacked the necessary information.
- Correct division-bound multiplication order, rewriting scope, a proof/value typo,
  and the noncomputable real logarithmic-weight definition.
- Use `Real.pi_lt_d4`; the old premise `π ≤ 4` cannot establish `2π ≤ 7`.

## Mathematical correction

The old `taylor_truncation_absorbed_linear` statement was false. Taking
`quad_error = 0` and `linear_bound = -1` satisfies its two hypotheses but violates
its conclusion `0 ≤ -1/5`. The repaired statement requires
`0 ≤ linear_bound ≤ 1/10`. There were no theorem callers to migrate.
`audit/Step31LegacyRegression.lean` kernel-checks the counterexample and the
corrected public interface.

Three unused legacy arithmetic interfaces now use `ℝ` instead of `Float`:
`Proposition_2_1_Union_Bound`, `nu_of_divisor_proved`, and
`Cor_a_bound_Positive_Transfer`. These are intentional API changes: opaque machine
floating-point operations were being treated as ordered real algebra. Numerical
Float definitions elsewhere remain numerical scaffolding.

## Verification and remaining mathematics

The full `lake build` succeeded under Lean 4.30.0 (3529 jobs). The authoritative
`tools/verify_all_lean.sh` now also compiles every audit regression after the full
build; its generated report records the final result.
The final authoritative run completed with `LEAN_KERNEL_VERIFICATION=PASS`,
including all 19 Spec modules, the full build, and all three audit modules.
The per-module Spec verifier builds each module's dependency closure before
checking its source, so it also works on a fresh CI checkout without local oleans.

The semantic scanner still finds 38 review candidates. In particular the legacy
`L` is defined to equal the Assumption-A threshold plus one, making that assumption
impossible by construction. Its regression witness remains in the full gate.
No conclusion about a defect in Zhang's paper follows from a defect in this legacy
formalization. The next mathematical obligation is the trusted contour
approximation and small-error bound connecting the Gaussian sum to `L'(1,χ)`;
the paper-level theorem targets remain unproved.
