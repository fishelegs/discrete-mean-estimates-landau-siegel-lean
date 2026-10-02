import ZhangLS.AssumptionA

/-!
# Regression witness for the legacy Assumption A defect

This is not part of the trusted proof.  It records, as a Lean proposition, why the old
`AssumptionA` cannot represent the paper's contradiction hypothesis: the legacy `L` is
literally defined to be the right-hand side plus `1`.
-/

namespace ZhangLS.Audit

/-- Under the legacy definition, Assumption A is impossible for every `D` and `χ`, without
using any analytic number theory.  This theorem should disappear only after legacy `L` is
removed from the trusted dependency graph. -/
theorem legacy_assumptionA_impossible (D : ℕ) (χ : ZhangLS.RealPrimChar D) :
    ¬ ZhangLS.AssumptionA D χ := by
  intro h
  unfold ZhangLS.AssumptionA ZhangLS.L ZhangLS.ℒ at h
  linarith

end ZhangLS.Audit
