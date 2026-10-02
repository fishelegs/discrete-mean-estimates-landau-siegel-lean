import ZhangLS.Spec.Lemma57ResidueBudget

/-! # Step 48 residue-budget regression -/

namespace ZhangLS.Spec

example {D : ℕ} (hD : 1 < D) : 1 ≤ lemma57Scale D :=
  lemma57Scale_ge_one hD

example : ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → 2 ≤ Real.log (D : ℝ) :=
  exists_modulus_threshold_log_ge_two

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hlog : 2 ≤ Real.log (D : ℝ)) (hA : NormalizedAssumptionA χ) :
    |lemma57ResidueCorrection χ| ≤ (1 : ℝ) / 32 * lemma57Scale D :=
  lemma57ResidueCorrection_abs_le_scale_thirtysecond χ hD hlog hA

end ZhangLS.Spec
