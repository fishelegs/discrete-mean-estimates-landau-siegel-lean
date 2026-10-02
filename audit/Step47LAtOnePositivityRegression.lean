import ZhangLS.Spec.Lemma57LAtOnePositivity

/-! # Step 47 positivity and residue-correction regression -/

namespace ZhangLS.Spec

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    0 < realLAtOne χ := realLAtOne_pos χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hA : NormalizedAssumptionA χ) :
    |lemma57ResidueCorrection χ| ≤
      |Real.eulerMascheroniConstant + 4 * Real.log (D : ℝ)| *
        (Real.log (D : ℝ)) ^ (-2022 : ℤ) :=
  lemma57ResidueCorrection_abs_le_of_assumptionA χ hD hA

end ZhangLS.Spec
