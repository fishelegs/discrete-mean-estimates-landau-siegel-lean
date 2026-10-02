import ZhangLS.Spec.Lemma57ShiftedIntegralEnvelope

/-! # Step 46 shifted-integral quantitative-envelope regression -/

namespace ZhangLS.Spec

open Complex

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    ‖lemma57VerticalIntegral χ (-(1 : ℝ) / 2)‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (Real.exp (-2 * Real.log (D : ℝ) +
          1 / (16 * Real.log (D : ℝ) ^ 30)) *
          lemma57LeftGaussianEnvelope χ) :=
  lemma57LeftVerticalIntegral_norm_le_envelope χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {C : ℝ} (hgrowth : Lemma57LeftSubGaussianGrowth χ C) :
    lemma57LeftGaussianEnvelope χ ≤
      C * Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30) :=
  lemma57LeftGaussianEnvelope_le_of_subGaussian χ hD hgrowth

end ZhangLS.Spec
