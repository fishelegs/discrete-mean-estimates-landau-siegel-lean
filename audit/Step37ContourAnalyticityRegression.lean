import ZhangLS.Spec.Lemma57ContourAnalyticity

/-!
# Step 37 contour analyticity regression

This check pins the global analyticity of the pole-removed numerator, the
isolated nature of the pole, and the exact local circle residue integral.
-/

namespace ZhangLS.Spec

open Complex

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Differentiable ℂ (lemma57ResidueNumerator χ) :=
  lemma57ResidueNumerator_differentiable χ hD

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (lemma57MellinIntegrand χ) s :=
  lemma57MellinIntegrand_analyticAt χ hD hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {R : ℝ} (hR : 0 < R) :
    CircleIntegrable (lemma57MellinIntegrand χ) 0 R :=
  lemma57MellinIntegrand_circleIntegrable χ hD hR

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {R : ℝ} (hR : 0 < R) :
    lemma57NormalizedCircleIntegral χ R = lemma57ResidueValue χ :=
  lemma57NormalizedCircleIntegral_eq_residueValue χ hD hR

end ZhangLS.Spec
