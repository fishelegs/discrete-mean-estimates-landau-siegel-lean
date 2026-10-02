import ZhangLS.Spec.Lemma57GaussianQuadraticMoment

/-! # Step 49 quadratic Gaussian moment regression -/

namespace ZhangLS.Spec

open Complex
open scoped Real

example {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ, (1 + t ^ 2) * Real.exp (-(2 * b) * t ^ 2)) ≤
      (1 + b⁻¹) * Real.sqrt (Real.pi / b) :=
  integral_one_add_sq_mul_gaussian_le hb

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {C : ℝ} (hC : 0 ≤ C) (hgrowth : Lemma57LeftQuadraticGrowth χ C) :
    lemma57LeftGaussianEnvelope χ ≤
      C * (1 + 8 * Real.log (D : ℝ) ^ 30) *
        Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30) :=
  lemma57LeftGaussianEnvelope_le_of_quadratic χ hD hC hgrowth

end ZhangLS.Spec
