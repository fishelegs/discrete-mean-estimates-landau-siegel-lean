import ZhangLS.Spec.CharacterLSeriesAbel

/-!
# A quantitative bound for the character Abel integral

The bounded partial sums from Step 51 give an absolutely convergent Abel
integral throughout the open right half-plane. This is a bound on that
integral, not yet a claim that it equals the analytically continued
Dirichlet L-function there.
-/

namespace ZhangLS.Spec

open Finset Complex MeasureTheory Set
open scoped Real

/-- The Abel integral of the actual character coefficients. -/
noncomputable def characterAbelIntegral {D : ℕ}
    (χ : RealPrimitiveCharacter D) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Ioi 1,
    (∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1))

/-- For positive real part, the Abel integrand has an explicit integrable
majorant: the modulus times a decaying real power. -/
theorem RealPrimitiveCharacter.abelIntegrand_integrable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ =>
      (∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hmeas : Measurable (fun t : ℝ =>
      ∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) :=
    (measurable_of_countable
      (fun N : ℕ => ∑ n ∈ Icc 1 N, χ.evalNat n)).comp Nat.measurable_floor
  have hkernel : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
      (Or.inr (by linarith [mem_Ioi.mp ht]))).continuousWithinAt
  have hmaj : IntegrableOn
      (fun t : ℝ => (D : ℝ) * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  apply Integrable.mono' hmaj
  · exact hmeas.aestronglyMeasurable.mul
      (hkernel.aestronglyMeasurable measurableSet_Ioi)
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
    rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htpos]
    have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
    rw [hre]
    exact mul_le_mul_of_nonneg_right
      (χ.norm_sum_Icc_evalNat_le_modulus hD ⌊t⌋₊)
      (Real.rpow_nonneg htpos.le _)

/-- The undamped Abel integral has a conductor-linear bound on the entire
open right half-plane. The denominator is the real part of `s`. -/
theorem RealPrimitiveCharacter.norm_characterAbelIntegral_le
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 0 < s.re) :
    ‖characterAbelIntegral χ s‖ ≤ (D : ℝ) / s.re := by
  have hint := χ.abelIntegrand_integrable hD hs
  have hmaj : IntegrableOn
      (fun t : ℝ => (D : ℝ) * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  unfold characterAbelIntegral
  calc
    ‖∫ t : ℝ in Ioi 1,
        (∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t : ℝ in Ioi 1,
        ‖(∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) *
          (t : ℂ) ^ (-(s + 1))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 1, (D : ℝ) * t ^ (-s.re - 1) := by
      apply integral_mono_ae hint.norm hmaj
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htpos]
      have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
      rw [hre]
      exact mul_le_mul_of_nonneg_right
        (χ.norm_sum_Icc_evalNat_le_modulus hD ⌊t⌋₊)
        (Real.rpow_nonneg htpos.le _)
    _ = (D : ℝ) / s.re := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1)
          (by norm_num : (0 : ℝ) < 1)]
      simp only [Real.one_rpow]
      have hden : -s.re - 1 + 1 = -s.re := by ring
      rw [hden]
      ring

/-- The actual Dirichlet L-function has an explicit conductor-linear,
linear-in-height bound in the initial half-plane of absolute convergence. -/
theorem RealPrimitiveCharacter.norm_dirichletLFunction_le_of_one_lt_re
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 1 < s.re) :
    ‖dirichletLFunction χ s‖ ≤ ‖s‖ * ((D : ℝ) / s.re) := by
  rw [dirichletLFunction_eq_abelIntegral χ hD hs]
  change ‖s * characterAbelIntegral χ s‖ ≤ ‖s‖ * ((D : ℝ) / s.re)
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (χ.norm_characterAbelIntegral_le hD (by linarith)) (norm_nonneg _)

end ZhangLS.Spec
