import ZhangLS.Spec.Lemma56CharacterAbel

/-! # Actual Abel-integral majorant for arbitrary nonprincipal characters -/

namespace ZhangLS.Spec
open Finset Complex MeasureTheory Set
open scoped Real
set_option maxHeartbeats 1000000

/-- For positive real part, the Abel integrand has an explicit integrable
majorant: the modulus times a decaying real power. -/
theorem lemma56_actual_abel_integrand_integrable
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun t : ℝ =>
      (∑ n ∈ Icc 1 ⌊t⌋₊, θ (n : ZMod r)) * (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
  have hmeas : Measurable (fun t : ℝ =>
      ∑ n ∈ Icc 1 ⌊t⌋₊, θ (n : ZMod r)) :=
    (measurable_of_countable
      (fun N : ℕ => ∑ n ∈ Icc 1 N, θ (n : ZMod r))).comp Nat.measurable_floor
  have hkernel : ContinuousOn (fun t : ℝ => (t : ℂ) ^ (-(s + 1))) (Ioi 1) := by
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const t (-(s + 1))
      (Or.inr (by linarith [mem_Ioi.mp ht]))).continuousWithinAt
  have hmaj : IntegrableOn
      (fun t : ℝ => (r : ℝ) * t ^ (-s.re - 1)) (Ioi 1) :=
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
      (lemma56_character_norm_sum_Icc_le_modulus θ hθ ⌊t⌋₊)
      (Real.rpow_nonneg htpos.le _)

/-- The undamped Abel integral has a conductor-linear bound on the entire
open right half-plane. The denominator is the real part of `s`. -/
theorem lemma56_actual_abelIntegral_norm_bound
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {s : ℂ} (hs : 0 < s.re) :
    ‖lemma56AbelIntegral θ s‖ ≤ (r : ℝ) / s.re := by
  have hint := lemma56_actual_abel_integrand_integrable θ hθ hs
  have hmaj : IntegrableOn
      (fun t : ℝ => (r : ℝ) * t ^ (-s.re - 1)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)).const_mul _
  unfold lemma56AbelIntegral
  calc
    ‖∫ t : ℝ in Ioi 1,
        (∑ n ∈ Icc 1 ⌊t⌋₊, θ (n : ZMod r)) * (t : ℂ) ^ (-(s + 1))‖ ≤
      ∫ t : ℝ in Ioi 1,
        ‖(∑ n ∈ Icc 1 ⌊t⌋₊, θ (n : ZMod r)) *
          (t : ℂ) ^ (-(s + 1))‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ t : ℝ in Ioi 1, (r : ℝ) * t ^ (-s.re - 1) := by
      apply integral_mono_ae hint.norm hmaj
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have htpos : 0 < t := by linarith [mem_Ioi.mp ht]
      rw [norm_mul, norm_cpow_eq_rpow_re_of_pos htpos]
      have hre : (-(s + 1)).re = -s.re - 1 := by simp; ring
      rw [hre]
      exact mul_le_mul_of_nonneg_right
        (lemma56_character_norm_sum_Icc_le_modulus θ hθ ⌊t⌋₊)
        (Real.rpow_nonneg htpos.le _)
    _ = (r : ℝ) / s.re := by
      rw [MeasureTheory.integral_const_mul,
        integral_Ioi_rpow_of_lt (by linarith : -s.re - 1 < -1)
          (by norm_num : (0 : ℝ) < 1)]
      simp only [Real.one_rpow]
      have hden : -s.re - 1 + 1 = -s.re := by ring
      rw [hden]
      ring

/-- The actual Dirichlet L-function has an explicit conductor-linear,
linear-in-height bound in the initial half-plane of absolute convergence. -/
theorem lemma56_actual_LFunction_bound_re_gt_one
    {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    ‖DirichletCharacter.LFunction θ s‖ ≤ ‖s‖ * ((r : ℝ) / s.re) := by
  rw [lemma56_actual_LFunction_eq_abelIntegral θ hθ hs]
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left
    (lemma56_actual_abelIntegral_norm_bound θ hθ (by linarith)) (norm_nonneg _)

end ZhangLS.Spec
