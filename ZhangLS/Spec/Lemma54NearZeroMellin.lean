import ZhangLS.Spec.Lemma54CentralDeltaApproximation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # The actual Mellin integral near zero has exponentially small mass -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma54NearZeroConstant : ℝ :=
  2 * Real.sqrt Real.pi + lemma53SmallErrorConstant

theorem lemma54_near_zero_constant_pos : 0 < lemma54NearZeroConstant := by
  unfold lemma54NearZeroConstant lemma53SmallErrorConstant
  positivity

theorem lemma54_near_zero_gap {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {x : ℝ} (hx : x ≤ 1) : lemma23PaperL D ^ 405 ≤ |x - lemma51PaperT0 D| := by
  have hw := lemma54_window_width_le_half_center hL
  have hw1 : 1 ≤ lemma23PaperL D ^ 405 := one_le_pow₀ (by linarith)
  have ha := neg_le_abs (x - lemma51PaperT0 D)
  linarith

theorem lemma54_gaussian_density_le_prefactor {B : ℝ} (hB : 0 < B) (t x : ℝ) :
    lemma54GaussianDensity B t x ≤ Real.sqrt Real.pi / B := by
  unfold lemma54GaussianDensity
  have he : Real.exp (-((Real.pi * (x - t) / B) ^ 2)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (neg_nonpos.mpr (sq_nonneg _))
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ Real.sqrt Real.pi / B)

theorem lemma54_actual_gaussian_near_zero {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {x : ℝ} (hx : x ≤ 1) :
    lemma54PaperGaussian D x ≤ Real.sqrt Real.pi * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  let B := lemma53PaperScale D
  have hB1 : 1 ≤ B := lemma54_scale_ge_one hL
  have hB : 0 < B := by linarith
  have hw0 : 0 ≤ lemma23PaperL D ^ 405 := pow_nonneg (by linarith) _
  have hg := lemma54_gaussian_exterior_pointwise hB hw0 (lemma54_near_zero_gap hL hx)
  calc
    _ ≤ (2 * Real.exp (-((Real.pi * lemma23PaperL D ^ 405 / B) ^ 2) / 2)) *
        lemma54GaussianDensity (2 * B) (lemma51PaperT0 D) x := hg
    _ ≤ (2 * Real.exp (-(lemma23PaperL D ^ 10) / 2)) *
        (Real.sqrt Real.pi / (2 * B)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left (lemma54_window_gaussian_damping hL) (by norm_num))
        (lemma54_gaussian_density_le_prefactor (by positivity : 0 < 2 * B) _ _)
        (lemma54_gaussian_density_pos (by positivity : 0 < 2 * B) _ _).le (by positivity)
    _ = (Real.sqrt Real.pi / B) * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (div_le_self (Real.sqrt_nonneg _) hB1) (Real.exp_pos _).le

theorem lemma54_actual_delta_small_gaussian_bound {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {x : ℝ} (hx : 0 < x)
    (hxT : x ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ)) :
    ‖lemma53PaperDelta D x‖ ≤ 2 * lemma54PaperGaussian D x +
      lemma53SmallErrorConstant * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  have hg : 0 ≤ lemma54PaperGaussian D x := (lemma54_gaussian_density_pos (lemma53_scale_pos hD) _ _).le
  have hb := lemma53_small_range_estimate hD hL hx hxT
  rw [lemma54_actual_omega_eq_gaussian, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg] at hb
  have ha := (lemma54_disk_alpha_small hL).2
  have hp := mul_le_mul_of_nonneg_right (show lemma44PaperAlpha D ≤ 1 by linarith) hg
  have hn : ‖lemma53PaperDelta D x‖ ≤ ‖lemma53PaperDelta D x - (lemma54PaperGaussian D x : ℂ)‖ +
      lemma54PaperGaussian D x := by
    calc
      _ = ‖(lemma53PaperDelta D x - (lemma54PaperGaussian D x : ℂ)) +
          (lemma54PaperGaussian D x : ℂ)‖ := by congr 1; ring
      _ ≤ _ := by
        simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hg] using
          norm_add_le (lemma53PaperDelta D x - (lemma54PaperGaussian D x : ℂ))
            (lemma54PaperGaussian D x : ℂ)
  linarith

theorem lemma54_disk_near_zero_weight {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {s : ℂ} (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) : ‖(x : ℂ) ^ (s - 1)‖ ≤ x ^ (-(1 : ℝ) / 2) := by
  rw [norm_cpow_eq_rpow_re_of_pos hx, sub_re, one_re]
  exact Real.rpow_le_rpow_of_exponent_ge hx hx1 (by
    have hh := (lemma54_disk_closed_strip hL hs).1
    linarith)

theorem lemma54_half_inverse_unit_integrable :
    IntegrableOn (fun x : ℝ => x ^ (-(1 : ℝ) / 2)) (Ioc 0 1) :=
  (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := -(1 : ℝ) / 2) (by norm_num)).1

theorem lemma54_half_inverse_unit_integral :
    (∫ x : ℝ in Ioc 0 1, x ^ (-(1 : ℝ) / 2)) = 2 := by
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_rpow (Or.inl (by norm_num : (-1 : ℝ) < -(1 : ℝ) / 2))]
  norm_num

theorem lemma54_actual_near_zero_mellin_bound {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖∫ x : ℝ in Ioc 0 1, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x‖ ≤
      2 * lemma54NearZeroConstant * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  let E := Real.exp (-(lemma23PaperL D ^ 10) / 2)
  have hi : IntegrableOn (fun x : ℝ => (lemma54NearZeroConstant * E) * x ^ (-(1 : ℝ) / 2)) (Ioc 0 1) :=
    lemma54_half_inverse_unit_integrable.const_mul _
  calc
    _ ≤ ∫ x : ℝ in Ioc 0 1, (lemma54NearZeroConstant * E) * x ^ (-(1 : ℝ) / 2) := by
      apply norm_integral_le_of_norm_le hi
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
      have hT := (lemma54_small_endpoint_polynomial hL).1
      have hd := (lemma54_actual_delta_small_gaussian_bound hD hL hx.1 (hx.2.trans hT)).trans
        (add_le_add (mul_le_mul_of_nonneg_left (lemma54_actual_gaussian_near_zero hL hx.2)
          (by norm_num : (0 : ℝ) ≤ 2)) le_rfl)
      have hd' : ‖lemma53PaperDelta D x‖ ≤ lemma54NearZeroConstant * E := by
        dsimp [lemma54NearZeroConstant, E]
        nlinarith only [hd]
      rw [norm_mul]
      have hh := mul_le_mul (lemma54_disk_near_zero_weight hL hs hx.1 hx.2) hd'
        (norm_nonneg _) (Real.rpow_nonneg hx.1.le _)
      simpa only [mul_comm] using hh
    _ = _ := by rw [integral_const_mul, lemma54_half_inverse_unit_integral]; dsimp [E]; ring

end ZhangLS.Spec
