import ZhangLS.Spec.Lemma44GaussianVerticalTail
import ZhangLS.Spec.Lemma44LocalRectangle

/-! # Gaussian decay on the actual finite horizontal edges -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

theorem lemma44_horizontal_gaussian_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {x v : ℝ} (hx : |x| ≤ 10) (hv : |v| = lemma23PaperL D ^ 20) :
    ‖lemma57OmegaOne D ((x : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp 1 * Real.exp (-(lemma23PaperL D ^ 10 / 4)) := by
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have h6 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 6
  have h630 := pow_le_pow_right₀ hL1 (show 6 ≤ 30 by norm_num)
  have h30 : 100 ≤ lemma23PaperL D ^ 30 := by norm_num at h6; linarith
  have hx2 : x ^ 2 ≤ 100 := by
    have h := sq_le_sq₀ (abs_nonneg x) (by norm_num : (0 : ℝ) ≤ 10) |>.mpr hx
    norm_num [_root_.sq_abs] at h
    nlinarith only [h]
  have hv2 : v ^ 2 = (lemma23PaperL D ^ 20) ^ 2 := by
    have h := congrArg (fun y : ℝ => y ^ 2) hv
    nlinarith only [h, _root_.sq_abs v]
  have he : (x ^ 2 - v ^ 2) / (4 * lemma23PaperL D ^ 30) =
      x ^ 2 / (4 * lemma23PaperL D ^ 30) - lemma23PaperL D ^ 10 / 4 := by
    rw [hv2]
    field_simp
  rw [lemma44_Omega_norm_vertical, he, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hxden : x ^ 2 / (4 * lemma23PaperL D ^ 30) ≤ 1 := by
    apply (div_le_one (by positivity : 0 < 4 * lemma23PaperL D ^ 30)).mpr
    linarith
  linarith only [hxden]

theorem lemma44_horizontal_denominator_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    (x : ℝ) {v : ℝ} (hv : |v| = lemma23PaperL D ^ 20) :
    ‖((x : ℂ) + (v : ℂ) * I)‖⁻¹ ≤ 1 := by
  have hn := Complex.abs_im_le_norm ((x : ℂ) + (v : ℂ) * I)
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero, add_zero,
    zero_add] at hn
  rw [hv] at hn
  apply inv_le_one_of_one_le₀
  exact (one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)).trans hn

theorem lemma44_horizontal_scale_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {x : ℝ} (hx : x ≤ 10) (v : ℝ) :
    ‖exp (((x : ℂ) + (v : ℂ) * I) * (Real.log (lemma44PaperGaussianScale D) : ℂ))‖ ≤
      Real.exp (18 * lemma23PaperL D ^ 9) := by
  rw [norm_exp, mul_re]
  simp only [ofReal_re, ofReal_im, mul_zero, sub_zero,
    lemma44_paper_gaussian_scale_log]
  simp only [add_re, mul_re, ofReal_re, ofReal_im, I_re, I_im, mul_zero,
    zero_mul, sub_zero, add_zero]
  apply Real.exp_le_exp.mpr
  have hL0 : 0 ≤ lemma23PaperL D := by linarith
  nlinarith only [mul_le_mul_of_nonneg_right hx (pow_nonneg hL0 9)]

theorem lemma44_Z_coarse_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {z : ℂ} (hz : Lemma44InExtendedGammaRegion D z) (hre : -1 / 2 ≤ z.re) :
    ‖lemma44ActualZtilde χ ψ z‖ ≤
      Real.exp (2 * lemma23PaperL D ^ 9 + 3 * lemma23PaperL D) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL0 : 0 ≤ lemma23PaperL D := by linarith
  have hp : 0 ≤ lemma23PaperL D ^ 9 := by positivity
  by_cases hr : 1 / 2 ≤ z.re
  · apply (lemma44ActualZtilde_norm_le_right χ ψ hD hψ hz hr).trans
    simp only [lemma23PaperP, Real.log_exp]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_nonpos_of_nonpos_of_nonneg (show 1 - 2 * z.re ≤ 0 by linarith) hp, hp, hL0]
  · apply (lemma44ActualZtilde_norm_le_left χ ψ hD hψ hz (le_of_not_ge hr)).trans
    simp only [lemma23PaperP, Real.log_exp]
    apply Real.exp_le_exp.mpr
    nlinarith only [mul_le_mul_of_nonneg_right (show 1 - 2 * z.re ≤ 2 by linarith) hp,
      mul_le_mul_of_nonneg_left (show 1 / 2 - z.re ≤ 1 by linarith) (show 0 ≤ 3 * lemma23PaperL D by linarith)]

theorem lemma44_product_horizontal_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {x v : ℝ}
    (hx : -s.re - 1 / 2 ≤ x) (hx10 : |x| ≤ 10) (hv : |v| = lemma23PaperL D ^ 20) :
    ‖lemma44ProductMellinNumerator χ ψ s (lemma44PaperGaussianScale D)
      ((x : ℂ) + (v : ℂ) * I) / ((x : ℂ) + (v : ℂ) * I)‖ ≤
      262144 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL0 : 0 ≤ lemma23PaperL D := by linarith
  let w : ℂ := (x : ℂ) + (v : ℂ) * I
  have hr : Lemma44InExtendedGammaRegion D (s + w) :=
    lemma44_truncated_shift_in_extended_gamma_region hL hs
      (by simpa [w] using hx10.trans (by norm_num : (10 : ℝ) ≤ 15))
      (by simpa [w] using hv.le)
  have hre : -1 / 2 ≤ (s + w).re := by simp [w]; linarith only [hx]
  have hp := lemma44_actual_product_local_growth χ ψ hD hψ hr hre
  have hb := lemma44_horizontal_scale_bound hL (abs_le.mp hx10).2 v
  have hg := lemma44_horizontal_gaussian_bound hL hx10 hv
  have hi := lemma44_horizontal_denominator_bound hL x hv
  have hbudget : lemma23PaperL D ^ 1038 *
      Real.exp (22 * lemma23PaperL D ^ 9 + 4 * lemma23PaperL D - lemma23PaperL D ^ 10 / 4) ≤
      lemma23PaperL D ^ (-180 : ℤ) := by
    apply le_trans _ (lemma44_horizontal_decay_budget (lemma44_log_large_at_threshold hD))
    apply mul_le_mul
      (pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (show 1038 ≤ 2000 by norm_num))
      (Real.exp_le_exp.mpr (by nlinarith only [hL0, pow_nonneg hL0 9]))
      (Real.exp_nonneg _) (pow_nonneg hL0 2000)
  change ‖lemma44ProductMellinNumerator χ ψ s (lemma44PaperGaussianScale D) w / w‖ ≤ _
  unfold lemma44ProductMellinNumerator
  simp only [norm_mul, norm_inv, div_eq_mul_inv]
  rw [norm_mul] at hp
  calc
    _ ≤ (262144 * Real.exp (4 * lemma23PaperL D + 4 * lemma23PaperL D ^ 9) * lemma23PaperL D ^ 1038) *
        Real.exp (18 * lemma23PaperL D ^ 9) *
        (Real.exp 1 * Real.exp (-(lemma23PaperL D ^ 10 / 4))) * 1 := by
      gcongr
    _ = (262144 * Real.exp 1) * (lemma23PaperL D ^ 1038 *
        Real.exp (22 * lemma23PaperL D ^ 9 + 4 * lemma23PaperL D - lemma23PaperL D ^ 10 / 4)) := by
      have he : Real.exp (22 * lemma23PaperL D ^ 9 + 4 * lemma23PaperL D - lemma23PaperL D ^ 10 / 4) =
          Real.exp (4 * lemma23PaperL D + 4 * lemma23PaperL D ^ 9) *
          Real.exp (18 * lemma23PaperL D ^ 9) * Real.exp (-(lemma23PaperL D ^ 10 / 4)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget (by positivity)

end ZhangLS.Spec
