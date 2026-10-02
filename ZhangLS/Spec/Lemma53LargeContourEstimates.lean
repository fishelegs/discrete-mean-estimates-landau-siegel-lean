import ZhangLS.Spec.Lemma53LargeRangeParameters
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-! # The three original large-x contour bounds -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

theorem lemma53_real_envelope_integral {D : ℕ} (hD : 1 < D) (x : ℝ) :
    (∫ u : ℝ, ‖lemma53OscillatoryKernel D x (u : ℂ)‖) =
      Real.sqrt Real.pi / lemma53PaperScale D *
        Real.exp (1 / (16 * lemma53PaperScale D ^ 2)) := by
  have hg := lemma53_gaussian_laplace (lemma53_scale_pos hD) (1 / 2)
  have hn : ∀ u : ℝ, ‖lemma53OscillatoryKernel D x (u : ℂ)‖ =
      (Complex.exp ((1 / 2 : ℂ) * (u : ℂ) - (lemma53PaperScale D : ℂ) ^ 2 * (u : ℂ) ^ 2)).re := by
    intro u
    rw [lemma53_oscillatory_kernel_norm_real, Complex.exp_re]
    simp [mul_re, ← ofReal_pow]
    ring
  simp_rw [hn]
  have hlin := integral_re (lemma53_gaussian_laplace_integrable (lemma53_scale_pos hD) (1 / 2))
  simp only [RCLike.re_eq_complex_re] at hlin
  rw [hlin, congrArg Complex.re hg]
  have he : (1 / 2 : ℂ) ^ 2 / (4 * (lemma53PaperScale D : ℂ) ^ 2) =
      ((1 / (16 * lemma53PaperScale D ^ 2) : ℝ) : ℂ) := by push_cast; ring
  rw [he]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, exp_ofReal_re]

theorem lemma53_large_left_tail_bound {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 1 ≤ x) :
    ‖∫ u : ℝ in Iic (lemma53LargeEndpoint x), lemma53OscillatoryKernel D x (u : ℂ)‖ ≤
      2 * Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) := by
  have ha := lemma53_large_endpoint_nonpos hx
  have hb : 0 ≤ lemma53PaperScale D ^ 2 := sq_nonneg _
  let A := Real.exp (-(lemma53PaperScale D ^ 2 * lemma53LargeEndpoint x ^ 2))
  have hi := (integrableOn_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2)
    (lemma53LargeEndpoint x)).const_mul A
  have hnorm : ∀ u ∈ Iic (lemma53LargeEndpoint x),
      ‖lemma53OscillatoryKernel D x (u : ℂ)‖ ≤ A * Real.exp ((1 / 2 : ℝ) * u) := by
    intro u hu
    have hsq : lemma53LargeEndpoint x ^ 2 ≤ u ^ 2 := by
      have hu0 : u ≤ 0 := hu.trans ha
      nlinarith [show u ≤ lemma53LargeEndpoint x from hu]
    rw [lemma53_oscillatory_kernel_norm_real]
    dsimp only [A]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hsq hb]
  have h := norm_integral_le_of_norm_le hi
    (by filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu; exact hnorm u hu)
  rw [integral_const_mul, integral_exp_mul_Iic (by norm_num : (0 : ℝ) < 1 / 2)] at h
  have he : Real.exp ((1 / 2 : ℝ) * lemma53LargeEndpoint x) ≤ 1 := by
    exact Real.exp_le_one_iff.mpr (by linarith)
  have hA : A = Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) := by
    dsimp only [A, lemma53LargeEndpoint]
    congr 1
    ring
  rw [hA] at h
  nlinarith [Real.exp_pos (-((lemma53PaperScale D * Real.log x / 100) ^ 2))]

theorem lemma53_large_vertical_bound {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {x u : ℝ} (hx : 0 < x) (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x)
    (ht : 0 ≤ lemma51PaperT0 D) (hu : lemma53LargeEndpoint x ≤ u) :
    ‖∫ v : ℝ in 0..lemma53LargeHeight D,
      lemma53OscillatoryKernel D x ((u : ℂ) + (v : ℂ) * I)‖ ≤
      (1 / lemma53PaperScale D) * Real.exp (1 + u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) := by
  have hB0 : 0 < lemma53PaperScale D := by linarith
  have hh : lemma53LargeHeight D ≤ 0 := by
    unfold lemma53LargeHeight
    exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hB0.le
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := lemma53LargeHeight D)
    (f := fun v : ℝ => lemma53OscillatoryKernel D x ((u : ℂ) + (v : ℂ) * I))
    (C := Real.exp (1 + u / 2 - lemma53PaperScale D ^ 2 * u ^ 2)) (by
      intro v hv
      have hv' := uIoc_subset_uIcc hv
      have hv0 := (lemma53_large_height_interval hB hv').2.1
      apply (lemma53_large_shifted_norm_bound hB hx hX ht hu hv').trans
      apply Real.exp_le_exp.mpr
      have hX0 : 0 ≤ lemma53LargePower x := Real.rpow_nonneg hx.le _
      nlinarith [mul_nonpos_of_nonneg_of_nonpos hX0 hv0])
  rw [sub_zero, abs_of_nonpos hh] at h
  simpa only [lemma53LargeHeight, neg_div, neg_neg, mul_comm] using h

theorem lemma53_large_left_vertical_bound {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {x : ℝ} (hx : 1 < x) (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x)
    (ht : 0 ≤ lemma51PaperT0 D) :
    ‖∫ v : ℝ in 0..lemma53LargeHeight D,
      lemma53OscillatoryKernel D x ((lemma53LargeEndpoint x : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp 1 * Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) := by
  have h := lemma53_large_vertical_bound hB (by linarith : 0 < x) hX ht le_rfl
  have ha := lemma53_large_endpoint_nonpos hx.le
  have hB0 : 0 < lemma53PaperScale D := by linarith
  have hi : 1 / lemma53PaperScale D ≤ 1 := (div_le_one hB0).mpr hB
  have he : Real.exp (1 + lemma53LargeEndpoint x / 2 -
      lemma53PaperScale D ^ 2 * lemma53LargeEndpoint x ^ 2) ≤
      Real.exp 1 * Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hh : lemma53PaperScale D ^ 2 * lemma53LargeEndpoint x ^ 2 =
        (lemma53PaperScale D * Real.log x / 100) ^ 2 := by
      unfold lemma53LargeEndpoint
      ring
    rw [hh]
    linarith
  exact h.trans ((mul_le_mul_of_nonneg_right hi (Real.exp_nonneg _)).trans (by simpa using he))

theorem lemma53_large_ray_norm_bound {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {x u : ℝ} (hx : 0 < x) (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x)
    (ht : 0 ≤ lemma51PaperT0 D) (hu : lemma53LargeEndpoint x ≤ u) :
    ‖lemma53OscillatoryKernel D x ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)‖ ≤
      Real.exp (1 - lemma53LargePower x / lemma53PaperScale D) *
        ‖lemma53OscillatoryKernel D x (u : ℂ)‖ := by
  have h := lemma53_large_shifted_norm_bound hB hx hX ht hu
    (v := lemma53LargeHeight D) (by simp)
  rw [lemma53_oscillatory_kernel_norm_real, ← Real.exp_add]
  convert h using 1
  unfold lemma53LargeHeight
  congr 1
  ring

theorem lemma53_large_ray_integrable {D : ℕ} (hD : 1 < D) (hB : 1 ≤ lemma53PaperScale D)
    {x : ℝ} (hx : 0 < x) (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x)
    (ht : 0 ≤ lemma51PaperT0 D) :
    IntegrableOn (fun u : ℝ => lemma53OscillatoryKernel D x
      ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)) (Ioi (lemma53LargeEndpoint x)) := by
  have hg := ((lemma53_oscillatory_kernel_integrable hD x).norm.const_mul
    (Real.exp (1 - lemma53LargePower x / lemma53PaperScale D))).integrableOn
      (s := Ioi (lemma53LargeEndpoint x))
  apply hg.mono'
  · apply Continuous.aestronglyMeasurable
    unfold lemma53OscillatoryKernel
    fun_prop
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact lemma53_large_ray_norm_bound hB hx hX ht hu.le

theorem lemma53_large_right_ray_bound {D : ℕ} (hD : 1 < D) (hB : 1 ≤ lemma53PaperScale D)
    {x : ℝ} (hx : 0 < x) (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x)
    (ht : 0 ≤ lemma51PaperT0 D) :
    ‖∫ u : ℝ in Ioi (lemma53LargeEndpoint x), lemma53OscillatoryKernel D x
      ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)‖ ≤
      Real.sqrt Real.pi * Real.exp 2 * Real.exp (-lemma53LargePower x / lemma53PaperScale D) := by
  have hfi := (lemma53_oscillatory_kernel_integrable hD x).norm.const_mul
    (Real.exp (1 - lemma53LargePower x / lemma53PaperScale D))
  have h := norm_integral_le_of_norm_le hfi.integrableOn
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
        exact lemma53_large_ray_norm_bound hB hx hX ht hu.le)
  apply h.trans
  apply (setIntegral_le_integral hfi (by filter_upwards [] with u; positivity)).trans
  rw [integral_const_mul, lemma53_real_envelope_integral hD x]
  have hB0 := lemma53_scale_pos hD
  have hs : Real.sqrt Real.pi / lemma53PaperScale D ≤ Real.sqrt Real.pi :=
    (div_le_self (Real.sqrt_nonneg _) hB)
  have hsq : 1 ≤ lemma53PaperScale D ^ 2 := by nlinarith
  have he : Real.exp (1 / (16 * lemma53PaperScale D ^ 2)) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_one (by positivity : 0 < 16 * lemma53PaperScale D ^ 2)).mpr
    nlinarith
  have hm := mul_le_mul hs he (Real.exp_nonneg _) (Real.sqrt_nonneg _)
  apply (mul_le_mul_of_nonneg_left hm (Real.exp_nonneg _)).trans
  apply le_of_eq
  have hh : Real.exp (1 - lemma53LargePower x / lemma53PaperScale D) =
      Real.exp 1 * Real.exp (-lemma53LargePower x / lemma53PaperScale D) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hh, show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
  ring

end ZhangLS.Spec
