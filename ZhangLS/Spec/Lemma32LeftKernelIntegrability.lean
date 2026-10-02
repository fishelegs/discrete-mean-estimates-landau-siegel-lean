import ZhangLS.Spec.Lemma32LeftKernelContinuity
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_left_kernel_high_bound (t : ℝ) (ht : 1 ≤ |t|) :
    lemma32LeftKernel t ≤ (8^8*3^8*(1+((20 : ℕ).factorial : ℝ)))/|t|^4 := by
  have hz := lemma32_actual_zeta_strip_high_growth (1+lemma32LeftLine t)
    (by norm_num [lemma32LeftLine,mul_re]) (by norm_num [lemma32LeftLine,mul_re])
    (by simpa [lemma32LeftLine] using ht)
  have hn := lemma32_positive_strip_high_norm (1+lemma32LeftLine t)
    (by norm_num [lemma32LeftLine,mul_re]) (by norm_num [lemma32LeftLine,mul_re])
    (by simpa [lemma32LeftLine] using ht)
  have ht0 : t ≠ 0 := by intro h;rw [h,abs_zero] at ht;linarith
  have hg := lemma32_gamma_strip_polynomial_decay (lemma32LeftLine t)
    (by norm_num [lemma32LeftLine,mul_re]) (by norm_num [lemma32LeftLine,mul_re])
    (by simpa [lemma32LeftLine] using ht0) 20 (by norm_num)
  simp only [lemma32LeftLine,add_im,ofReal_im,mul_im,I_im,I_re,ofReal_re,
    mul_one,mul_zero,add_zero,zero_add,one_im] at hz hn hg
  unfold lemma32LeftKernel
  calc
    _ ≤ (8*|t|)^8*(3*|t|)^8*((1+((20 : ℕ).factorial : ℝ))/|t|^20) := by
      exact mul_le_mul
        (mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hz 8)
          (pow_le_pow_left₀ (norm_nonneg _) hn 8) (by positivity) (by positivity))
        hg (norm_nonneg _) (by positivity)
    _ = _ := by
      have hp : |t| ≠ 0 := (abs_pos.mpr ht0).ne'
      field_simp

lemma lemma32_left_kernel_integrable : Integrable lemma32LeftKernel := by
  have hi : Integrable (fun t : ℝ => (lemma32LeftKernel t : ℂ)) := by
    apply lemma32_integrable_of_quartic_decay _
      (Complex.continuous_ofReal.comp lemma32_left_kernel_continuous)
      (8^8*3^8*(1+((20 : ℕ).factorial : ℝ))) (by positivity)
    intro t ht
    change ‖(lemma32LeftKernel t : ℂ)‖ ≤ _
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (lemma32_left_kernel_nonneg t)]
      using lemma32_left_kernel_high_bound t ht
  simpa only [RCLike.re_to_complex,Complex.ofReal_re] using hi.re

noncomputable def lemma32LeftKernelConstant : ℝ := 1+∫ t : ℝ, lemma32LeftKernel t

lemma lemma32_left_kernel_constant_pos : 0 < lemma32LeftKernelConstant := by
  have hi : 0 ≤ ∫ t : ℝ, lemma32LeftKernel t := integral_nonneg lemma32_left_kernel_nonneg
  unfold lemma32LeftKernelConstant
  linarith

lemma lemma32_left_kernel_integral_le : (∫ t : ℝ, lemma32LeftKernel t) ≤ lemma32LeftKernelConstant := by
  unfold lemma32LeftKernelConstant
  linarith

end ZhangLS.Spec
