import ZhangLS.Spec.Lemma54MellinAnalytic

/-! # Uniform Gaussian mass bounds for the actual first two derivatives -/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma54_real_gaussian_integral {B : ℝ} (hB : 0 < B) (q : ℝ) :
    (∫ u : ℝ, Real.exp (q * u - B ^ 2 * u ^ 2)) =
      Real.sqrt Real.pi / B * Real.exp (q ^ 2 / (4 * B ^ 2)) := by
  have hg := lemma53_gaussian_laplace hB (q : ℂ)
  have hn (u : ℝ) : Real.exp (q * u - B ^ 2 * u ^ 2) =
      (Complex.exp ((q : ℂ) * (u : ℂ) - (B : ℂ) ^ 2 * (u : ℂ) ^ 2)).re := by
    simp [Complex.exp_re, mul_re, ← ofReal_pow]
  simp_rw [hn]
  have hlin := integral_re (lemma53_gaussian_laplace_integrable hB (q : ℂ))
  simp only [RCLike.re_eq_complex_re] at hlin
  rw [hlin, congrArg Complex.re hg]
  have he : (q : ℂ) ^ 2 / (4 * (B : ℂ) ^ 2) = ((q ^ 2 / (4 * B ^ 2) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [he]
  simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, exp_ofReal_re]

theorem lemma54_first_majorant_integral_bound {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) :
    (∫ u : ℝ, lemma54FirstMajorant D u) ≤
      4 * Real.pi * Real.sqrt Real.pi * Real.exp 1 / lemma53PaperScale D := by
  have hB0 := lemma53_scale_pos hD
  have hs : 1 ≤ lemma53PaperScale D ^ 2 := by nlinarith
  have h1 : Real.exp ((3 / 2 : ℝ) ^ 2 / (4 * lemma53PaperScale D ^ 2)) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * lemma53PaperScale D ^ 2)).mpr
    nlinarith
  have h2 : Real.exp ((1 / 2 : ℝ) ^ 2 / (4 * lemma53PaperScale D ^ 2)) ≤ Real.exp 1 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * lemma53PaperScale D ^ 2)).mpr
    nlinarith
  unfold lemma54FirstMajorant
  rw [integral_const_mul, integral_add
    (lemma54_real_gaussian_integrable hB0 (3 / 2))
    (lemma54_real_gaussian_integrable hB0 (1 / 2)),
    lemma54_real_gaussian_integral hB0, lemma54_real_gaussian_integral hB0]
  have hmul := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (show 0 ≤ 2 * Real.pi * (Real.sqrt Real.pi / lemma53PaperScale D) by positivity)
  convert hmul using 1 <;> ring

theorem lemma54_second_majorant_integral_bound {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) :
    (∫ u : ℝ, lemma54SecondMajorant D u) ≤
      16 * Real.pi ^ 2 * Real.sqrt Real.pi * Real.exp 2 / lemma53PaperScale D := by
  have hB0 := lemma53_scale_pos hD
  have hs : 1 ≤ lemma53PaperScale D ^ 2 := by nlinarith
  have h1 : Real.exp ((5 / 2 : ℝ) ^ 2 / (4 * lemma53PaperScale D ^ 2)) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * lemma53PaperScale D ^ 2)).mpr
    nlinarith
  have h2 : Real.exp ((1 / 2 : ℝ) ^ 2 / (4 * lemma53PaperScale D ^ 2)) ≤ Real.exp 2 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * lemma53PaperScale D ^ 2)).mpr
    nlinarith
  unfold lemma54SecondMajorant
  rw [integral_const_mul, integral_add
    (lemma54_real_gaussian_integrable hB0 (5 / 2))
    (lemma54_real_gaussian_integrable hB0 (1 / 2)),
    lemma54_real_gaussian_integral hB0, lemma54_real_gaussian_integral hB0]
  have hmul := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (show 0 ≤ 8 * Real.pi ^ 2 * (Real.sqrt Real.pi / lemma53PaperScale D) by positivity)
  convert hmul using 1 <;> ring

theorem lemma54_first_integral_norm_bound {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) (x : ℝ) :
    ‖lemma54FirstIntegral D x‖ ≤
      4 * Real.pi * Real.sqrt Real.pi * Real.exp 1 / lemma53PaperScale D := by
  apply (norm_integral_le_of_norm_le (lemma54_first_majorant_integrable hD)
    (Filter.Eventually.of_forall (lemma54_first_kernel_norm_bound D x))).trans
  exact lemma54_first_majorant_integral_bound hD hB

theorem lemma54_second_integral_norm_bound {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) (x : ℝ) :
    ‖lemma54SecondIntegral D x‖ ≤
      16 * Real.pi ^ 2 * Real.sqrt Real.pi * Real.exp 2 / lemma53PaperScale D := by
  apply (norm_integral_le_of_norm_le (lemma54_second_majorant_integrable hD)
    (Filter.Eventually.of_forall (lemma54_second_kernel_norm_bound D x))).trans
  exact lemma54_second_majorant_integral_bound hD hB

theorem lemma54_actual_first_deriv_norm_bound {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) {x : ℝ} (hx : 0 < x) :
    ‖deriv (lemma53PaperDelta D) x‖ ≤
      4 * Real.pi * Real.sqrt Real.pi * Real.exp 1 / lemma53PaperScale D := by
  rw [lemma54_actual_delta_deriv hD hx]
  exact lemma54_first_integral_norm_bound hD hB x

theorem lemma54_actual_second_deriv_norm_bound {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) {x : ℝ} (hx : 0 < x) :
    ‖deriv (deriv (lemma53PaperDelta D)) x‖ ≤
      16 * Real.pi ^ 2 * Real.sqrt Real.pi * Real.exp 2 / lemma53PaperScale D := by
  rw [lemma54_actual_delta_second_deriv hD hx]
  exact lemma54_second_integral_norm_bound hD hB x

end ZhangLS.Spec
