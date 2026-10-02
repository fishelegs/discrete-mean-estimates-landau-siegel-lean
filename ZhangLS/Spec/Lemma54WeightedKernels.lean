import ZhangLS.Spec.Lemma54DerivativeBounds

/-! # Entire weighted kernels and common Gaussian bounds for both derivatives -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

noncomputable def lemma54ContourFactor (w : ℂ) : ℂ :=
  -(2 * Real.pi : ℂ) * I * (Complex.exp w - 1)

noncomputable def lemma54WeightedKernel (D : ℕ) (x : ℝ) (n : ℕ) (w : ℂ) : ℂ :=
  lemma54ContourFactor w ^ n * lemma53OscillatoryKernel D x w

noncomputable def lemma54WeightedConstant : ℝ := 1 + 8 * Real.pi ^ 2

noncomputable def lemma54WeightedMajorant (D : ℕ) (u : ℝ) : ℝ :=
  lemma54WeightedConstant *
    (Real.exp ((5 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) +
      Real.exp ((1 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2))

theorem lemma54_weighted_constant_pos : 0 < lemma54WeightedConstant := by
  unfold lemma54WeightedConstant
  positivity

theorem lemma54_weighted_kernel_differentiable (D : ℕ) (x : ℝ) (n : ℕ) :
    Differentiable ℂ (lemma54WeightedKernel D x n) := by
  unfold lemma54WeightedKernel lemma54ContourFactor lemma53OscillatoryKernel
  fun_prop

theorem lemma54_weighted_kernel_one_real (D : ℕ) (x u : ℝ) :
    lemma54WeightedKernel D x 1 (u : ℂ) = lemma54FirstKernel D x u := by
  simp only [lemma54WeightedKernel, lemma54ContourFactor, lemma54FirstKernel,
    lemma54DerivativeFactor, pow_one, Complex.ofReal_exp]

theorem lemma54_weighted_kernel_two_real (D : ℕ) (x u : ℝ) :
    lemma54WeightedKernel D x 2 (u : ℂ) = lemma54SecondKernel D x u := by
  simp only [lemma54WeightedKernel, lemma54ContourFactor, lemma54SecondKernel,
    lemma54DerivativeFactor, Complex.ofReal_exp]

theorem lemma54_contour_factor_norm_bound (u v : ℝ) :
    ‖lemma54ContourFactor ((u : ℂ) + (v : ℂ) * I)‖ ≤
      2 * Real.pi * (Real.exp u + 1) := by
  have he : ‖Complex.exp ((u : ℂ) + (v : ℂ) * I)‖ = Real.exp u := by
    rw [norm_exp]
    simp
  unfold lemma54ContourFactor
  rw [norm_mul, norm_mul, norm_neg, norm_I, mul_one]
  have hn : ‖(2 * Real.pi : ℂ)‖ = 2 * Real.pi := by
    simp [norm_mul, norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hn]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [he, norm_one] using norm_sub_le (Complex.exp ((u : ℂ) + (v : ℂ) * I)) 1

theorem lemma54_contour_factor_pow_bound {n : ℕ} (hn : n ≤ 2) (u v : ℝ) :
    ‖lemma54ContourFactor ((u : ℂ) + (v : ℂ) * I)‖ ^ n ≤
      lemma54WeightedConstant * (Real.exp (2 * u) + 1) := by
  have hf := lemma54_contour_factor_norm_bound u v
  have hsq : ‖lemma54ContourFactor ((u : ℂ) + (v : ℂ) * I)‖ ^ 2 ≤
      8 * Real.pi ^ 2 * (Real.exp (2 * u) + 1) := by
    have hs := pow_le_pow_left₀ (norm_nonneg _) hf 2
    have he : Real.exp (2 * u) = Real.exp u ^ 2 := by
      rw [two_mul, Real.exp_add, pow_two]
    rw [he]
    nlinarith [mul_nonneg (sq_nonneg Real.pi) (sq_nonneg (Real.exp u - 1))]
  have hp : ‖lemma54ContourFactor ((u : ℂ) + (v : ℂ) * I)‖ ^ n ≤
      ‖lemma54ContourFactor ((u : ℂ) + (v : ℂ) * I)‖ ^ 2 + 1 := by
    interval_cases n
    · simp only [pow_zero]
      nlinarith [sq_nonneg ‖lemma54ContourFactor ((u : ℂ) + (v : ℂ) * I)‖]
    · simp only [pow_one]
      nlinarith [sq_nonneg (‖lemma54ContourFactor ((u : ℂ) + (v : ℂ) * I)‖ - 1 / 2)]
    · linarith
  apply hp.trans
  unfold lemma54WeightedConstant
  nlinarith only [hsq, Real.exp_nonneg (2 * u)]

theorem lemma54_weighted_majorant_factorization (D : ℕ) (u : ℝ) :
    lemma54WeightedConstant * (Real.exp (2 * u) + 1) *
      Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) = lemma54WeightedMajorant D u := by
  unfold lemma54WeightedMajorant
  have h1 : Real.exp (2 * u) * Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) =
      Real.exp ((5 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) =
      Real.exp ((1 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) := by congr 1; ring
  rw [mul_assoc, add_mul, one_mul, h1, h2]

theorem lemma54_weighted_majorant_integrable {D : ℕ} (hD : 1 < D) :
    Integrable (lemma54WeightedMajorant D) :=
  ((lemma54_real_gaussian_integrable (lemma53_scale_pos hD) (5 / 2)).add
    (lemma54_real_gaussian_integrable (lemma53_scale_pos hD) (1 / 2))).const_mul _

theorem lemma54_weighted_kernel_norm_real {n : ℕ} (hn : n ≤ 2) (D : ℕ) (x u : ℝ) :
    ‖lemma54WeightedKernel D x n (u : ℂ)‖ ≤ lemma54WeightedMajorant D u := by
  have hf := lemma54_contour_factor_pow_bound hn u 0
  simp only [ofReal_zero, zero_mul, add_zero] at hf
  unfold lemma54WeightedKernel
  rw [norm_mul, norm_pow, lemma53_oscillatory_kernel_norm_real]
  rw [← lemma54_weighted_majorant_factorization]
  exact mul_le_mul_of_nonneg_right hf (Real.exp_nonneg _)

theorem lemma54_weighted_kernel_integrable {D : ℕ} (hD : 1 < D) {n : ℕ}
    (hn : n ≤ 2) (x : ℝ) : Integrable (fun u : ℝ => lemma54WeightedKernel D x n (u : ℂ)) := by
  apply (lemma54_weighted_majorant_integrable hD).mono'
  · exact ((lemma54_weighted_kernel_differentiable D x n).continuous.comp
      continuous_ofReal).aestronglyMeasurable
  · exact Eventually.of_forall (lemma54_weighted_kernel_norm_real hn D x)

theorem lemma54_weighted_majorant_integral_bound {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) :
    (∫ u : ℝ, lemma54WeightedMajorant D u) ≤
      2 * lemma54WeightedConstant * Real.sqrt Real.pi * Real.exp 2 / lemma53PaperScale D := by
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
  unfold lemma54WeightedMajorant
  rw [integral_const_mul, integral_add
    (lemma54_real_gaussian_integrable hB0 (5 / 2)) (lemma54_real_gaussian_integrable hB0 (1 / 2)),
    lemma54_real_gaussian_integral hB0, lemma54_real_gaussian_integral hB0]
  have hm := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (show 0 ≤ lemma54WeightedConstant * (Real.sqrt Real.pi / lemma53PaperScale D) by
      exact mul_nonneg lemma54_weighted_constant_pos.le (by positivity))
  convert hm using 1 <;> ring

theorem lemma54_weighted_ray_norm_bound {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {n : ℕ} (hn : n ≤ 2) {x u : ℝ} (hx : 0 < x)
    (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x) (ht : 0 ≤ lemma51PaperT0 D)
    (hu : lemma53LargeEndpoint x ≤ u) :
    ‖lemma54WeightedKernel D x n ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)‖ ≤
      Real.exp (1 - lemma53LargePower x / lemma53PaperScale D) * lemma54WeightedMajorant D u := by
  have hk := lemma53_large_ray_norm_bound hB hx hX ht hu
  have hf := lemma54_contour_factor_pow_bound hn u (lemma53LargeHeight D)
  unfold lemma54WeightedKernel
  rw [norm_mul, norm_pow]
  apply (mul_le_mul hf hk (norm_nonneg _)
    (mul_nonneg lemma54_weighted_constant_pos.le (by positivity))).trans
  apply le_of_eq
  rw [lemma53_oscillatory_kernel_norm_real, ← lemma54_weighted_majorant_factorization]
  ring

end ZhangLS.Spec
