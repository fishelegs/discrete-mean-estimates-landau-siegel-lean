import ZhangLS.Spec.Lemma54WeightedKernels

/-! # Actual weighted kernels through order eight

This extends the existing genuine oscillatory derivative kernels, not the
Mellin target as an assumption. Uniform constants and all contour branches
are retained explicitly. The eighth-order Mellin estimate is a later step.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Topology

noncomputable def lemma54EighthConstant : ℝ := (4*Real.pi)^8

noncomputable def lemma54EighthMajorant (D : ℕ) (u : ℝ) : ℝ :=
  lemma54EighthConstant *
    (Real.exp ((17/2:ℝ)*u-lemma53PaperScale D^2*u^2) +
      Real.exp ((1/2:ℝ)*u-lemma53PaperScale D^2*u^2))

theorem lemma54_eighth_weighted_constant_pos : 0<lemma54EighthConstant := by
  unfold lemma54EighthConstant
  positivity

/-- The eighth-power envelope is valid for every intermediate derivative,
including the zeroth. No nonunit or small-x restriction enters this bound. -/
theorem lemma54_eighth_contour_factor_pow_bound {n : ℕ} (hn : n≤8) (u v : ℝ) :
    ‖lemma54ContourFactor ((u:ℂ)+(v:ℂ)*I)‖^n ≤
      lemma54EighthConstant*(Real.exp (8*u)+1) := by
  have hf := lemma54_contour_factor_norm_bound u v
  have hc : (1:ℝ)≤4*Real.pi := by linarith [Real.two_le_pi]
  have hcp : 0≤4*Real.pi := by positivity
  by_cases hu : 0≤u
  · have he : 1≤Real.exp u := Real.one_le_exp hu
    have hbound : ‖lemma54ContourFactor ((u:ℂ)+(v:ℂ)*I)‖ ≤ 4*Real.pi*Real.exp u := by
      nlinarith [Real.pi_pos]
    have hbase : 1≤4*Real.pi*Real.exp u := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) (sub_nonneg.mpr he)]
    have hp := (pow_le_pow_left₀ (norm_nonneg _) hbound n).trans (pow_le_pow_right₀ hbase hn)
    have hexp : (Real.exp u)^8 = Real.exp (8*u) := by rw [← Real.exp_nat_mul]; norm_num
    rw [mul_pow,hexp] at hp
    change _ ≤ (4*Real.pi)^8*(Real.exp (8*u)+1)
    nlinarith [pow_nonneg hcp 8]
  · have he : Real.exp u≤1 := Real.exp_le_one_iff.mpr (le_of_not_ge hu)
    have hbound : ‖lemma54ContourFactor ((u:ℂ)+(v:ℂ)*I)‖ ≤ 4*Real.pi := by
      nlinarith [Real.pi_pos]
    have hp := (pow_le_pow_left₀ (norm_nonneg _) hbound n).trans (pow_le_pow_right₀ hc hn)
    change _ ≤ (4*Real.pi)^8*(Real.exp (8*u)+1)
    nlinarith [mul_nonneg (pow_nonneg hcp 8) (Real.exp_nonneg (8*u))]

theorem lemma54_eighth_weighted_majorant_factorization (D : ℕ) (u : ℝ) :
    lemma54EighthConstant * (Real.exp (8 * u) + 1) *
      Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) = lemma54EighthMajorant D u := by
  unfold lemma54EighthMajorant
  have h1 : Real.exp (8 * u) * Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) =
      Real.exp ((17 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (u / 2 - lemma53PaperScale D ^ 2 * u ^ 2) =
      Real.exp ((1 / 2 : ℝ) * u - lemma53PaperScale D ^ 2 * u ^ 2) := by congr 1; ring
  rw [mul_assoc, add_mul, one_mul, h1, h2]

theorem lemma54_eighth_weighted_majorant_integrable {D : ℕ} (hD : 1 < D) :
    Integrable (lemma54EighthMajorant D) :=
  ((lemma54_real_gaussian_integrable (lemma53_scale_pos hD) (17 / 2)).add
    (lemma54_real_gaussian_integrable (lemma53_scale_pos hD) (1 / 2))).const_mul _

theorem lemma54_eighth_weighted_kernel_norm_real {n : ℕ} (hn : n ≤ 8) (D : ℕ) (x u : ℝ) :
    ‖lemma54WeightedKernel D x n (u : ℂ)‖ ≤ lemma54EighthMajorant D u := by
  have hf := lemma54_eighth_contour_factor_pow_bound hn u 0
  simp only [ofReal_zero, zero_mul, add_zero] at hf
  unfold lemma54WeightedKernel
  rw [norm_mul, norm_pow, lemma53_oscillatory_kernel_norm_real]
  rw [← lemma54_eighth_weighted_majorant_factorization]
  exact mul_le_mul_of_nonneg_right hf (Real.exp_nonneg _)

theorem lemma54_eighth_weighted_kernel_integrable {D : ℕ} (hD : 1 < D) {n : ℕ}
    (hn : n ≤ 8) (x : ℝ) : Integrable (fun u : ℝ => lemma54WeightedKernel D x n (u : ℂ)) := by
  apply (lemma54_eighth_weighted_majorant_integrable hD).mono'
  · exact ((lemma54_weighted_kernel_differentiable D x n).continuous.comp
      continuous_ofReal).aestronglyMeasurable
  · exact Eventually.of_forall (lemma54_eighth_weighted_kernel_norm_real hn D x)

theorem lemma54_eighth_weighted_majorant_integral_bound {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) :
    (∫ u : ℝ, lemma54EighthMajorant D u) ≤
      2 * lemma54EighthConstant * Real.sqrt Real.pi * Real.exp 19 / lemma53PaperScale D := by
  have hB0 := lemma53_scale_pos hD
  have hs : 1 ≤ lemma53PaperScale D ^ 2 := by nlinarith
  have h1 : Real.exp ((17 / 2 : ℝ) ^ 2 / (4 * lemma53PaperScale D ^ 2)) ≤ Real.exp 19 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * lemma53PaperScale D ^ 2)).mpr
    nlinarith
  have h2 : Real.exp ((1 / 2 : ℝ) ^ 2 / (4 * lemma53PaperScale D ^ 2)) ≤ Real.exp 19 := by
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * lemma53PaperScale D ^ 2)).mpr
    nlinarith
  unfold lemma54EighthMajorant
  rw [integral_const_mul, integral_add
    (lemma54_real_gaussian_integrable hB0 (17 / 2)) (lemma54_real_gaussian_integrable hB0 (1 / 2)),
    lemma54_real_gaussian_integral hB0, lemma54_real_gaussian_integral hB0]
  have hm := mul_le_mul_of_nonneg_left (add_le_add h1 h2)
    (show 0 ≤ lemma54EighthConstant * (Real.sqrt Real.pi / lemma53PaperScale D) by
      exact mul_nonneg lemma54_eighth_weighted_constant_pos.le (by positivity))
  convert hm using 1 <;> ring

theorem lemma54_eighth_weighted_ray_norm_bound {D : ℕ} (hB : 1 ≤ lemma53PaperScale D)
    {n : ℕ} (hn : n ≤ 8) {x u : ℝ} (hx : 0 < x)
    (hX : 4 * lemma51PaperT0 D ≤ lemma53LargePower x) (ht : 0 ≤ lemma51PaperT0 D)
    (hu : lemma53LargeEndpoint x ≤ u) :
    ‖lemma54WeightedKernel D x n ((u : ℂ) + (lemma53LargeHeight D : ℂ) * I)‖ ≤
      Real.exp (1 - lemma53LargePower x / lemma53PaperScale D) * lemma54EighthMajorant D u := by
  have hk := lemma53_large_ray_norm_bound hB hx hX ht hu
  have hf := lemma54_eighth_contour_factor_pow_bound hn u (lemma53LargeHeight D)
  unfold lemma54WeightedKernel
  rw [norm_mul, norm_pow]
  apply (mul_le_mul hf hk (norm_nonneg _)
    (mul_nonneg lemma54_eighth_weighted_constant_pos.le (by positivity))).trans
  apply le_of_eq
  rw [lemma53_oscillatory_kernel_norm_real, ← lemma54_eighth_weighted_majorant_factorization]
  ring

end ZhangLS.Spec
