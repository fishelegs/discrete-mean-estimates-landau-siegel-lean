import ZhangLS.Spec.Lemma57GaussianMellinTransform

/-! The genuine positive logarithmic Gaussian weight and sharp scalar errors. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open MeasureTheory Set Filter
open scoped Topology

noncomputable def lemma171LogGaussianWeight (D : ℕ) (x : ℝ) : ℝ :=
  Real.log x * zhangGaussianWeight D x +
    Real.exp (-(zhangGaussianEndpoint D x) ^ 2) /
      (2 * Real.sqrt Real.pi * lemma57GaussianLogScale D)

lemma lemma171_log_gaussian_weight_exp (D : ℕ) (y : ℝ) :
    lemma171LogGaussianWeight D (Real.exp y) =
      y * zhangGaussianWeight D (Real.exp y) +
        Real.exp (-(lemma57GaussianLogScale D * y) ^ 2) /
          (2 * Real.sqrt Real.pi * lemma57GaussianLogScale D) := by
  simp [lemma171LogGaussianWeight, zhangGaussianEndpoint, lemma57GaussianLogScale]

lemma lemma171_gaussian_first_tail_integral (u : ℝ) :
    (∫ t : ℝ in Ioi u, t * Real.exp (-(t ^ 2))) = Real.exp (-(u ^ 2)) / 2 := by
  have hd (t : ℝ) : HasDerivAt (fun t : ℝ => -Real.exp (-(t ^ 2)) / 2)
      (t * Real.exp (-(t ^ 2))) t := by
    convert (((((hasDerivAt_id t).pow 2).neg).exp).neg.div_const 2) using 1 <;>
      simp only [Pi.neg_apply, Pi.pow_apply, id_eq] <;> ring
  have hi : Integrable (fun t : ℝ => t * Real.exp (-(t ^ 2))) := by
    simpa using integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)
  have hp : Tendsto (fun t : ℝ => t ^ 2) atTop atTop :=
    tendsto_pow_atTop (by norm_num)
  have he : Tendsto (fun t : ℝ => Real.exp (-(t ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hp)
  have hlim : Tendsto (fun t : ℝ => -Real.exp (-(t ^ 2)) / 2) atTop (𝓝 0) := by
    simpa using he.neg.div_const 2
  have h := integral_Ioi_of_hasDerivAt_of_tendsto' (a := u) (fun t _ => hd t) hi.integrableOn hlim
  simpa only [zero_sub, neg_div, neg_neg] using h

/-- Mills' inequality in a division-free form, including the endpoint u=0. -/
lemma lemma171_gaussian_mills_bound (u : ℝ) :
    u * (∫ t : ℝ in Ioi u, Real.exp (-(t ^ 2))) ≤ Real.exp (-(u ^ 2)) / 2 := by
  have hg : IntegrableOn (fun t : ℝ => Real.exp (-(t ^ 2))) (Ioi u) := by
    simpa using (integrable_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn
  have ht : IntegrableOn (fun t : ℝ => t * Real.exp (-(t ^ 2))) (Ioi u) := by
    simpa using (integrable_mul_exp_neg_mul_sq (by norm_num : (0 : ℝ) < 1)).integrableOn
  rw [← integral_const_mul, ← lemma171_gaussian_first_tail_integral u]
  apply setIntegral_mono_ae_restrict (hg.const_mul u) ht
  refine ae_restrict_of_forall_mem measurableSet_Ioi ?_
  intro t ht
  exact mul_le_mul_of_nonneg_right ht.le (Real.exp_pos _).le

lemma lemma171_log_gaussian_nonneg_of_log_nonpos {D : ℕ} (hD : 1 < D)
    (y : ℝ) (hy : y ≤ 0) : 0 ≤ lemma171LogGaussianWeight D (Real.exp y) := by
  let c := lemma57GaussianLogScale D
  let q := Real.sqrt Real.pi
  have hc : 0 < c := pow_pos (Real.log_pos (by exact_mod_cast hD)) 15
  have hq : 0 < q := Real.sqrt_pos.mpr Real.pi_pos
  have he : zhangGaussianEndpoint D (Real.exp y) = c * y := by
    simp [zhangGaussianEndpoint, c, lemma57GaussianLogScale]
  have hw := zhangGaussianWeight_eq_tail_of_endpoint_nonpos
    (D := D) (x := Real.exp y) (by rw [he]; exact mul_nonpos_of_nonneg_of_nonpos hc.le hy)
  rw [he] at hw
  have hm := lemma171_gaussian_mills_bound (-c * y)
  simp only [neg_mul, neg_sq] at hm
  rw [lemma171_log_gaussian_weight_exp, hw]
  change 0 ≤ y * (q⁻¹ * ∫ t : ℝ in Ioi (-(c * y)), Real.exp (-(t ^ 2))) +
    Real.exp (-(c * y) ^ 2) / (2 * q * c)
  apply (mul_nonneg_iff_of_pos_right (by positivity : 0 < 2 * q * c)).mp
  have heq : (y * (q⁻¹ * ∫ t : ℝ in Ioi (-(c * y)), Real.exp (-(t ^ 2))) +
      Real.exp (-(c * y) ^ 2) / (2 * q * c)) * (2 * q * c) =
      2 * c * y * (∫ t : ℝ in Ioi (-(c * y)), Real.exp (-(t ^ 2))) +
        Real.exp (-(c * y) ^ 2) := by
    field_simp [hc.ne', hq.ne']
    <;> ring
  rw [heq]
  nlinarith only [hm]

lemma lemma171_log_gaussian_reflection (D : ℕ) (y : ℝ) :
    lemma171LogGaussianWeight D (Real.exp y) - y =
      lemma171LogGaussianWeight D (Real.exp (-y)) := by
  rw [lemma171_log_gaussian_weight_exp, lemma171_log_gaussian_weight_exp]
  have hw := zhangGaussianWeight_exp_add_neg (D := D) y
  simp only [mul_neg, neg_sq]
  linear_combination y * hw

lemma lemma171_log_gaussian_nonneg {D : ℕ} (hD : 1 < D) (y : ℝ) :
    0 ≤ lemma171LogGaussianWeight D (Real.exp y) := by
  by_cases hy : y ≤ 0
  · exact lemma171_log_gaussian_nonneg_of_log_nonpos hD y hy
  · rw [lemma171_log_gaussian_weight_exp]
    have hy0 : 0 ≤ y := (lt_of_not_ge hy).le
    have hc : 0 < lemma57GaussianLogScale D :=
      pow_pos (Real.log_pos (by exact_mod_cast hD)) 15
    have hg := zhangGaussianWeight_nonneg hD (Real.exp_pos y)
    exact add_nonneg (mul_nonneg hy0 hg) (div_nonneg (Real.exp_pos _).le (by positivity))

lemma lemma171_log_gaussian_error {D : ℕ} (hD : 1 < D) (y : ℝ) :
    0 ≤ lemma171LogGaussianWeight D (Real.exp y) - max y 0 ∧
    lemma171LogGaussianWeight D (Real.exp y) - max y 0 ≤
      Real.exp (-(lemma57GaussianLogScale D * y) ^ 2) /
        (2 * Real.sqrt Real.pi * lemma57GaussianLogScale D) := by
  have hneg (v : ℝ) (hv : v ≤ 0) :
      lemma171LogGaussianWeight D (Real.exp v) ≤
        Real.exp (-(lemma57GaussianLogScale D * v) ^ 2) /
          (2 * Real.sqrt Real.pi * lemma57GaussianLogScale D) := by
    rw [lemma171_log_gaussian_weight_exp]
    have hg := zhangGaussianWeight_nonneg hD (Real.exp_pos v)
    nlinarith
  by_cases hy : 0 ≤ y
  · rw [max_eq_left hy, lemma171_log_gaussian_reflection]
    refine ⟨lemma171_log_gaussian_nonneg hD (-y), ?_⟩
    simpa only [mul_neg, neg_sq] using hneg (-y) (by linarith)
  · rw [max_eq_right (le_of_not_ge hy), sub_zero]
    exact ⟨lemma171_log_gaussian_nonneg hD y, hneg y (le_of_not_ge hy)⟩

end ZhangLS.Spec
