import ZhangLS.Spec.Lemma54WeightedContour

/-! # Actual derivative decay, Mellin convergence and endpoint products -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000

theorem lemma54_scale_ge_one {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    1 ≤ lemma53PaperScale D := by
  unfold lemma53PaperScale
  exact one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)

theorem lemma54_isBigO_atTop_of_derivative_tail {D : ℕ} (hD : 1 < D)
    {f : ℝ → ℂ}
    (hf : ∀ x : ℝ, 0 < x → lemma51PaperT0 D ^ (51 / 50 : ℝ) < x →
      ‖f x‖ ≤ lemma54DerivativeTail D x) {a : ℝ} (ha : 0 < a) :
    f =O[atTop] (fun x : ℝ => x ^ (-a)) := by
  apply IsBigO.of_bound (lemma54WeightedConstant * (4 + 2 * Real.exp 1) +
    2 * lemma54WeightedConstant * Real.sqrt Real.pi * Real.exp 3)
  filter_upwards [lemma54_log_gaussian_le_rpow_eventually (lemma53_scale_pos hD) ha,
    lemma54_stretched_exp_le_rpow_eventually (lemma53_scale_pos hD) ha,
    eventually_gt_atTop (lemma51PaperT0 D ^ (51 / 50 : ℝ)),
    eventually_gt_atTop (0 : ℝ)] with x hfirst hsecond hxhi hx
  have he := hf x hx hxhi
  have h1 := mul_le_mul_of_nonneg_left hfirst
    (show 0 ≤ lemma54WeightedConstant * (4 + 2 * Real.exp 1) by
      exact mul_nonneg lemma54_weighted_constant_pos.le (by positivity))
  have h2 := mul_le_mul_of_nonneg_left hsecond
    (show 0 ≤ 2 * lemma54WeightedConstant * Real.sqrt Real.pi * Real.exp 3 by
      exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) lemma54_weighted_constant_pos.le)
        (Real.sqrt_nonneg _)) (Real.exp_nonneg _))
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le _)]
  unfold lemma54DerivativeTail at he
  nlinarith only [he, h1, h2]

theorem lemma54_actual_first_deriv_isBigO_atTop {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {a : ℝ} (ha : 0 < a) :
    deriv (lemma53PaperDelta D) =O[atTop] (fun x : ℝ => x ^ (-a)) :=
  lemma54_isBigO_atTop_of_derivative_tail hD
    (fun _ hx hxhi => lemma54_actual_first_deriv_large_range hD hL hx hxhi) ha

theorem lemma54_actual_second_deriv_isBigO_atTop {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {a : ℝ} (ha : 0 < a) :
    deriv (deriv (lemma53PaperDelta D)) =O[atTop] (fun x : ℝ => x ^ (-a)) :=
  lemma54_isBigO_atTop_of_derivative_tail hD
    (fun _ hx hxhi => lemma54_actual_second_deriv_large_range hD hL hx hxhi) ha

theorem lemma54_actual_first_deriv_isBigO_at_zero {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) :
    deriv (lemma53PaperDelta D) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  apply IsBigO.of_bound (4 * Real.pi * Real.sqrt Real.pi * Real.exp 1 / lemma53PaperScale D)
  filter_upwards [show ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x from self_mem_nhdsWithin] with x hx
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using
    lemma54_actual_first_deriv_norm_bound hD hB hx

theorem lemma54_actual_second_deriv_isBigO_at_zero {D : ℕ} (hD : 1 < D)
    (hB : 1 ≤ lemma53PaperScale D) :
    deriv (deriv (lemma53PaperDelta D)) =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(0 : ℝ))) := by
  apply IsBigO.of_bound (16 * Real.pi ^ 2 * Real.sqrt Real.pi * Real.exp 2 / lemma53PaperScale D)
  filter_upwards [show ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x from self_mem_nhdsWithin] with x hx
  simpa only [neg_zero, Real.rpow_zero, norm_one, mul_one] using
    lemma54_actual_second_deriv_norm_bound hD hB hx

theorem lemma54_actual_first_deriv_continuousOn {D : ℕ} (hD : 1 < D) :
    ContinuousOn (deriv (lemma53PaperDelta D)) (Ioi 0) := by
  intro x hx
  exact (lemma54_actual_delta_deriv_hasDerivAt hD hx).continuousAt.continuousWithinAt

theorem lemma54_second_integral_continuous {D : ℕ} (hD : 1 < D) :
    Continuous (lemma54SecondIntegral D) := by
  apply continuous_of_dominated (bound := lemma54SecondMajorant D)
  · intro x
    exact (lemma54_second_kernel_integrable hD x).aestronglyMeasurable
  · intro x
    exact Eventually.of_forall (lemma54_second_kernel_norm_bound D x)
  · exact lemma54_second_majorant_integrable hD
  · apply Eventually.of_forall
    intro u
    unfold lemma54SecondKernel lemma53OscillatoryKernel
    fun_prop

theorem lemma54_actual_second_deriv_continuousOn {D : ℕ} (hD : 1 < D) :
    ContinuousOn (deriv (deriv (lemma53PaperDelta D))) (Ioi 0) := by
  apply (lemma54_second_integral_continuous hD).continuousOn.congr
  intro x hx
  exact lemma54_actual_delta_second_deriv hD hx

theorem lemma54_first_deriv_mellin_convergent {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (deriv (lemma53PaperDelta D)) s := by
  apply mellinConvergent_of_isBigO_rpow
    ((lemma54_actual_first_deriv_continuousOn hD).locallyIntegrableOn measurableSet_Ioi)
    (lemma54_actual_first_deriv_isBigO_atTop hD hL (a := s.re + 1) (by linarith))
    (by linarith) (lemma54_actual_first_deriv_isBigO_at_zero hD (lemma54_scale_ge_one hL)) hs

theorem lemma54_second_deriv_mellin_convergent {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (deriv (deriv (lemma53PaperDelta D))) s := by
  apply mellinConvergent_of_isBigO_rpow
    ((lemma54_actual_second_deriv_continuousOn hD).locallyIntegrableOn measurableSet_Ioi)
    (lemma54_actual_second_deriv_isBigO_atTop hD hL (a := s.re + 1) (by linarith))
    (by linarith) (lemma54_actual_second_deriv_isBigO_at_zero hD (lemma54_scale_ge_one hL)) hs

theorem lemma54_cpow_mul_tendsto_at_zero {f : ℝ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hf : f =O[𝓝[>] 0] (fun x : ℝ => x ^ (-(0 : ℝ)))) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * f x) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨c, hc⟩ := hf.bound
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hp : Tendsto (fun x : ℝ => x ^ s.re) (𝓝[>] 0) (𝓝 0) := by
    simpa only [Real.zero_rpow hs.ne'] using
      (Real.continuousAt_rpow_const 0 s.re (Or.inr hs.le)).continuousWithinAt.tendsto
  have hl := hp.const_mul c
  simp only [mul_zero] at hl
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hl
    (Eventually.of_forall fun x => norm_nonneg _) ?_
  filter_upwards [hc, show ∀ᶠ x : ℝ in 𝓝[>] 0, 0 < x from self_mem_nhdsWithin] with x hbound hx
  simp only [neg_zero, Real.rpow_zero, norm_one, mul_one] at hbound
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  have h := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hx.le s.re)
  simpa only [mul_comm] using h

theorem lemma54_cpow_mul_tendsto_atTop {f : ℝ → ℂ} (s : ℂ)
    (hf : f =O[atTop] (fun x : ℝ => x ^ (-(s.re + 1)))) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * f x) atTop (𝓝 0) := by
  obtain ⟨c, hc⟩ := hf.bound
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hp := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1)).const_mul c
  simp only [mul_zero] at hp
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hp
    (Eventually.of_forall fun x => norm_nonneg _) ?_
  filter_upwards [hc, eventually_gt_atTop (0 : ℝ)] with x hbound hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx.le _)] at hbound
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hx]
  have h := mul_le_mul_of_nonneg_left hbound (Real.rpow_nonneg hx.le s.re)
  have he : x ^ s.re * (c * x ^ (-(s.re + 1))) = c * x ^ (-(1 : ℝ)) := by
    rw [← mul_assoc, mul_comm (x ^ s.re) c, mul_assoc, ← Real.rpow_add hx]
    congr 1
    ring
  rw [he] at h
  exact h

theorem lemma54_actual_delta_boundary_products {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * lemma53PaperDelta D x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x : ℝ => (x : ℂ) ^ s * lemma53PaperDelta D x) atTop (𝓝 0) :=
  ⟨lemma54_cpow_mul_tendsto_at_zero hs (lemma54_actual_delta_isBigO_at_zero hD),
    lemma54_cpow_mul_tendsto_atTop s
      (lemma54_actual_delta_isBigO_atTop hD hL (a := s.re + 1) (by linarith))⟩

theorem lemma54_actual_first_deriv_boundary_products {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    Tendsto (fun x : ℝ => (x : ℂ) ^ s * deriv (lemma53PaperDelta D) x) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto (fun x : ℝ => (x : ℂ) ^ s * deriv (lemma53PaperDelta D) x) atTop (𝓝 0) :=
  ⟨lemma54_cpow_mul_tendsto_at_zero hs
      (lemma54_actual_first_deriv_isBigO_at_zero hD (lemma54_scale_ge_one hL)),
    lemma54_cpow_mul_tendsto_atTop s
      (lemma54_actual_first_deriv_isBigO_atTop hD hL (a := s.re + 1) (by linarith))⟩

end ZhangLS.Spec
