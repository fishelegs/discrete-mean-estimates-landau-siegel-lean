import ZhangLS.Spec.Lemma54LogTailMoments
import ZhangLS.Spec.Lemma54HalfPowerMoments
import ZhangLS.Spec.Lemma54SmallSecondMoment

/-! # Uniform integration of both actual large-x derivative tails -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000

noncomputable def lemma54LogTailConstant : ℝ := lemma54WeightedConstant * (4 + 2 * Real.exp 1)
noncomputable def lemma54ExpTailConstant : ℝ :=
  2 * lemma54WeightedConstant * Real.sqrt Real.pi * Real.exp 3

noncomputable def lemma54LargeMomentEnvelope (D : ℕ) (x : ℝ) : ℝ :=
  lemma54LogTailConstant * ((1 + x ^ 3) * Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2))) +
    lemma54ExpTailConstant * ((1 + x ^ 3) * Real.exp (-(x ^ (1 / 2 : ℝ)) / lemma53PaperScale D))

theorem lemma54_log_tail_constant_pos : 0 < lemma54LogTailConstant := by
  unfold lemma54LogTailConstant
  exact mul_pos lemma54_weighted_constant_pos (by positivity)

theorem lemma54_exp_tail_constant_pos : 0 < lemma54ExpTailConstant := by
  unfold lemma54ExpTailConstant
  exact mul_pos (mul_pos (mul_pos (by norm_num) lemma54_weighted_constant_pos)
    (Real.sqrt_pos.mpr Real.pi_pos)) (Real.exp_pos _)

theorem lemma54_strip_weight_le_one_add_cube {x σ : ℝ} (hx : 0 < x)
    (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) : x ^ (σ + 1) ≤ 1 + x ^ 3 := by
  by_cases hx1 : x ≤ 1
  · have hh := Real.rpow_le_one hx.le hx1 (show 0 ≤ σ + 1 by linarith)
    nlinarith [pow_nonneg hx.le 3]
  · have hh := lemma54_strip_weight_le_cubic_cap hx le_rfl (lt_of_not_ge hx1).le hσ hσ2
    linarith

theorem lemma54_stretched_exp_le_half_power {B x : ℝ} (hB : 0 < B) (hx : 1 ≤ x) :
    Real.exp (-(x ^ (99 / 100 : ℝ)) / B) ≤ Real.exp (-(x ^ (1 / 2 : ℝ)) / B) := by
  apply Real.exp_le_exp.mpr
  exact div_le_div_of_nonneg_right
    (neg_le_neg (Real.rpow_le_rpow_of_exponent_le hx (by norm_num : (1 / 2 : ℝ) ≤ 99 / 100))) hB.le

theorem lemma54_large_moment_envelope_integrable {D : ℕ} (hD : 1 < D) :
    IntegrableOn (lemma54LargeMomentEnvelope D) (Ioi 0) :=
  ((lemma54_log_cubic_tail_integrable (lemma53_scale_pos hD)).const_mul lemma54LogTailConstant).add
    ((lemma54_half_power_cubic_tail_integrable (lemma53_scale_pos hD)).const_mul lemma54ExpTailConstant)

theorem lemma54_large_moment_envelope_nonneg {D : ℕ} {x : ℝ} (hx : 0 < x) :
    0 ≤ lemma54LargeMomentEnvelope D x := by
  unfold lemma54LargeMomentEnvelope
  exact add_nonneg
    (mul_nonneg lemma54_log_tail_constant_pos.le (mul_nonneg (by positivity) (Real.exp_nonneg _)))
    (mul_nonneg lemma54_exp_tail_constant_pos.le (mul_nonneg (by positivity) (Real.exp_nonneg _)))

theorem lemma54_actual_large_moment_envelope {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {σ x : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2)
    (hx : lemma51PaperT0 D ^ (51 / 50 : ℝ) < x) :
    x ^ (σ + 1) * ‖deriv (deriv (lemma53PaperDelta D)) x‖ ≤ lemma54LargeMomentEnvelope D x := by
  have hx1 : 1 ≤ x := (lemma54_small_endpoint_polynomial hL).1.trans hx.le
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have he := lemma54_actual_second_deriv_large_range hD hL hx0 hx
  have hw := lemma54_strip_weight_le_one_add_cube hx0 hσ hσ2
  have hf := lemma54_stretched_exp_le_half_power (lemma53_scale_pos hD) hx1
  have ht : ‖deriv (deriv (lemma53PaperDelta D)) x‖ ≤
      lemma54LogTailConstant * Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) +
        lemma54ExpTailConstant * Real.exp (-(x ^ (1 / 2 : ℝ)) / lemma53PaperScale D) := by
    unfold lemma54DerivativeTail at he
    change ‖deriv (deriv (lemma53PaperDelta D)) x‖ ≤
      lemma54LogTailConstant * Real.exp (-((lemma53PaperScale D * Real.log x / 100) ^ 2)) +
        lemma54ExpTailConstant * Real.exp (-(x ^ (99 / 100 : ℝ)) / lemma53PaperScale D) at he
    exact he.trans (add_le_add le_rfl
      (mul_le_mul_of_nonneg_left hf lemma54_exp_tail_constant_pos.le))
  have hh := mul_le_mul hw ht (norm_nonneg _) (show 0 ≤ 1 + x ^ 3 by positivity)
  unfold lemma54LargeMomentEnvelope
  convert hh using 1 <;> ring

theorem lemma54_large_moment_envelope_integral_bound {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) :
    (∫ x : ℝ in Ioi 0, lemma54LargeMomentEnvelope D x) ≤
      lemma54LogTailConstant * (200 * Real.sqrt Real.pi * Real.exp 1) +
        lemma54ExpTailConstant * (10082 * lemma53PaperScale D ^ 8) := by
  unfold lemma54LargeMomentEnvelope
  rw [integral_add
    ((lemma54_log_cubic_tail_integrable (lemma53_scale_pos hD)).const_mul _)
    ((lemma54_half_power_cubic_tail_integrable (lemma53_scale_pos hD)).const_mul _),
    integral_const_mul, integral_const_mul]
  exact add_le_add
    (mul_le_mul_of_nonneg_left (lemma54_log_cubic_tail_integral_bound (lemma54_scale_ge_200 hL))
      lemma54_log_tail_constant_pos.le)
    (mul_le_mul_of_nonneg_left (lemma54_half_power_cubic_tail_integral_bound (lemma54_scale_ge_one hL))
      lemma54_exp_tail_constant_pos.le)

theorem lemma54_actual_large_second_moment_bound {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {σ : ℝ} (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) :
    (∫ x : ℝ in Ioi (lemma51PaperT0 D ^ (51 / 50 : ℝ)),
      x ^ (σ + 1) * ‖deriv (deriv (lemma53PaperDelta D)) x‖) ≤
      lemma54LogTailConstant * (200 * Real.sqrt Real.pi * Real.exp 1) +
        lemma54ExpTailConstant * (10082 * lemma53PaperScale D ^ 8) := by
  have ht0 : 0 ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ) := by
    have hh := (lemma54_small_endpoint_polynomial hL).1
    linarith
  have hg := lemma54_large_moment_envelope_integrable hD
  have hi := (lemma54_actual_second_moment_integrable hD hL (by linarith : 0 < σ)).mono_set
    (Ioi_subset_Ioi ht0)
  have hm := integral_mono_ae hi (hg.mono_set (Ioi_subset_Ioi ht0)) (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact lemma54_actual_large_moment_envelope hD hL hσ hσ2 hx)
  have hs := setIntegral_mono_set hg
    (by filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
        exact lemma54_large_moment_envelope_nonneg hx)
    (Eventually.of_forall fun x hx => ht0.trans_lt hx)
  exact hm.trans (hs.trans (lemma54_large_moment_envelope_integral_bound hD hL))

end ZhangLS.Spec
