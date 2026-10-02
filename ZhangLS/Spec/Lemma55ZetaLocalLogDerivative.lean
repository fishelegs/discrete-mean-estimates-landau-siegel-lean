import ZhangLS.Spec.Lemma55ZetaZeroRemovedLog

/-! # Actual local zeta logarithmic derivatives

The pole-removed function factors on Re s>0, including removable zero
values. Its logarithmic derivative is the actual local zero sum plus
the analytic quotient term. Restoring zeta subtracts its pole at one.
-/

namespace ZhangLS.Spec

open Complex Metric Set Filter
open scoped Topology Real

theorem lemma55_actual_zeta_zero_factor_logDeriv {t : ℝ} {z : ℂ}
    (hP : lemma55ZetaLocalZeroFactor t z ≠ 0) :
    logDeriv (lemma55ZetaLocalZeroFactor t) z =
      ∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
        (analyticOrderNatAt zetaPoleRemoved ρ : ℂ) / (z - ρ) := by
  classical
  have heq : lemma55ZetaLocalZeroFactor t = fun w =>
      ∏ ρ ∈ lemma55ZetaLocalZeroFinset t,
        (w - ρ) ^ analyticOrderNatAt zetaPoleRemoved ρ :=
    funext (lemma55_actual_zeta_zero_factor_eq_product t)
  have hterms : ∀ ρ ∈ lemma55ZetaLocalZeroFinset t,
      (z - ρ) ^ analyticOrderNatAt zetaPoleRemoved ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mp
    rwa [← lemma55_actual_zeta_zero_factor_eq_product t z]
  rw [heq, logDeriv_prod hterms (fun ρ _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro ρ _
  have hderiv : deriv (fun w : ℂ => w - ρ) z = 1 := by
    simpa using ((hasDerivAt_id z).sub_const ρ).deriv
  rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply, hderiv]
  ring

theorem lemma55_actual_zeta_removed_local_logDeriv_formula
    (t : ℝ) {z : ℂ} (hz : 0 < z.re) (hR : zetaPoleRemoved z ≠ 0) :
    logDeriv zetaPoleRemoved z =
      (∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
        (analyticOrderNatAt zetaPoleRemoved ρ : ℂ) / (z - ρ)) +
          logDeriv (lemma55ZetaZeroRemoved t) z := by
  have heq : zetaPoleRemoved =ᶠ[𝓝 z] fun w =>
      lemma55ZetaLocalZeroFactor t w * lemma55ZetaZeroRemoved t w := by
    filter_upwards [(isOpen_lt continuous_const continuous_re).mem_nhds hz] with w hw
    exact lemma55_actual_zeta_zero_factorization t hw
  have hn : lemma55ZetaLocalZeroFactor t z ≠ 0 ∧ lemma55ZetaZeroRemoved t z ≠ 0 := by
    apply mul_ne_zero_iff.mp
    rwa [← lemma55_actual_zeta_zero_factorization t hz]
  have hlog : logDeriv zetaPoleRemoved z =
      logDeriv (fun w => lemma55ZetaLocalZeroFactor t w * lemma55ZetaZeroRemoved t w) z := by
    change deriv zetaPoleRemoved z / zetaPoleRemoved z = _
    rw [heq.deriv_eq, heq.self_of_nhds]
    rfl
  rw [hlog, logDeriv_mul z hn.1 hn.2
    (lemma55_actual_zeta_zero_factor_analytic t z (mem_univ z)).differentiableAt
    (lemma55_actual_zeta_zero_removed_analytic t z hz).differentiableAt,
    lemma55_actual_zeta_zero_factor_logDeriv hn.1]

theorem lemma55_actual_zeta_zero_removed_center_logDeriv_bound
    {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    ‖logDeriv (lemma55ZetaZeroRemoved t) (lemma55JensenCenter t)‖ ≤
      240 * Real.log (D : ℝ) := by
  have hb := lemma23_norm_logDeriv_le_of_norm_ratio_bound_on_ball
    (f := lemma55ZetaZeroRemoved t) (c := lemma55JensenCenter t)
    (R := (5 / 4 : ℝ)) (H := lemma55ZetaZeroRemovedRatioBound D t) (by norm_num)
    (lemma55_zeta_zero_removed_ratio_bound_gt_one hD t)
    (fun z hz => (lemma55_actual_zeta_zero_removed_analytic t z
      (lemma55_zeta_disk_re_pos (by norm_num) (ball_subset_closedBall hz))).differentiableAt)
    (fun z hz => lemma55_actual_zeta_zero_removed_ne_zero (ball_subset_closedBall hz))
    (fun z hz => lemma55_actual_zeta_zero_removed_ratio_bound hD ht
      (closedBall_subset_closedBall (by norm_num : (5 / 4 : ℝ) ≤ 3 / 2) (ball_subset_closedBall hz)))
  have hlog := lemma55_actual_zeta_zero_removed_log_ratio_bound hD hL ht
  apply hb.trans
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5 / 4)).mpr
  linarith only [hlog]

theorem lemma55_actual_zeta_center_local_logDeriv_formula (t : ℝ) :
    logDeriv riemannZeta (lemma55JensenCenter t) + 1 / (lemma55JensenCenter t - 1) =
      (∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
        (analyticOrderNatAt zetaPoleRemoved ρ : ℂ) / (lemma55JensenCenter t - ρ)) +
          logDeriv (lemma55ZetaZeroRemoved t) (lemma55JensenCenter t) := by
  have hc1 : lemma55JensenCenter t ≠ 1 := by
    intro h
    have hh := congrArg Complex.re h
    simp at hh
  have hζ : riemannZeta (lemma55JensenCenter t) ≠ 0 := norm_pos_iff.mp (by
    have hb := lemma55_actual_zeta_norm_lower (by simp : 2 ≤ (lemma55JensenCenter t).re)
    linarith only [hb])
  have hR : zetaPoleRemoved (lemma55JensenCenter t) ≠ 0 := norm_pos_iff.mp (by
    have hb := lemma55_actual_zeta_pole_removed_center_lower t
    linarith only [hb])
  rw [← lemma55_actual_zeta_removed_local_logDeriv_formula t (by simp) hR,
    lemma55_actual_zeta_pole_removed_logDeriv (by simp) hc1 hζ, add_comm]

theorem lemma55_actual_zeta_center_local_logDeriv_error
    {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ))
    {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    ‖logDeriv riemannZeta (lemma55JensenCenter t) + 1 / (lemma55JensenCenter t - 1) -
      ∑ ρ ∈ lemma55ZetaLocalZeroFinset t,
        (analyticOrderNatAt zetaPoleRemoved ρ : ℂ) / (lemma55JensenCenter t - ρ)‖ ≤
          240 * Real.log (D : ℝ) := by
  rw [lemma55_actual_zeta_center_local_logDeriv_formula, add_sub_cancel_left]
  exact lemma55_actual_zeta_zero_removed_center_logDeriv_bound hD hL ht

end ZhangLS.Spec
