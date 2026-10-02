import ZhangLS.Spec.Lemma55ZeroRemovedLog

/-!
# The actual local logarithmic-derivative formula

The actual L-function's logarithmic derivative equals the contributions
from actual local zeros, counted with their actual orders, plus the
logarithmic derivative of the zero-removed analytic factor. At every
height-2D Jensen center this remainder has norm at most 176 log D.
-/

namespace ZhangLS.Spec

open Complex Metric Set
open scoped Real

theorem lemma55_actual_zero_factor_logDeriv
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) {t : ℝ} {z : ℂ}
    (hP : lemma55LocalZeroFactor χ t z ≠ 0) :
    logDeriv (lemma55LocalZeroFactor χ t) z =
      ∑ ρ ∈ lemma55LocalZeroFinset χ t,
        (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) / (z - ρ) := by
  classical
  have heq : lemma55LocalZeroFactor χ t = fun w =>
      ∏ ρ ∈ lemma55LocalZeroFinset χ t,
        (w - ρ) ^ analyticOrderNatAt (dirichletLFunction χ) ρ :=
    funext (lemma55_actual_zero_factor_eq_product χ hD t)
  have hterms : ∀ ρ ∈ lemma55LocalZeroFinset χ t,
      (z - ρ) ^ analyticOrderNatAt (dirichletLFunction χ) ρ ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mp
    rwa [← lemma55_actual_zero_factor_eq_product χ hD t z]
  rw [heq, logDeriv_prod hterms (fun ρ _ => by fun_prop)]
  apply Finset.sum_congr rfl
  intro ρ _
  have hderiv : deriv (fun w : ℂ => w - ρ) z = 1 := by
    simpa using ((hasDerivAt_id z).sub_const ρ).deriv
  rw [logDeriv_fun_pow (by fun_prop), logDeriv_apply, hderiv]
  ring

theorem lemma55_actual_local_logDeriv_formula
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) {z : ℂ}
    (hLz : dirichletLFunction χ z ≠ 0) :
    logDeriv (dirichletLFunction χ) z =
      (∑ ρ ∈ lemma55LocalZeroFinset χ t,
        (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) / (z - ρ)) +
          logDeriv (lemma55ZeroRemovedL χ t) z := by
  have heq : dirichletLFunction χ = fun w =>
      lemma55LocalZeroFactor χ t w * lemma55ZeroRemovedL χ t w :=
    funext (lemma55_actual_zero_factorization χ hD t)
  have hn : lemma55LocalZeroFactor χ t z ≠ 0 ∧ lemma55ZeroRemovedL χ t z ≠ 0 := by
    apply mul_ne_zero_iff.mp
    rwa [← lemma55_actual_zero_factorization χ hD t z]
  nth_rw 1 [heq]
  rw [logDeriv_mul z hn.1 hn.2
    (lemma55_actual_zero_factor_analytic χ hD t z (mem_univ z)).differentiableAt
    (lemma55_actual_zero_removed_analytic χ hD t z (mem_univ z)).differentiableAt]
  rw [lemma55_actual_zero_factor_logDeriv χ hD hn.1]

theorem lemma55_actual_zero_removed_center_logDeriv_bound
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    ‖logDeriv (lemma55ZeroRemovedL χ t) (lemma55JensenCenter t)‖ ≤
      176 * Real.log (D : ℝ) := by
  have hb := lemma23_norm_logDeriv_le_of_norm_ratio_bound_on_ball
    (f := lemma55ZeroRemovedL χ t) (c := lemma55JensenCenter t)
    (R := (5 / 4 : ℝ)) (H := lemma55ZeroRemovedRatioBound χ t) (by norm_num)
    (lemma55_zero_removed_ratio_bound_gt_one χ hD t)
    (fun z _ => (lemma55_actual_zero_removed_analytic χ hD t z (mem_univ z)).differentiableAt)
    (fun z hz => lemma55_actual_zero_removed_ne_zero χ hD (ball_subset_closedBall hz))
    (fun z hz => lemma55_actual_zero_removed_ratio_bound χ hD ht
      (closedBall_subset_closedBall (by norm_num : (5 / 4 : ℝ) ≤ 3 / 2) (ball_subset_closedBall hz)))
  have hlog := lemma55_actual_zero_removed_log_ratio_bound χ hD hL ht
  apply hb.trans
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 5 / 4)).mpr
  linarith only [hlog]

theorem lemma55_actual_center_local_logDeriv_error
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ)) :
    ‖logDeriv (dirichletLFunction χ) (lemma55JensenCenter t) -
      ∑ ρ ∈ lemma55LocalZeroFinset χ t,
        (analyticOrderNatAt (dirichletLFunction χ) ρ : ℂ) / (lemma55JensenCenter t - ρ)‖ ≤
          176 * Real.log (D : ℝ) := by
  rw [lemma55_actual_local_logDeriv_formula χ hD t (lemma55_actual_jensen_center_ne_zero χ t),
    add_sub_cancel_left]
  exact lemma55_actual_zero_removed_center_logDeriv_bound χ hD hL ht

end ZhangLS.Spec
