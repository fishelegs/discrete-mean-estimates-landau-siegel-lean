import ZhangLS.Spec.Lemma55MangoldtPositivity
import ZhangLS.Spec.Lemma55ExceptionalLocalTail

/-! # Actual upper bound for the four remaining-zero families

The exact pole and exceptional-zero identities combine arithmetic positivity with the actual analytic errors. The complete height family and both exceptional local-disk cases are retained.
-/

namespace ZhangLS.Spec
open Complex Finset

noncomputable def lemma55CombinedRemainingPower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t r : ℝ) (β v : ℂ) (J : ℕ) : ℂ :=
  (lemma55WeightedRemainingZeroPowerSum χ 0 r β v J + lemma55ZetaWeightedZeroPowerSum 0 r v J) +
    (lemma55WeightedRemainingZeroPowerSum χ t r β v J + lemma55ZetaWeightedZeroPowerSum t r v J)

noncomputable def lemma55CombinedRemovedDerivative {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t r : ℝ) (β v : ℂ) (J : ℕ) : ℂ :=
  (lemma55WeightedRemovedLogDerivative χ 0 r β v J + lemma55ZetaWeightedRemovedLogDerivative 0 r v J) +
    (lemma55WeightedRemovedLogDerivative χ t r β v J + lemma55ZetaWeightedRemovedLogDerivative t r v J)

lemma lemma55_actual_combined_remaining_error_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {β : ℂ} (hzero : dirichletLFunction χ β = 0) (hderiv : deriv (dirichletLFunction χ) β ≠ 0)
    {r : ℝ} (hr : 0 < r) (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55CombinedRemovedDerivative χ t r β v J - lemma55CombinedRemainingPower χ t r β v J‖ ≤
      374400 * Real.log (D : ℝ) := by
  have hχ0 := lemma55_actual_weighted_remaining_error_uniform_bound χ hD hL (by simp : |(0 : ℝ)| ≤ 2 * D)
    hr hlower hzero hderiv hv J
  have hχt := lemma55_actual_weighted_remaining_error_uniform_bound χ hD hL ht hr hlower hzero hderiv hv J
  have hζ0 := lemma55_actual_zeta_weighted_power_error_uniform_bound hD hL (by simp : |(0 : ℝ)| ≤ 2 * D)
    hr hlower hv J
  have hζt := lemma55_actual_zeta_weighted_power_error_uniform_bound hD hL ht hr hlower hv J
  have heq : lemma55CombinedRemovedDerivative χ t r β v J - lemma55CombinedRemainingPower χ t r β v J =
      ((lemma55WeightedRemovedLogDerivative χ 0 r β v J - lemma55WeightedRemainingZeroPowerSum χ 0 r β v J) +
        (lemma55ZetaWeightedRemovedLogDerivative 0 r v J - lemma55ZetaWeightedZeroPowerSum 0 r v J)) +
      ((lemma55WeightedRemovedLogDerivative χ t r β v J - lemma55WeightedRemainingZeroPowerSum χ t r β v J) +
        (lemma55ZetaWeightedRemovedLogDerivative t r v J - lemma55ZetaWeightedZeroPowerSum t r v J)) := by
    unfold lemma55CombinedRemovedDerivative lemma55CombinedRemainingPower
    ring
  rw [heq]
  apply (norm_add_le _ _).trans
  have h0 := (norm_add_le _ _).trans (add_le_add hχ0 hζ0)
  have ht' := (norm_add_le _ _).trans (add_le_add hχt hζt)
  calc
    _ ≤ (79200 * Real.log (D : ℝ) + 108000 * Real.log (D : ℝ)) +
        (79200 * Real.log (D : ℝ) + 108000 * Real.log (D : ℝ)) := add_le_add h0 ht'
    _ = _ := by ring

noncomputable def lemma55WeightedLocalPoleDifference {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t r : ℝ) (β v : ℂ) (J : ℕ) : ℂ :=
  ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
    (1 / (lemma55JensenCenter t - 1) ^ (2 * (j + 1)) -
      (if β ∈ lemma55LocalZeroFinset χ t then
        1 / (lemma55JensenCenter t - β) ^ (2 * (j + 1)) else 0)) / (r : ℂ) ^ (j + 1)

lemma lemma55_actual_removed_pair_pole_identity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t r : ℝ) (β v : ℂ) (J : ℕ) :
    lemma55WeightedRemovedLogDerivative χ t r β v J + lemma55ZetaWeightedRemovedLogDerivative t r v J =
      (∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (lemma55NormalizedLogDerivative χ t (2 * j + 1) + lemma55ZetaNormalizedLogDerivative t (2 * j + 1)) /
          (r : ℂ) ^ (j + 1)) + lemma55WeightedLocalPoleDifference χ t r β v J := by
  unfold lemma55WeightedRemovedLogDerivative lemma55RemovedNormalizedLogDerivative
    lemma55ZetaWeightedRemovedLogDerivative lemma55WeightedLocalPoleDifference
  simp_rw [lemma55_actual_zeta_normalized_pole_correction,
    show ∀ j : ℕ, 2 * j + 1 + 1 = 2 * (j + 1) by intro j; omega]
  rw [← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro j _
  ring

lemma lemma55_actual_combined_removed_derivative_nonpos {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t : ℝ) {r : ℝ} (hr : 0 < r) (β : ℂ) {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    (lemma55CombinedRemovedDerivative χ t r β v J -
      (lemma55WeightedLocalPoleDifference χ 0 r β v J + lemma55WeightedLocalPoleDifference χ t r β v J)).re ≤ 0 := by
  have heq : lemma55CombinedRemovedDerivative χ t r β v J -
      (lemma55WeightedLocalPoleDifference χ 0 r β v J + lemma55WeightedLocalPoleDifference χ t r β v J) =
      ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (lemma55NormalizedLogDerivative χ 0 (2 * j + 1) + lemma55ZetaNormalizedLogDerivative 0 (2 * j + 1) +
          (lemma55NormalizedLogDerivative χ t (2 * j + 1) + lemma55ZetaNormalizedLogDerivative t (2 * j + 1))) /
            (r : ℂ) ^ (j + 1) := by
    unfold lemma55CombinedRemovedDerivative
    rw [lemma55_actual_removed_pair_pole_identity, lemma55_actual_removed_pair_pole_identity]
    have hsum : (∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (lemma55NormalizedLogDerivative χ 0 (2 * j + 1) + lemma55ZetaNormalizedLogDerivative 0 (2 * j + 1)) /
          (r : ℂ) ^ (j + 1)) +
      (∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (lemma55NormalizedLogDerivative χ t (2 * j + 1) + lemma55ZetaNormalizedLogDerivative t (2 * j + 1)) /
          (r : ℂ) ^ (j + 1)) =
      ∑ j ∈ range J, (lemma55FejerDetectionWeight v J j : ℂ) *
        (lemma55NormalizedLogDerivative χ 0 (2 * j + 1) + lemma55ZetaNormalizedLogDerivative 0 (2 * j + 1) +
          (lemma55NormalizedLogDerivative χ t (2 * j + 1) + lemma55ZetaNormalizedLogDerivative t (2 * j + 1))) /
            (r : ℂ) ^ (j + 1) := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro j _
      ring
    linear_combination hsum
  rw [heq]
  exact lemma55_actual_weighted_four_logDeriv_nonpos χ t hr hv J


lemma lemma55_actual_local_pole_difference_eq {D : ℕ} (χ : RealPrimitiveCharacter D)
    (t β r : ℝ) (v : ℂ) (J : ℕ) :
    lemma55WeightedLocalPoleDifference χ t r (β : ℂ) v J =
      lemma55WeightedExceptionalPoleDifference t β r v J +
        (if (β : ℂ) ∈ lemma55LocalZeroFinset χ t then 0 else lemma55WeightedExceptionalTail t β r v J) := by
  classical
  by_cases hm : (β : ℂ) ∈ lemma55LocalZeroFinset χ t
  · simp only [hm, if_true, add_zero, lemma55WeightedLocalPoleDifference,
      lemma55WeightedExceptionalPoleDifference]
    apply sum_congr rfl
    intro j _
    rw [inv_pow, inv_pow]
    ring
  · simp only [hm, if_false, lemma55WeightedLocalPoleDifference,
      lemma55WeightedExceptionalPoleDifference, lemma55WeightedExceptionalTail]
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro j _
    rw [inv_pow, inv_pow]
    ring

lemma lemma55_actual_local_pole_difference_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) (t : ℝ) {β r : ℝ}
    (hβ : β ≤ 1) (hzero : dirichletLFunction χ (β : ℂ) = 0) (hr : 0 < r)
    (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    ‖lemma55WeightedLocalPoleDifference χ t r (β : ℂ) v J‖ ≤
      2 * (1 - β) * (J : ℝ) * ((J : ℝ) + 1) * Real.exp (4 * (J : ℝ) / Real.log (D : ℝ)) + 4 := by
  have hp := lemma55_weighted_exceptional_pole_difference_bound t β hβ
    (by linarith only [hL] : 0 < Real.log (D : ℝ)) hr hlower hv J
  rw [lemma55_actual_local_pole_difference_eq]
  by_cases hm : (β : ℂ) ∈ lemma55LocalZeroFinset χ t
  · rw [if_pos hm, add_zero]
    linarith only [hp]
  · rw [if_neg hm]
    exact (norm_add_le _ _).trans (add_le_add hp
      (lemma55_actual_exceptional_outside_local_disk_tail_bound χ hD hL t hzero hm hr hlower hv J))

lemma lemma55_actual_combined_remaining_real_upper_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ Real.log (D : ℝ)) {t : ℝ} (ht : |t| ≤ 2 * (D : ℝ))
    {β r : ℝ} (hβ : β ≤ 1) (hzero : dirichletLFunction χ (β : ℂ) = 0)
    (hderiv : deriv (dirichletLFunction χ) (β : ℂ) ≠ 0) (hr : 0 < r)
    (hlower : ((1 + 2 / Real.log (D : ℝ))⁻¹) ^ 2 ≤ r)
    {v : ℂ} (hv : ‖v‖ ≤ 1) (J : ℕ) :
    (lemma55CombinedRemainingPower χ t r (β : ℂ) v J).re ≤
      374400 * Real.log (D : ℝ) + 8 +
        4 * (1 - β) * (J : ℝ) * ((J : ℝ) + 1) * Real.exp (4 * (J : ℝ) / Real.log (D : ℝ)) := by
  have he := (abs_re_le_norm (lemma55CombinedRemovedDerivative χ t r (β : ℂ) v J -
    lemma55CombinedRemainingPower χ t r (β : ℂ) v J)).trans
      (lemma55_actual_combined_remaining_error_bound χ hD hL ht hzero hderiv hr hlower hv J)
  rw [sub_re] at he
  have hb := lemma55_actual_combined_removed_derivative_nonpos χ t hr (β : ℂ) hv J
  rw [sub_re, add_re] at hb
  have h0 := (re_le_norm (lemma55WeightedLocalPoleDifference χ 0 r (β : ℂ) v J)).trans
    (lemma55_actual_local_pole_difference_bound χ hD hL 0 hβ hzero hr hlower hv J)
  have h1 := (re_le_norm (lemma55WeightedLocalPoleDifference χ t r (β : ℂ) v J)).trans
    (lemma55_actual_local_pole_difference_bound χ hD hL t hβ hzero hr hlower hv J)
  linarith only [(abs_le.mp he).1, hb, h0, h1]

end ZhangLS.Spec
