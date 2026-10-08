import FrequencyProfile

noncomputable section

namespace PiWeightedColon.Regression

theorem origin_entry_guards_and_zero_power :
    originEntry 0 1 1 0 = 1 ∧ originEntry 1 1 0 2 = 0 ∧ originEntry 1 0 3 2 = 0 := by decide

theorem actual_small_frequency_lengths :
    frequencyLength 0 0 = 1 ∧ frequencyLength 0 1 = 3 ∧
    frequencyLength 1 0 = 2 ∧ frequencyLength 1 1 = 6 ∧
    frequencyLength 1 2 = 1 ∧ frequencyLength 1 3 = 3 ∧
    frequencyLength 1 4 = 1 ∧ frequencyLength 1 5 = 3 := by decide

theorem actual_frequency_cutoff :
    frequencyLength 1 1 > 3 ∧ ¬ frequencyLength 1 3 > 3 ∧
    frequencyLength 2 4 > 0 ∧ ¬ frequencyLength 2 4 > 2 := by decide

theorem actual_origin_column_counts :
    Fintype.card (OriginLabel 0) = 4 ∧ Fintype.card (OriginLabel 1) = 16 ∧
    Fintype.card (OriginLabel 2) = 36 := by
  simp only [originLabel_card]
  decide

theorem actual_origin_label_roundtrip :
    originalLabelEquiv 1 ((originalLabelEquiv 1).symm ⟨(5, 2), by decide⟩) =
      ⟨(5, 2), by decide⟩ := (originalLabelEquiv 1).apply_symm_apply _

/-- This checks an actual integral divided difference, including its even
node difference. It is not obtained by cancelling in F2. -/
theorem actual_newton_order_one : integerNewtonEntry 3 0 0 1 true = 13 := by
  have h := originEntry_newton_expansion 3 0 0 1 true
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  rw [integerNewtonEntry_zero] at h
  norm_num [originEntry, frequencyNode, newtonEvaluationFactor, Finset.prod_range_succ] at h
  omega

theorem actual_newton_order_two : integerNewtonEntry 3 0 0 2 true = 9 := by
  have h := originEntry_newton_expansion 3 0 0 2 true
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at h
  rw [integerNewtonEntry_zero, actual_newton_order_one] at h
  norm_num [originEntry, frequencyNode, newtonEvaluationFactor, Finset.prod_range_succ] at h
  omega

theorem actual_newton_reduction_boundary : (integerNewtonEntry 0 1 1 0 false : F2) = 1 := by
  rw [integerNewtonEntry_mod_two]
  decide

theorem actual_newton_reduction_parity : (integerNewtonEntry 4 0 0 2 true : F2) = 0 := by
  rw [integerNewtonEntry_mod_two]
  decide

theorem actual_newton_diagonal_factors :
    newtonEvaluationFactor false 0 0 = 1 ∧ newtonEvaluationFactor true 1 1 = 2 ∧
    newtonEvaluationFactor false 2 2 = 8 ∧ newtonEvaluationFactor true 3 3 = 48 := by decide

theorem actual_newton_above_diagonal : newtonEvaluationFactor true 3 1 = 0 := by
  exact newtonEvaluationFactor_above true 3 1 (by decide)

end PiWeightedColon.Regression
