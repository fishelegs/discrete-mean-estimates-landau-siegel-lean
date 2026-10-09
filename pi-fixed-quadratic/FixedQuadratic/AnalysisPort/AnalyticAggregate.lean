/- Adapted from openai/math adc7f1241b42e322a6451854ab7e4b4c146bf78a,
Analysis/AnalyticAggregate.lean, Apache-2.0; complete determinant summation and collision transfer. -/
import FixedQuadratic.AnalysisPort.LiteralAnalyticSummand
import OAI.NumberTheory.PiExponent.Analysis.TranslationCountLimit

namespace OAI

open scoped BigOperators Topology
open Filter

namespace PiExponent.FixedFieldLiteralAnalytic
open FixedFieldAnalyticData

theorem actual_minor_expansion {nu : ℝ} (d : FixedFieldAnalyticData nu) {H : ℝ}
    (selection : Row d H → Column d H) :
    (actualMinor d H selection).det =
      ∑ f : ChoiceFamily d H, (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det := by
  classical
  have hp : ∀ r c : Row d H,
      (MatrixTranslation.periodMonomial r.1.val logarithmicPeriod
        ((selection c).1 0) (fun i => (selection c).1 i.succ)).support ⊆
        MatrixTranslation.transverseIndices (fixedWeights d) H := by
    intro r c
    apply MatrixTranslation.periodMonomial_support_subset _ _ _ _ _ _ (fixedWeights_pos d)
    have hc := InterpolationMatrix.column_weight_le d.w0_pos (fixedWeights_pos d) (selection c)
    have hz : 0 ≤ (d.w0 : ℝ) * ((selection c).1 0 : ℝ) :=
      mul_nonneg d.w0_pos.le (Nat.cast_nonneg _)
    linarith
  have he := MatrixTranslation.det_matrix_translation
    (centers d)
    (MatrixArithmetic.truncationOrders (finiteHeights d) d.F0 d.v0)
    (fun r : Row d H => r.1.val) (fun r => r.2.1 0) logarithmicPeriod
    (fun r i => r.2.1 i.succ) (fun c => (selection c).1 0)
    (fun c i => (selection c).1 i.succ) (MatrixTranslation.transverseIndices (fixedWeights d) H) hp
  convert! he using 1

theorem card_choiceFamily_le {nu : ℝ} (d : FixedFieldAnalyticData nu) (H : ℝ) :
    Fintype.card (ChoiceFamily d H) ≤ translationTermCount d.m d.v0 H ^ actualRowCount d H := by
  classical
  rw [Fintype.card_pi]
  calc
    _ ≤ ∏ _r : Row d H, translationTermCount d.m d.v0 H := by
      apply Finset.prod_le_prod
      intro r _
      exact MatrixTranslation.row_term_count (fixedWeights d) H d.v0
        (weights_one_le d)
        (beta d r) (r.2.1 0) (rowOrder_le d r)
    _ = _ := by simp only [Finset.prod_const, Finset.card_univ, actualRowCount]

noncomputable def analyticRemainder {nu : ℝ} (d : FixedFieldAnalyticData nu) (H : ℝ) : ℝ :=
  Collision.collisionRemainder (actualRowCount d H) H +
    Real.log (translationTermCount d.m d.v0 H : ℝ) / H

theorem actual_minor_analytic_bound {nu : ℝ} (d : FixedFieldAnalyticData nu) (hnu : 0 ≤ nu)
    {H : ℝ} (hH : 0 < H) (selection : Row d H → Column d H)
    (hne : (actualMinor d H selection).det ≠ 0) :
    Real.log ‖(actualMinor d H selection).det‖ / ((actualRowCount d H : ℝ) * H) ≤
      d.analyticError + analyticRemainder d H +
        max (-collisionRate d H)
          (-nu * ((d.A : ℝ) * (1 - d.eta) - actualMean d H)) := by
  have hQ : (0 : ℝ) < translationTermCount d.m d.v0 H := by
    unfold translationTermCount
    positivity
  have hc : (Fintype.card (ChoiceFamily d H) : ℝ) ≤
      (translationTermCount d.m d.v0 H : ℝ) ^ actualRowCount d H := by
    exact_mod_cast card_choiceFamily_le d H
  have hb := DeterminantAnalyticBound.log_norm_sum_le
    (fun f : ChoiceFamily d H => (∏ r, choiceScalar d r (f r)) * (choiceMatrix d selection f).det)
    (actualMinor d H selection).det (actualRowCount_pos d hH) hH hQ hc
    (actual_minor_expansion d selection) hne (norm_actual_summand_le d hnu hH selection)
  convert! hb using 1
  unfold analyticRemainder
  ring

theorem tendsto_analyticRemainder {nu : ℝ} (d : FixedFieldAnalyticData nu) :
    Tendsto (analyticRemainder d) atTop (𝓝 0) := by
  have hv : 0 < d.v0 := by exact_mod_cast d.v0_pos
  have ht : 0 < d.theta := by exact_mod_cast d.theta_pos
  have hcount := MatrixCounting.tendsto_rowCount_normalized d.K d.v0 d.theta
    (finiteHeights d) hv ht (finiteHeights_two_le d)
  have hlead : 0 < (d.K : ℝ) * (d.theta : ℝ) ^ d.m /
      (((d.m + 1).factorial : ℝ) * (d.v0 : ℝ) *
        ∏ i, MatrixArithmetic.logWeights (finiteHeights d) i) := by
    apply div_pos
    · apply mul_pos
      · exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one d.K_pos
      · exact pow_pos d.theta_pos _
    · apply mul_pos
      · exact mul_pos (by positivity) d.v0_pos
      · exact Finset.prod_pos (fun i _ => fixedWeights_pos d i)
  have hr := tendsto_collisionRemainder_of_normalized_pow
    (M := actualRowCount d) hcount hlead
  have hq := tendsto_log_translationTermCount_div d.m d.v0_pos
  convert! hr.add hq using 1
  norm_num

end PiExponent.FixedFieldLiteralAnalytic

end OAI
