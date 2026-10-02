import ZhangLS.Spec.Lemma32InfiniteShift
import ZhangLS.Spec.Lemma32SmoothingWindow
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Set Filter
open scoped Classical Topology
set_option maxHeartbeats 2000000

lemma lemma32_actual_original_tail_reduction {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 2 ≤ D) (hL : 3 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ) :
    lemma32SmoothingWindowLowerBound*(∑ n ∈ Finset.Icc (D^4+1) (D^8),
      ‖lemma23NuArithmeticFunction χ n‖^2*(lemma34Tau 2 n : ℝ)^2/(n : ℝ)) ≤
      lemma32CircleConstant*lemma23PaperL D^(-2007 : ℤ)+‖lemma32LeftVerticalIntegral χ‖ := by
  have hd : 1 < D := by omega
  calc
    _ ≤ (lemma32SmoothedWeightedDifference χ).re := lemma32_actual_weighted_tail_le_smoothed χ hD
    _ = (lemma32ActualResidue χ+lemma32LeftVerticalIntegral χ).re := by
      rw [lemma32_actual_smoothed_difference_eq_residue_add_left χ hd]
    _ ≤ ‖lemma32ActualResidue χ+lemma32LeftVerticalIntegral χ‖ := Complex.re_le_norm _
    _ ≤ ‖lemma32ActualResidue χ‖+‖lemma32LeftVerticalIntegral χ‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (lemma32_actual_residue_bound χ hd hL hA) le_rfl

end ZhangLS.Spec
