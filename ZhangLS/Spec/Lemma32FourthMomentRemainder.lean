import ZhangLS.Spec.Lemma32QuarticTrivialBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32NondegenerateFourthMoment {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (H : ℕ) : ℝ :=
  ∑ v ∈ Finset.univ \ lemma32DegenerateQuarticTuples H, |lemma32QuarticCorrelation χ v|

lemma lemma32_actual_fourth_moment_decomposition {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (H : ℕ) :
    lemma32BurgessFourthMoment χ H =
      (∑ v ∈ lemma32DegenerateQuarticTuples H, lemma32QuarticCorrelation χ v)+
        ∑ v ∈ Finset.univ \ lemma32DegenerateQuarticTuples H, lemma32QuarticCorrelation χ v := by
  rw [lemma32_actual_burgess_fourth_moment_expansion]
  rw [Finset.sum_sdiff_eq_sub (Finset.subset_univ _)]
  ring

lemma lemma32_actual_fourth_moment_remainder_bound {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (H : ℕ) :
    lemma32BurgessFourthMoment χ H ≤ 3*(D : ℝ)*(H : ℝ)^2+lemma32NondegenerateFourthMoment χ H := by
  rw [lemma32_actual_fourth_moment_decomposition]
  apply add_le_add (lemma32_degenerate_fourth_moment_contribution_bound χ H)
  unfold lemma32NondegenerateFourthMoment
  exact Finset.sum_le_sum (fun v hv => le_abs_self _)

lemma lemma32_nondegenerate_fourth_moment_nonneg {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (H : ℕ) : 0 ≤ lemma32NondegenerateFourthMoment χ H := by
  unfold lemma32NondegenerateFourthMoment
  exact Finset.sum_nonneg (fun v hv => abs_nonneg _)

end ZhangLS.Spec
