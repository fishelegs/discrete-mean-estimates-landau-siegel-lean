import ZhangLS.Spec.Lemma32BurgessPairings
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_actual_quartic_correlation_abs_bound {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) {H : ℕ} (v : Fin 4 → Fin H) :
    |lemma32QuarticCorrelation χ v| ≤ (D : ℝ) := by
  unfold lemma32QuarticCorrelation
  calc
    _ = ‖∑ x : ZMod D, (χ.chi (∏ i : Fin 4, (x+((v i).val : ZMod D)))).re‖ :=
      (Real.norm_eq_abs _).symm
    _ ≤ ∑ x : ZMod D, ‖(χ.chi (∏ i : Fin 4, (x+((v i).val : ZMod D)))).re‖ := norm_sum_le _ _
    _ ≤ ∑ x : ZMod D, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x hx
      rw [Real.norm_eq_abs]
      exact (Complex.abs_re_le_norm _).trans (χ.chi.norm_le_one _)
    _ = _ := by simp

lemma lemma32_degenerate_fourth_moment_contribution_bound {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (H : ℕ) :
    (∑ v ∈ lemma32DegenerateQuarticTuples H, lemma32QuarticCorrelation χ v) ≤
      3*(D : ℝ)*(H : ℝ)^2 := by
  have hc := lemma32_degenerate_quartic_tuples_card H
  calc
    _ ≤ ∑ v ∈ lemma32DegenerateQuarticTuples H, (D : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      exact (le_abs_self _).trans (lemma32_actual_quartic_correlation_abs_bound χ v)
    _ = ((lemma32DegenerateQuarticTuples H).card : ℝ)*(D : ℝ) := by simp
    _ ≤ ((3*H^2 : ℕ) : ℝ)*(D : ℝ) := mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (Nat.cast_nonneg _)
    _ = _ := by push_cast;ring

end ZhangLS.Spec
