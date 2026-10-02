import ZhangLS.Spec.Lemma32RealSmoothing
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32SmoothingWindowLowerBound : ℝ :=
  min (Real.exp (-(1/2 : ℝ))-Real.exp (-1)) (Real.exp (-1)-Real.exp (-2))

lemma lemma32_smoothing_window_lower_bound_pos : 0 < lemma32SmoothingWindowLowerBound := by
  unfold lemma32SmoothingWindowLowerBound
  apply lt_min
  · apply sub_pos.mpr
    exact Real.exp_lt_exp.mpr (by norm_num)
  · apply sub_pos.mpr
    exact Real.exp_lt_exp.mpr (by norm_num)

lemma lemma32_exponential_smoothing_window_lower (X Y u : ℝ) (hX : 0 < X)
    (hY : 4*X ≤ Y) (hu : X < u) (huY : u ≤ Y) :
    lemma32SmoothingWindowLowerBound ≤ Real.exp (-u/Y)-Real.exp (-u/X) := by
  have hY0 : 0 < Y := by linarith
  have hx1 : 1 ≤ u/X := (le_div_iff₀ hX).mpr (by linarith)
  have hy1 : u/Y ≤ 1 := (div_le_iff₀ hY0).mpr (by simpa using huY)
  have hex : Real.exp (-u/X) ≤ Real.exp (-1) := by
    apply Real.exp_le_exp.mpr
    simp only [neg_div]
    linarith
  by_cases hsmall : u ≤ 2*X
  · have hhalf : u/Y ≤ 1/2 := (div_le_iff₀ hY0).mpr (by linarith)
    have hey : Real.exp (-(1/2 : ℝ)) ≤ Real.exp (-u/Y) := by
      apply Real.exp_le_exp.mpr
      simp only [neg_div]
      linarith
    exact (min_le_left _ _).trans (by linarith)
  · have hx2 : 2 ≤ u/X := (le_div_iff₀ hX).mpr (by linarith)
    have hex2 : Real.exp (-u/X) ≤ Real.exp (-2) := by
      apply Real.exp_le_exp.mpr
      simp only [neg_div]
      linarith
    have hey : Real.exp (-1) ≤ Real.exp (-u/Y) := by
      apply Real.exp_le_exp.mpr
      simp only [neg_div]
      linarith
    exact (min_le_right _ _).trans (by linarith)

lemma lemma32_actual_smoothing_weight_window_lower {D n : ℕ} (hD : 2 ≤ D)
    (hn : D^4 < n) (hn8 : n ≤ D^8) :
    lemma32SmoothingWindowLowerBound ≤
      Real.exp (-(n : ℝ)/(D : ℝ)^8)-Real.exp (-(n : ℝ)/(D : ℝ)^4) := by
  have hd2 : 2 ≤ (D : ℝ) := by exact_mod_cast hD
  have hd0 : 0 < (D : ℝ) := by linarith
  have hd4 : 4 ≤ (D : ℝ)^4 := by
    calc
      _ ≤ (2 : ℝ)^4 := by norm_num
      _ ≤ _ := by gcongr
  apply lemma32_exponential_smoothing_window_lower ((D : ℝ)^4) ((D : ℝ)^8) (n : ℝ)
    (pow_pos hd0 4)
  · have he : (D : ℝ)^8 = ((D : ℝ)^4)^2 := by ring
    rw [he]
    nlinarith
  · exact_mod_cast hn
  · exact_mod_cast hn8

lemma lemma32_actual_weighted_tail_le_smoothed {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 2 ≤ D) :
    lemma32SmoothingWindowLowerBound*
      (∑ n ∈ Finset.Icc (D^4+1) (D^8), lemma32ActualCoefficient χ n/(n : ℝ)) ≤
      (lemma32SmoothedWeightedDifference χ).re := by
  rw [lemma32_actual_smoothed_difference_real_series,Complex.ofReal_re,mul_sum]
  calc
    _ ≤ ∑ n ∈ Finset.Icc (D^4+1) (D^8), lemma32RealSmoothedTerm χ n := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := Finset.mem_Icc.mp hn
      have hw := lemma32_actual_smoothing_weight_window_lower hD (by omega : D^4 < n) hh.2
      unfold lemma32RealSmoothedTerm
      calc
        _ = (lemma32ActualCoefficient χ n/(n : ℝ))*lemma32SmoothingWindowLowerBound := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hw
          (div_nonneg (lemma32_actual_coefficient_nonneg χ n) (Nat.cast_nonneg n))
    _ ≤ _ := (lemma32_actual_real_smoothed_terms_summable χ).sum_le_tsum _
      (fun n _ => lemma32_actual_real_smoothed_term_nonneg χ (by omega : 1 ≤ D) n)

end ZhangLS.Spec
