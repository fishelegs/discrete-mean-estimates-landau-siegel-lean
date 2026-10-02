import ZhangLS.Spec.Lemma54LargeExteriorMellin

/-! # All actual Mellin pieces give one uniform disk error budget -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma54DiskTailConstant : ℝ :=
  2 + 6 * lemma53SmallErrorConstant + 2 * lemma54NearZeroConstant +
    (288 + lemma53SmallErrorConstant) + lemma54LargeExteriorConstant

theorem lemma54_disk_tail_constant_pos : 0 < lemma54DiskTailConstant := by
  unfold lemma54DiskTailConstant
  have hc : 0 < lemma53SmallErrorConstant := by unfold lemma53SmallErrorConstant; positivity
  have hn := lemma54_near_zero_constant_pos
  have hl := lemma54_large_exterior_constant_pos
  positivity

theorem lemma54_window_subset_small_middle {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    lemma54PaperWindow D ⊆ Ioc 1 (lemma51PaperT0 D ^ (51 / 50 : ℝ)) := by
  have ht : 2000 ≤ lemma51PaperT0 D := by
    apply hL.trans
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D)
      (show (1 : ℕ) ≤ 519 by norm_num)
  intro x hx
  have hb := lemma54_window_x_bounds hL hx
  exact ⟨by linarith [hb.2.1], hb.2.2.2⟩

theorem lemma54_actual_mellin_disk_budget {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖lemma54PaperDeltaMellin D s - 1‖ ≤
      10403 * lemma44PaperAlpha D * Real.log (lemma23PaperL D) +
        lemma54DiskTailConstant * lemma23PaperL D ^ 3200 * Real.exp (-(lemma23PaperL D ^ 10) / 2) := by
  let T := lemma51PaperT0 D ^ (51 / 50 : ℝ)
  let S := Ioc (1 : ℝ) T \ lemma54PaperWindow D
  let f : ℝ → ℂ := fun x => (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x
  let E := Real.exp (-(lemma23PaperL D ^ 10) / 2)
  have hT1 : 1 ≤ T := (lemma54_small_endpoint_polynomial hL).1
  have hT0 : 0 ≤ T := by linarith
  have hS : MeasurableSet S := measurableSet_Ioc.diff (lemma54_window_measurable D)
  have hr := (lemma54_disk_closed_strip hL hs).1
  have hi : IntegrableOn f (Ioi 0) := lemma54_mellin_convergent hD hL (by linarith : 0 < s.re)
  have hi1 := hi.mono_set (Ioi_subset_Ioi (show (0 : ℝ) ≤ 1 by norm_num))
  have hiT := hi.mono_set (Ioi_subset_Ioi hT0)
  have hi1T := hi.mono_set (show Ioc (1 : ℝ) T ⊆ Ioi 0 from fun x hx => by
    change 0 < x
    linarith [hx.1])
  have h01 := intervalIntegral.integral_interval_add_Ioi (a := 0) (b := 1) hi hi1
  have h1T := intervalIntegral.integral_interval_add_Ioi (a := 1) (b := T) hi1 hiT
  rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)] at h01
  rw [intervalIntegral.integral_of_le hT1] at h1T
  have hwindow := integral_inter_add_diff (lemma54_window_measurable D) hi1T
  rw [inter_eq_right.mpr (lemma54_window_subset_small_middle hL)] at hwindow
  have heq : (∫ x : ℝ in Ioi 0, f x) - 1 =
      ((∫ x : ℝ in lemma54PaperWindow D, f x) - 1) +
        (∫ x : ℝ in Ioc 0 1, f x) + (∫ x : ℝ in S, f x) + (∫ x : ℝ in Ioi T, f x) := by
    rw [← h01, ← h1T, ← hwindow]
    dsimp only [S]
    ring
  have hcenter := lemma54_disk_window_actual_mellin_normalization hD hL hs
  have hnear := lemma54_actual_near_zero_mellin_bound hD hL hs
  have hsmall := lemma54_actual_small_exterior_mellin_bound hD hL hs hS
    (show S ⊆ Ioc (1 : ℝ) T from diff_subset)
    (show S ⊆ (lemma54PaperWindow D)ᶜ from fun _ hx => hx.2)
  have hlarge := lemma54_actual_large_exterior_mellin_bound hD hL hs
  have hn1 := norm_add_le
    (((∫ x : ℝ in lemma54PaperWindow D, f x) - 1) + (∫ x : ℝ in Ioc 0 1, f x) + (∫ x : ℝ in S, f x))
    (∫ x : ℝ in Ioi T, f x)
  have hn2 := norm_add_le
    (((∫ x : ℝ in lemma54PaperWindow D, f x) - 1) + (∫ x : ℝ in Ioc 0 1, f x))
    (∫ x : ℝ in S, f x)
  have hn3 := norm_add_le ((∫ x : ℝ in lemma54PaperWindow D, f x) - 1) (∫ x : ℝ in Ioc 0 1, f x)
  have hbudget : ‖(∫ x : ℝ in Ioi 0, f x) - 1‖ ≤
      10400 * lemma44PaperAlpha D * Real.log (lemma23PaperL D) + 3 * lemma44PaperAlpha D +
        (2 + 6 * lemma53SmallErrorConstant * lemma23PaperL D ^ 405 + 2 * lemma54NearZeroConstant +
          (288 + lemma53SmallErrorConstant) * lemma23PaperL D ^ 1838 +
            lemma54LargeExteriorConstant * lemma23PaperL D ^ 3200) * E := by
    rw [heq]
    dsimp only [f, S, T] at hn1 hn2 hn3 ⊢
    dsimp only [E]
    nlinarith only [hn1, hn2, hn3, hcenter, hnear, hsmall, hlarge]
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hlog : 1 ≤ Real.log (lemma23PaperL D) :=
    (Real.le_log_iff_exp_le (by linarith : 0 < lemma23PaperL D)).2
      (Real.exp_one_lt_three.le.trans (by linarith : (3 : ℝ) ≤ lemma23PaperL D))
  have ha := (lemma54_disk_alpha_small hL).1
  have hCs : 0 ≤ lemma53SmallErrorConstant := by unfold lemma53SmallErrorConstant; positivity
  have hp0 : 1 ≤ lemma23PaperL D ^ 3200 := one_le_pow₀ hL1
  have hp405 : lemma23PaperL D ^ 405 ≤ lemma23PaperL D ^ 3200 := pow_le_pow_right₀ hL1 (by norm_num)
  have hp1838 : lemma23PaperL D ^ 1838 ≤ lemma23PaperL D ^ 3200 := pow_le_pow_right₀ hL1 (by norm_num)
  have hα := mul_le_mul_of_nonneg_left hlog (show 0 ≤ 3 * lemma44PaperAlpha D by positivity)
  have h0 := mul_le_mul_of_nonneg_left hp0 (show 0 ≤ 2 + 2 * lemma54NearZeroConstant by
    have h := lemma54_near_zero_constant_pos; positivity)
  have h405 := mul_le_mul_of_nonneg_left hp405 (show 0 ≤ 6 * lemma53SmallErrorConstant by positivity)
  have h1838 := mul_le_mul_of_nonneg_left hp1838 (show 0 ≤ 288 + lemma53SmallErrorConstant by positivity)
  have htail : (2 + 6 * lemma53SmallErrorConstant * lemma23PaperL D ^ 405 + 2 * lemma54NearZeroConstant +
      (288 + lemma53SmallErrorConstant) * lemma23PaperL D ^ 1838 +
        lemma54LargeExteriorConstant * lemma23PaperL D ^ 3200) * E ≤
      lemma54DiskTailConstant * lemma23PaperL D ^ 3200 * E := by
    apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
    unfold lemma54DiskTailConstant
    nlinarith only [h0, h405, h1838]
  change ‖(∫ x : ℝ in Ioi 0, f x) - 1‖ ≤ _
  dsimp only [E] at hbudget htail
  nlinarith only [hbudget, htail, hα]

end ZhangLS.Spec
