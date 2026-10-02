import ZhangLS.Spec.Lemma54GaussianConcentration

/-! # The original Gaussian window and the original radius-10-alpha disk -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter

set_option maxHeartbeats 1000000

noncomputable def lemma54PaperWindow (D : ℕ) : Set ℝ :=
  Icc (lemma51PaperT0 D - lemma23PaperL D ^ 405)
    (lemma51PaperT0 D + lemma23PaperL D ^ 405)

theorem lemma54_window_measurable (D : ℕ) : MeasurableSet (lemma54PaperWindow D) :=
  measurableSet_Icc

theorem lemma54_window_width_le_half_center {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    2 * lemma23PaperL D ^ 405 ≤ lemma51PaperT0 D := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hp : lemma23PaperL D ^ 405 ≤ lemma23PaperL D ^ 518 :=
    pow_le_pow_right₀ hL1 (by norm_num)
  unfold lemma51PaperT0
  calc
    _ ≤ 2 * lemma23PaperL D ^ 518 := mul_le_mul_of_nonneg_left hp (by norm_num)
    _ ≤ lemma23PaperL D ^ 518 * lemma23PaperL D := by
      nlinarith [pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 518]
    _ = _ := (pow_succ (lemma23PaperL D) 518).symm

theorem lemma54_twice_center_le_small_endpoint {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    2 * lemma51PaperT0 D ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ) := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have ht : 0 ≤ lemma23PaperL D ^ 519 := pow_nonneg (by linarith) _
  have hp : lemma23PaperL D ^ 520 ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ) := by
    unfold lemma51PaperT0
    rw [← Real.rpow_natCast, ← Real.rpow_natCast (lemma23PaperL D) 519,
      ← Real.rpow_mul (by linarith : 0 ≤ lemma23PaperL D)]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  apply le_trans _ hp
  unfold lemma51PaperT0
  calc
    _ ≤ lemma23PaperL D ^ 519 * lemma23PaperL D := by nlinarith
    _ = _ := (pow_succ (lemma23PaperL D) 519).symm

theorem lemma54_window_x_bounds {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {x : ℝ} (hx : x ∈ lemma54PaperWindow D) :
    1 ≤ x ∧ lemma51PaperT0 D / 2 ≤ x ∧ x ≤ 2 * lemma51PaperT0 D ∧
      x ≤ lemma51PaperT0 D ^ (51 / 50 : ℝ) := by
  have hw := lemma54_window_width_le_half_center hL
  have ht : 2000 ≤ lemma51PaperT0 D := by
    have hp : lemma23PaperL D ≤ lemma23PaperL D ^ 519 := by
      simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D)
        (show (1 : ℕ) ≤ 519 by norm_num)
    exact hL.trans hp
  change lemma51PaperT0 D - lemma23PaperL D ^ 405 ≤ x ∧
    x ≤ lemma51PaperT0 D + lemma23PaperL D ^ 405 at hx
  have hx2 : x ≤ 2 * lemma51PaperT0 D := by linarith
  exact ⟨by linarith, by linarith, hx2,
    hx2.trans (lemma54_twice_center_le_small_endpoint hL)⟩

theorem lemma54_window_log_bound {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {x : ℝ} (hx : x ∈ lemma54PaperWindow D) :
    0 ≤ Real.log x ∧ Real.log x ≤ 520 * Real.log (lemma23PaperL D) := by
  have hb := lemma54_window_x_bounds hL hx
  have hLpos : 0 < lemma23PaperL D := by linarith
  have htpos : 0 < lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  refine ⟨Real.log_nonneg hb.1, ?_⟩
  calc
    _ ≤ Real.log (2 * lemma51PaperT0 D) := Real.log_le_log (by linarith) hb.2.2.1
    _ = Real.log 2 + 519 * Real.log (lemma23PaperL D) := by
      rw [Real.log_mul (by norm_num) htpos.ne', lemma51PaperT0, Real.log_pow]
      norm_num
    _ ≤ _ := by
      have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 2)
        (show (2 : ℝ) ≤ lemma23PaperL D by linarith)
      linarith

theorem lemma54_disk_alpha_small {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    0 < lemma44PaperAlpha D ∧ lemma44PaperAlpha D ≤ 1 / 20 := by
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hp : lemma23PaperL D ≤ lemma23PaperL D ^ 9 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D)
      (show (1 : ℕ) ≤ 9 by norm_num)
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  refine ⟨by positivity, ?_⟩
  apply (div_le_iff₀ (by positivity : 0 < lemma23PaperL D ^ 9)).2
  nlinarith [Real.pi_le_four]

theorem lemma54_disk_closed_strip {D : ℕ} (hL : 2000 ≤ lemma23PaperL D)
    {s : ℂ} (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    1 / 2 ≤ s.re ∧ s.re ≤ 3 / 2 := by
  have ha := (lemma54_disk_alpha_small hL).2
  have hr := Complex.abs_re_le_norm (s - 1)
  simp only [sub_re, one_re] at hr
  have hh : |s.re - 1| ≤ 1 / 2 := by linarith
  exact ⟨by linarith [(abs_le.mp hh).1], by linarith [(abs_le.mp hh).2]⟩

theorem lemma54_disk_window_exponent_budget {D : ℕ} (hL : 2000 ≤ lemma23PaperL D) :
    5200 * lemma44PaperAlpha D * Real.log (lemma23PaperL D) ≤ 1 := by
  let L := lemma23PaperL D
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL2000 : 2000 ≤ L := hL
  have hp : 20800 ≤ L ^ 8 := by
    have h2 : (2000 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL2000 2
    have h28 : L ^ 2 ≤ L ^ 8 := pow_le_pow_right₀ hL1 (by norm_num)
    norm_num at h2
    linarith
  have hlog : Real.log L ≤ L := (Real.log_le_sub_one_of_pos hLpos).trans (by linarith)
  have hl0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  unfold lemma44PaperAlpha lemma23PaperP
  rw [Real.log_exp]
  change 5200 * (Real.pi / L ^ 9) * Real.log L ≤ 1
  rw [← mul_div_assoc, div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hLpos 9)).2
  calc
    5200 * Real.pi * Real.log L ≤ 20800 * L := by nlinarith [Real.pi_le_four]
    _ ≤ L ^ 8 * L := mul_le_mul_of_nonneg_right hp hLpos.le
    _ = 1 * L ^ 9 := by ring

end ZhangLS.Spec
