import ZhangLS.Spec.Lemma111SmoothedTent

/-! # Lemma 11.1 with the paper's original ranges and absolute constants -/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Filter
open scoped Real Topology

lemma lemma111_scaled_log_displacement {D : ℕ} (hD : 1 < D) (y a : ℝ) :
    lemma111Scale D * (Real.log y / Real.log (lemma23PaperP D) - a) =
      lemma23PaperL D ^ 15 * (Real.log y - a * lemma23PaperL D ^ 9) := by
  have hL : lemma23PaperL D ≠ 0 := (Real.log_pos (by exact_mod_cast hD)).ne'
  unfold lemma111Scale lemma23PaperP
  rw [Real.log_exp]
  field_simp

lemma lemma111_scale_eta (D : ℕ) (hD : 1 < D) :
    lemma23PaperL D ^ 15 * lemma23PaperL D ^ (-10 : ℤ) = lemma23PaperL D ^ 5 := by
  have hL : lemma23PaperL D ≠ 0 := (Real.log_pos (by exact_mod_cast hD)).ne'
  rw [zpow_neg, zpow_ofNat]
  field_simp

lemma lemma111_lower_log_gap {D : ℕ} (hD : 1 < D) {y a : ℝ}
    (h : lemma23PaperP D ^ a * lemma111EtaPlus D ≤ y) :
    lemma23PaperL D ^ 5 ≤
      lemma111Scale D * (Real.log y / Real.log (lemma23PaperP D) - a) := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hp := Real.rpow_pos_of_pos hP a
  have he : 0 < lemma111EtaPlus D := Real.exp_pos _
  have hl := Real.log_le_log (mul_pos hp he) h
  rw [Real.log_mul hp.ne' he.ne', Real.log_rpow hP,
    lemma111EtaPlus, Real.log_exp, lemma23PaperP, Real.log_exp] at hl
  have hm := mul_le_mul_of_nonneg_left hl
    (pow_nonneg (Real.log_natCast_nonneg D) 15)
  rw [lemma111_scaled_log_displacement hD]
  have hs := lemma111_scale_eta D hD
  change lemma23PaperL D ^ 15 * _ ≤ lemma23PaperL D ^ 15 * _ at hm
  nlinarith only [hm, hs]

lemma lemma111_upper_log_gap {D : ℕ} (hD : 1 < D) {y a : ℝ}
    (hy : 0 < y) (h : y ≤ lemma23PaperP D ^ a * lemma111EtaMinus D) :
    lemma23PaperL D ^ 5 ≤
      lemma111Scale D * (a - Real.log y / Real.log (lemma23PaperP D)) := by
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hp := Real.rpow_pos_of_pos hP a
  have he : 0 < lemma111EtaMinus D := Real.exp_pos _
  have hl := Real.log_le_log hy h
  rw [Real.log_mul hp.ne' he.ne', Real.log_rpow hP,
    lemma111EtaMinus, Real.log_exp, lemma23PaperP, Real.log_exp] at hl
  have hm := mul_le_mul_of_nonneg_left hl
    (pow_nonneg (Real.log_natCast_nonneg D) 15)
  have hs := lemma111_scale_eta D hD
  change lemma23PaperL D ^ 15 * _ ≤ lemma23PaperL D ^ 15 * _ at hm
  have hid := lemma111_scaled_log_displacement hD y a
  nlinarith only [hm, hs, hid]

lemma lemma111_interior_pos {D : ℕ} {y : ℝ} (h : Lemma111Interior D y) : 0 < y := by
  rcases h with h | h
  · exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _) (Real.exp_pos _)) h.1
  · exact lt_of_lt_of_le (mul_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _) (Real.exp_pos _)) h.1

lemma lemma111_transition_pos {D : ℕ} {y : ℝ} (h : Lemma111Transition D y) : 0 < y := by
  rcases h with (h | h) | h
  all_goals
    exact lt_trans (mul_pos (Real.rpow_pos_of_pos (Real.exp_pos _) _) (Real.exp_pos _)) h.1

lemma lemma111_interior_separation {D : ℕ} (hD : 1 < D) {y : ℝ}
    (h : Lemma111Interior D y) :
    let u := Real.log y / Real.log (lemma23PaperP D)
    lemma23PaperL D ^ 5 ≤ |lemma111Scale D * (1 / 2 - u)| ∧
    lemma23PaperL D ^ 5 ≤ |lemma111Scale D * (251 / 500 - u)| ∧
    lemma23PaperL D ^ 5 ≤ |lemma111Scale D * (63 / 125 - u)| := by
  have hy := lemma111_interior_pos h
  have hA := lemma111_scale_pos hD
  dsimp only
  rcases h with h | h
  · have hleft := lemma111_lower_log_gap hD h.1
    have hright := lemma111_upper_log_gap hD hy h.2
    refine ⟨?_, ?_, ?_⟩
    · have habs := neg_le_abs (lemma111Scale D * (1 / 2 - Real.log y / Real.log (lemma23PaperP D)))
      linarith only [hleft, habs]
    · exact hright.trans (le_abs_self _)
    · have habs := le_abs_self (lemma111Scale D * (63 / 125 - Real.log y / Real.log (lemma23PaperP D)))
      nlinarith only [hright, habs, hA]
  · have hleft := lemma111_lower_log_gap hD h.1
    have hright := lemma111_upper_log_gap hD hy h.2
    refine ⟨?_, ?_, ?_⟩
    · have habs := neg_le_abs (lemma111Scale D * (1 / 2 - Real.log y / Real.log (lemma23PaperP D)))
      nlinarith only [hleft, habs, hA]
    · have habs := neg_le_abs (lemma111Scale D * (251 / 500 - Real.log y / Real.log (lemma23PaperP D)))
      linarith only [hleft, habs]
    · exact hright.trans (le_abs_self _)

lemma lemma111_interior_bound {D : ℕ} (hD : 1 < D)
    (hL : 1 ≤ lemma23PaperL D) {y : ℝ} (hy : Lemma111Interior D y) :
    |lemma111Tent (Real.log y / Real.log (lemma23PaperP D)) -
      lemma111SmoothedOne D y| ≤ 4000 * Real.exp (-(lemma23PaperL D ^ 10)) := by
  have hsep := lemma111_interior_separation hD hy
  have hR : 0 ≤ lemma23PaperL D ^ 5 := pow_nonneg (by linarith) _
  have ha := lemma111_primitive_error_away hD hR hsep.1
  have hb := lemma111_primitive_error_away hD hR hsep.2.1
  have hc := lemma111_primitive_error_away hD hR hsep.2.2
  have hs := lemma111_second_difference_error ha hb hc
  rw [abs_sub_comm, lemma111_tent_second_difference,
    lemma111_smoothed_second_difference hD (lemma111_interior_pos hy)]
  dsimp only
  refine hs.trans ?_
  have hA : 1 ≤ lemma111Scale D := one_le_pow₀ hL
  have hpow : (lemma23PaperL D ^ 5) ^ 2 = lemma23PaperL D ^ 10 := by ring
  rw [hpow]
  calc
    2000 * (2 * Real.exp (-(lemma23PaperL D ^ 10)) / lemma111Scale D) ≤
        2000 * (2 * Real.exp (-(lemma23PaperL D ^ 10))) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact div_le_self (by positivity) hA
    _ = _ := by ring

lemma lemma111_transition_bound {D : ℕ} (hD : 1 < D)
    (hL : 1 ≤ lemma23PaperL D) {y : ℝ} (hy : Lemma111Transition D y) :
    |lemma111Tent (Real.log y / Real.log (lemma23PaperP D)) -
      lemma111SmoothedOne D y| ≤ 4000 * lemma23PaperL D ^ (-10 : ℤ) := by
  refine (lemma111_smoothed_uniform_bound hD (lemma111_transition_pos hy)).trans ?_
  rw [zpow_neg, zpow_ofNat, ← div_eq_mul_inv]
  apply div_le_div_of_nonneg_left (by norm_num)
    (pow_pos (by linarith : 0 < lemma23PaperL D) 10)
  exact pow_le_pow_right₀ hL (by norm_num : 10 ≤ 24)

/-- Zhang's original Lemma 11.1, with explicit absolute constants `C=4000`
and `c=1`. All hypotheses are genuine paper parameters or range restrictions. -/
theorem lemma111_proved : Lemma111Target := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop 1))
  refine ⟨4000, 1, by norm_num, by norm_num, max N 2, ?_⟩
  intro D hD y
  have hD' : 1 < D := lt_of_lt_of_le (by norm_num : 1 < 2) ((le_max_right N 2).trans hD)
  have hL := hN D ((le_max_left N 2).trans hD)
  constructor
  · intro hy
    simpa using lemma111_interior_bound hD' hL hy
  · intro hy
    exact lemma111_transition_bound hD' hL hy

end ZhangLS.Spec
