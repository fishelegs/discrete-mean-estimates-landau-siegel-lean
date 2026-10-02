import ZhangLS.Spec.Lemma56PerronFarError

/-! # Actual finite near-cut error and an explicit integer-window bound -/

namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PerronNearIndices (x ε : ℝ) : Finset ℕ :=
  (Finset.range ⌈x * Real.exp ε⌉₊).filter
    (fun n => n ≠ 0 ∧ |Real.log (x / (n : ℝ))| < ε)

lemma lemma56_perron_near_real_bounds {x ε : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ≠ 0)
    (hd : |Real.log (x / (n : ℝ))| < ε) :
    x * Real.exp (-ε) < (n : ℝ) ∧ (n : ℝ) < x * Real.exp ε := by
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hh := abs_lt.mp hd
  rw [Real.log_div hx.ne' hnp.ne'] at hh
  have hu : Real.log ((n : ℝ) / x) < ε := by
    rw [Real.log_div hnp.ne' hx.ne']
    linarith only [hh.1]
  have hl : -ε < Real.log ((n : ℝ) / x) := by
    rw [Real.log_div hnp.ne' hx.ne']
    linarith only [hh.2]
  have hle := Real.exp_lt_exp.mpr hl
  have hue := Real.exp_lt_exp.mpr hu
  rw [Real.exp_log (div_pos hnp hx)] at hle hue
  constructor
  · have h := (lt_div_iff₀ hx).mp hle
    simpa only [mul_comm] using h
  · have h := (div_lt_iff₀ hx).mp hue
    simpa only [mul_comm] using h

lemma lemma56_perron_near_term_outside {q : ℕ} (θ : DirichletCharacter ℂ q)
    (B τ ε : ℝ) {x : ℝ} (hx : 0 < x) {n : ℕ} (hn : n ∉ lemma56PerronNearIndices x ε) :
    lemma56PerronNearErrorTerm θ B x τ ε n = 0 := by
  by_cases hn0 : n = 0
  · subst n
    simp [lemma56PerronNearErrorTerm, lemma56_perron_error_zero]
  by_cases hd : |Real.log (x / (n : ℝ))| < ε
  · have hu := (lemma56_perron_near_real_bounds hx hn0 hd).2
    have hm : n ∈ lemma56PerronNearIndices x ε := by
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_ceil.mpr hu), hn0, hd⟩
    exact (hn hm).elim
  · simp only [lemma56PerronNearErrorTerm, if_neg hd]

lemma lemma56_perron_near_error_tsum {q : ℕ} (θ : DirichletCharacter ℂ q)
    (B τ ε : ℝ) {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, lemma56PerronNearErrorTerm θ B x τ ε n) =
      ∑ n ∈ lemma56PerronNearIndices x ε, lemma56PerronErrorTerm θ B x τ n := by
  rw [tsum_eq_sum (s := lemma56PerronNearIndices x ε)
    (fun n hn => lemma56_perron_near_term_outside θ B τ ε hx hn)]
  apply Finset.sum_congr rfl
  intro n hn
  exact if_pos (Finset.mem_filter.mp hn).2.2

lemma lemma56_perron_near_indices_card {x ε : ℝ} (hx : 0 < x) (hε : 0 ≤ ε) :
    ((lemma56PerronNearIndices x ε).card : ℝ) ≤
      x * Real.exp ε - x * Real.exp (-ε) + 2 := by
  let lo := x * Real.exp (-ε)
  let up := x * Real.exp ε
  have hlo : 0 < lo := by dsimp [lo]; positivity
  have hup : 0 < up := by dsimp [up]; positivity
  have horder : lo ≤ up := by
    apply mul_le_mul_of_nonneg_left _ hx.le
    exact Real.exp_le_exp.mpr (by linarith only [hε])
  have hsub : lemma56PerronNearIndices x ε ⊆ Finset.Icc ⌈lo⌉₊ ⌊up⌋₊ := by
    intro n hn
    have hh := (Finset.mem_filter.mp hn).2
    have hb := lemma56_perron_near_real_bounds hx hh.1 hh.2
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hb.1.le, Nat.le_floor hb.2.le⟩
  have hcard : ((lemma56PerronNearIndices x ε).card : ℝ) ≤
      ((Finset.Icc ⌈lo⌉₊ ⌊up⌋₊).card : ℝ) := by exact_mod_cast Finset.card_le_card hsub
  by_cases hi : ⌈lo⌉₊ ≤ ⌊up⌋₊
  · rw [Nat.card_Icc, Nat.cast_sub (by omega), Nat.cast_add, Nat.cast_one] at hcard
    have hl := Nat.le_ceil lo
    have hu := Nat.floor_le hup.le
    change ((lemma56PerronNearIndices x ε).card : ℝ) ≤ up - lo + 2
    linarith only [hcard, hl, hu]
  · have hz : (Finset.Icc ⌈lo⌉₊ ⌊up⌋₊).card = 0 := by rw [Nat.card_Icc]; omega
    rw [hz, Nat.cast_zero] at hcard
    change ((lemma56PerronNearIndices x ε).card : ℝ) ≤ up - lo + 2
    linarith only [hcard, horder]

lemma lemma56_perron_error_norm_le_mangoldt {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B τ : ℝ) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ‖lemma56PerronErrorTerm θ B x τ n‖ ≤ ArithmeticFunction.vonMangoldt n := by
  by_cases hn : n = 0
  · subst n
    rw [lemma56_perron_error_zero]
    simp
  have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have he : (if (n : ℝ) < x then (1 : ℝ) else 0) =
      (if 1 < x / (n : ℝ) then (1 : ℝ) else 0) := by simp only [lt_div_iff₀ hnp, one_mul]
  rw [lemma56PerronErrorTerm, norm_mul, norm_mul, lemma56_gaussian_phase_norm hn τ,
    one_mul, Complex.norm_real, Real.norm_eq_abs, he]
  have hb := mul_le_mul (lemma56_mangoldt_norm_le θ n)
    (lemma56_perron_weight_step_error_le_one B (div_pos hx hnp))
    (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
  simpa only [mul_one] using hb

lemma lemma56_perron_near_error_bound {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) (B τ : ℝ) {x ε : ℝ} (hx : 1 ≤ x) (hε : 0 ≤ ε) :
    ‖∑' n : ℕ, lemma56PerronNearErrorTerm θ B x τ ε n‖ ≤
      (x * Real.exp ε - x * Real.exp (-ε) + 2) * Real.log (x * Real.exp ε) := by
  have hxp : 0 < x := by linarith only [hx]
  have hex : 1 ≤ Real.exp ε := Real.one_le_exp hε
  have hupper : 1 ≤ x * Real.exp ε := by nlinarith only [hx, hex]
  have hlog : 0 ≤ Real.log (x * Real.exp ε) := Real.log_nonneg hupper
  rw [lemma56_perron_near_error_tsum θ B τ ε hxp]
  calc
    _ ≤ ∑ n ∈ lemma56PerronNearIndices x ε, ‖lemma56PerronErrorTerm θ B x τ n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ lemma56PerronNearIndices x ε, Real.log (x * Real.exp ε) := by
      apply Finset.sum_le_sum
      intro n hn
      have hh := (Finset.mem_filter.mp hn).2
      have hnp : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hh.1
      have hb := (lemma56_perron_near_real_bounds hxp hh.1 hh.2).2
      exact (lemma56_perron_error_norm_le_mangoldt θ B τ hxp n).trans
        (ArithmeticFunction.vonMangoldt_le_log.trans (Real.log_le_log hnp hb.le))
    _ = ((lemma56PerronNearIndices x ε).card : ℝ) * Real.log (x * Real.exp ε) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (lemma56_perron_near_indices_card hxp hε) hlog

lemma lemma56_actual_perron_smoothing_error_bound {q : ℕ} [NeZero q]
    (θ : DirichletCharacter ℂ q) {B x ε : ℝ} (hB : 0 < B) (hx : 1 ≤ x)
    (hε : 0 ≤ ε) (hwide : 1 ≤ B * ε) (τ : ℝ) :
    ‖lemma56PerronMangoldtSum θ B x τ - lemma56SharpMangoldtSum θ x τ‖ ≤
      (x * (Real.exp ε - Real.exp (-ε)) + 2) * (Real.log x + ε) +
        lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹ * x ^ 2 *
          Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2) := by
  have hxp : 0 < x := by linarith only [hx]
  have hb := lemma56_actual_perron_smoothing_error_split θ hB hxp hε hwide τ
  apply hb.trans
  have hn := lemma56_perron_near_error_bound θ B τ hx hε
  rw [Real.log_mul hxp.ne' (Real.exp_pos ε).ne', Real.log_exp] at hn
  convert add_le_add_right hn
    (lemma56GaussianRightConstant * (Real.sqrt Real.pi)⁻¹ * x ^ 2 *
      Real.exp (2 / B ^ 2 - B ^ 2 * ε ^ 2 / 2)) using 1 <;> ring

end ZhangLS.Spec
