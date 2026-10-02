import ZhangLS.Spec.Lemma54

/-! Original full Lemma 5.4: actual Mellin integral, both original domains,
one common absolute constant and one threshold chosen before all D and s. -/

open Complex MeasureTheory ZhangLS.Spec Set

set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

example : (∫ x : ℝ in Ioc 0 1, x ^ (-(1 : ℝ) / 2)) = 2 :=
  lemma54_half_inverse_unit_integral

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖∫ x : ℝ in Ioc 0 1, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x‖ ≤
      2 * lemma54NearZeroConstant * Real.exp (-((Real.log D) ^ 10) / 2) :=
  lemma54_actual_near_zero_mellin_bound hD hL hs

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖∫ x : ℝ in Ioi (((Real.log D) ^ 519) ^ (51 / 50 : ℝ)),
      (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x‖ ≤
      lemma54LargeExteriorConstant * (Real.log D) ^ 3200 * Real.exp (-((Real.log D) ^ 10) / 2) :=
  lemma54_actual_large_exterior_mellin_bound hD hL hs

-- The entire original disk, using the actual full positive-axis integral.
example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {s : ℂ}
    (hs : ‖s - 1‖ < 10 * lemma44PaperAlpha D) :
    ‖(∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x) - 1‖ ≤
      10403 * lemma44PaperAlpha D * Real.log (Real.log D) +
        lemma54DiskTailConstant * (Real.log D) ^ 3200 * Real.exp (-((Real.log D) ^ 10) / 2) :=
  lemma54_actual_mellin_disk_budget hD hL hs

-- The original quantifier order, actual analytic function, both closed
-- strip endpoints and the entire original open radius-10-alpha disk.
example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ,
    ∀ D : ℕ, D₀ ≤ D →
      AnalyticOnNhd ℂ (mellin (lemma53PaperDelta D)) {s : ℂ | 0 < s.re} ∧
        (∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
          ‖∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x‖ ≤
            C * (Real.log D) ^ c / ‖s‖ ^ 2) ∧
        (∀ s : ℂ, ‖s - 1‖ < 10 * lemma44PaperAlpha D →
          ‖(∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x) - 1‖ ≤
            C * lemma44PaperAlpha D * Real.log (Real.log D)) := lemma54_proved

example : ∃ D₀ : ℕ, Lemma54AtConstants lemma54Constant 3200 D₀ := lemma54_uniform_constants

-- Specializing the proved uniform disk threshold at the actual center s=1.
example : ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    ‖lemma54PaperDeltaMellin D 1 - 1‖ ≤ lemma54DiskConstant * lemma44PaperAlpha D * Real.log (Real.log D) := by
  obtain ⟨D₀, hD₀⟩ := lemma54_actual_mellin_disk_uniform_threshold
  refine ⟨D₀, ?_⟩
  intro D hD
  have ht := hD₀ D hD
  apply ht.2.2 1
  have ha := (lemma54_disk_alpha_small ht.2.1).1
  simpa only [sub_self, norm_zero] using mul_pos (by norm_num : (0 : ℝ) < 10) ha

#print axioms lemma54_actual_gaussian_near_zero
#print axioms lemma54_actual_delta_small_gaussian_bound
#print axioms lemma54_disk_near_zero_weight
#print axioms lemma54_half_inverse_unit_integrable
#print axioms lemma54_half_inverse_unit_integral
#print axioms lemma54_actual_near_zero_mellin_bound
#print axioms lemma54_actual_small_exterior_mellin_bound
#print axioms lemma54_large_log_damping
#print axioms lemma54_large_power_damping
#print axioms lemma54_large_log_tail_split
#print axioms lemma54_large_half_power_tail_split
#print axioms lemma54_actual_large_exterior_mellin_bound
#print axioms lemma54_window_subset_small_middle
#print axioms lemma54_actual_mellin_disk_budget
#print axioms lemma54_disk_exponential_absorption_threshold
#print axioms lemma54_actual_mellin_disk_uniform_threshold
#print axioms lemma54_constant_pos
#print axioms lemma54_uniform_constants
#print axioms lemma54_proved
