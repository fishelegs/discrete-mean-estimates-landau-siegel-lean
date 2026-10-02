import ZhangLS.Spec.Lemma54

/-! Original closed-strip regression for Lemma 5.4(i).
The original disk estimate and complete Lemma54Target remain open. -/

open Complex MeasureTheory ZhangLS.Spec Set

set_option maxHeartbeats 1000000

example {B : ℝ} (hB : 0 < B) :
    IntegrableOn (fun x : ℝ => (1 + x ^ 3) * Real.exp (-(x ^ (1 / 2 : ℝ)) / B)) (Ioi 0) ∧
    (∫ x : ℝ in Ioi 0, (1 + x ^ 3) * Real.exp (-(x ^ (1 / 2 : ℝ)) / B)) =
      2 * B ^ 2 + 10080 * B ^ 8 :=
  ⟨lemma54_half_power_cubic_tail_integrable hB, lemma54_half_power_cubic_tail_integral hB⟩

example {B : ℝ} (hB : 200 ≤ B) :
    (∫ x : ℝ in Ioi 0, (1 + x ^ 3) * Real.exp (-((B * Real.log x / 100) ^ 2))) ≤
      200 * Real.sqrt Real.pi * Real.exp 1 := lemma54_log_cubic_tail_integral_bound hB

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {σ : ℝ}
    (hσ : 1 / 2 ≤ σ) (hσ2 : σ ≤ 2) :
    (∫ x : ℝ in Ioi 0, x ^ (σ + 1) * ‖deriv (deriv (lemma53PaperDelta D)) x‖) ≤
      lemma54MellinStripConstant * (Real.log D) ^ 3200 :=
  lemma54_actual_second_moment_uniform_polynomial hD hL hσ hσ2

-- Original actual Mellin integral, both closed endpoints and uniform quantifier order.
example : ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ,
    ∀ D : ℕ, D₀ ≤ D →
      AnalyticOnNhd ℂ (mellin (lemma53PaperDelta D)) {s : ℂ | 0 < s.re} ∧
        ∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
          ‖∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x‖ ≤
            C * (Real.log D) ^ c / ‖s‖ ^ 2 := lemma54_first_part_proved

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) (t : ℝ) :
    ‖lemma54PaperDeltaMellin D ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ≤
      lemma54MellinStripConstant * (Real.log D) ^ (3200 : ℝ) /
        ‖(1 / 2 : ℂ) + (t : ℂ) * I‖ ^ 2 :=
  lemma54_actual_mellin_closed_strip_bound hD hL (by norm_num) (by norm_num)

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) (t : ℝ) :
    ‖lemma54PaperDeltaMellin D ((2 : ℂ) + (t : ℂ) * I)‖ ≤
      lemma54MellinStripConstant * (Real.log D) ^ (3200 : ℝ) /
        ‖(2 : ℂ) + (t : ℂ) * I‖ ^ 2 :=
  lemma54_actual_mellin_closed_strip_bound hD hL (by norm_num) (by norm_num)

#print axioms lemma54_log_tail_moment_integrable
#print axioms lemma54_log_tail_moment_integral
#print axioms lemma54_log_cubic_tail_integral_bound
#print axioms lemma54_half_power_moment_integrable
#print axioms lemma54_half_power_moment_integral
#print axioms lemma54_half_power_cubic_tail_integral
#print axioms lemma54_actual_small_second_moment_bound
#print axioms lemma54_actual_large_moment_envelope
#print axioms lemma54_actual_large_second_moment_bound
#print axioms lemma54_actual_second_moment_uniform_polynomial
#print axioms lemma54_actual_mellin_closed_strip_bound
#print axioms lemma54_first_estimate_uniform_threshold
#print axioms lemma54_first_part_proved
