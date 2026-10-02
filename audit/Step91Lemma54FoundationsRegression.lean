import ZhangLS.Spec.Lemma54

/-! Actual Mellin and derivative interfaces for the original Lemma 5.4.
Both quantitative conclusions in Lemma54Target remain open. -/

open Complex MeasureTheory ZhangLS.Spec Filter Set Asymptotics
open scoped Topology

set_option maxHeartbeats 1000000

example (D : ℕ) (s : ℂ) : lemma54PaperDeltaMellin D s =
    ∫ x : ℝ in Ioi 0, (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x := rfl

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (x : ℂ) ^ (s - 1) * lemma53PaperDelta D x) (Ioi 0) :=
  lemma54_mellin_convergent hD hL hs

-- A single natural threshold covers the entire open right half-plane.
example : ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    (∀ s : ℂ, 0 < s.re → MellinConvergent (lemma53PaperDelta D) s) ∧
      AnalyticOnNhd ℂ (mellin (lemma53PaperDelta D)) {s : ℂ | 0 < s.re} :=
  lemma54_mellin_analytic_uniform_threshold

example {D : ℕ} (hD : 1 < D) (hL : 2000 ≤ Real.log D) {a : ℝ} (ha : 0 < a) :
    lemma53PaperDelta D =O[atTop] (fun x : ℝ => x ^ (-a)) :=
  lemma54_actual_delta_isBigO_atTop hD hL ha

example {D : ℕ} (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    deriv (deriv (lemma53PaperDelta D)) x =
      -(4 * Real.pi ^ 2 : ℂ) *
        (∫ u : ℝ, ((Real.exp u : ℂ) - 1) ^ 2 *
          Complex.exp (lemma23PaperCenter D * (u : ℂ) -
            (((Real.log D) ^ 400 : ℝ) : ℂ) ^ 2 * (u : ℂ) ^ 2 -
              (2 * Real.pi : ℂ) * I * (x : ℂ) * (Complex.exp (u : ℂ) - 1))) :=
  lemma54_actual_delta_second_deriv_formula hD hx

example {D : ℕ} (hD : 1 < D) (hB : 1 ≤ (Real.log D) ^ 400) {x : ℝ} (hx : 0 < x) :
    ‖deriv (lemma53PaperDelta D) x‖ ≤
      4 * Real.pi * Real.sqrt Real.pi * Real.exp 1 / (Real.log D) ^ 400 ∧
    ‖deriv (deriv (lemma53PaperDelta D)) x‖ ≤
      16 * Real.pi ^ 2 * Real.sqrt Real.pi * Real.exp 2 / (Real.log D) ^ 400 :=
  ⟨lemma54_actual_first_deriv_norm_bound hD hB hx,
    lemma54_actual_second_deriv_norm_bound hD hB hx⟩

-- The open target preserves the complete closed strip, original radius,
-- actual Mellin transform, and constants uniform before all D and s.
example : Lemma54Target ↔
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ,
      ∀ D : ℕ, D₀ ≤ D →
        AnalyticOnNhd ℂ (mellin (lemma53PaperDelta D)) {s : ℂ | 0 < s.re} ∧
          (∀ s : ℂ, 1 / 2 ≤ s.re → s.re ≤ 2 →
            ‖mellin (lemma53PaperDelta D) s‖ ≤ C * (Real.log D) ^ c / ‖s‖ ^ 2) ∧
          (∀ s : ℂ, ‖s - 1‖ < 10 * lemma44PaperAlpha D →
            ‖mellin (lemma53PaperDelta D) s - 1‖ ≤
              C * lemma44PaperAlpha D * Real.log (Real.log D)) := Iff.rfl

#print axioms lemma54_first_kernel_integrable
#print axioms lemma54_second_kernel_integrable
#print axioms lemma54_oscillatory_hasDerivAt
#print axioms lemma54_first_integral_hasDerivAt
#print axioms lemma54_actual_delta_first_deriv_formula
#print axioms lemma54_actual_delta_second_deriv_formula
#print axioms lemma54_actual_delta_isBigO_atTop
#print axioms lemma54_actual_delta_isBigO_at_zero
#print axioms lemma54_actual_delta_continuousOn
#print axioms lemma54_mellin_convergent
#print axioms lemma54_mellin_differentiableAt
#print axioms lemma54_mellin_analyticOnNhd
#print axioms lemma54_mellin_analytic_uniform_threshold
#print axioms lemma54_actual_first_deriv_norm_bound
#print axioms lemma54_actual_second_deriv_norm_bound
