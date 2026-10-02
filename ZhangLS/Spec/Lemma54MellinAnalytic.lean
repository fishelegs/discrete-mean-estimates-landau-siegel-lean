import ZhangLS.Spec.Lemma54MellinDecay
import ZhangLS.Spec.Lemma54ActualDerivatives

/-! # The actual Mellin transform is analytic on the full right half-plane -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

noncomputable def lemma54PaperDeltaMellin (D : ℕ) : ℂ → ℂ :=
  mellin (lemma53PaperDelta D)

theorem lemma54_actual_delta_locallyIntegrableOn {D : ℕ} (hD : 1 < D) :
    LocallyIntegrableOn (lemma53PaperDelta D) (Ioi 0) :=
  (lemma54_actual_delta_continuousOn hD).locallyIntegrableOn measurableSet_Ioi

theorem lemma54_mellin_convergent {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    MellinConvergent (lemma53PaperDelta D) s := by
  apply mellinConvergent_of_isBigO_rpow (lemma54_actual_delta_locallyIntegrableOn hD)
    (lemma54_actual_delta_isBigO_atTop hD hL (a := s.re + 1) (by linarith))
    (by linarith) (lemma54_actual_delta_isBigO_at_zero hD) hs

theorem lemma54_mellin_differentiableAt {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 < s.re) :
    DifferentiableAt ℂ (lemma54PaperDeltaMellin D) s := by
  exact mellin_differentiableAt_of_isBigO_rpow
    (lemma54_actual_delta_locallyIntegrableOn hD)
    (lemma54_actual_delta_isBigO_atTop hD hL (a := s.re + 1) (by linarith))
    (by linarith) (lemma54_actual_delta_isBigO_at_zero hD) hs

theorem lemma54_mellin_analyticOnNhd {D : ℕ} (hD : 1 < D)
    (hL : 2000 ≤ lemma23PaperL D) :
    AnalyticOnNhd ℂ (lemma54PaperDeltaMellin D) {s : ℂ | 0 < s.re} := by
  have hd : DifferentiableOn ℂ (lemma54PaperDeltaMellin D) {s : ℂ | 0 < s.re} := by
    intro s hs
    exact (lemma54_mellin_differentiableAt hD hL hs).differentiableWithinAt
  exact hd.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

theorem lemma54_mellin_analytic_uniform_threshold :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      (∀ s : ℂ, 0 < s.re → MellinConvergent (lemma53PaperDelta D) s) ∧
        AnalyticOnNhd ℂ (lemma54PaperDeltaMellin D) {s : ℂ | 0 < s.re} := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (ht.eventually (eventually_ge_atTop 2000))
  refine ⟨max N 2, ?_⟩
  intro D hD
  have hD' : 1 < D := lt_of_lt_of_le (by norm_num : 1 < 2) ((le_max_right N 2).trans hD)
  have hL := hN D ((le_max_left N 2).trans hD)
  exact ⟨fun s hs => lemma54_mellin_convergent hD' hL hs, lemma54_mellin_analyticOnNhd hD' hL⟩

end ZhangLS.Spec
