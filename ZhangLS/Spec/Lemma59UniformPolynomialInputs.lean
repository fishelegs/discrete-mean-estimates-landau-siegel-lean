import ZhangLS.Spec.Lemma59ExtendedPolynomialLog

/-! # Auxiliary inputs for Lemma 5.9

The actual original closed strip, actual coefficients and actual L-function
are retained. The full `Lemma59Target` quotient is proved in `Lemma59.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set Metric MeasureTheory Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

theorem lemma59_uniform_extended_F_inputs :
    ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
      (ψ : DirichletCharacter ℂ p), D₀ ≤ D → Lemma23InPsi1 χ ψ →
      ∀ {s : ℂ}, Lemma59InRegion D s →
        (lemma23PaperL D ^ 88)⁻¹ ≤ ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ ∧
        ‖lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ ≤ lemma23PaperL D ^ 88 ∧
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s ≠ 0 ∧
        ‖logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) s‖ ≤ 140800 * lemma23PaperL D := by
  refine ⟨lemma23SectionFourModulusThreshold, ?_⟩
  intro D p _ χ ψ hD hψ s hs
  have hparam := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hL : 100 ≤ lemma23PaperL D := by
    have hh := Real.log_le_self (by linarith only [hparam.1] : 0 ≤ lemma23PaperL D)
    linarith only [hh, hparam.2]
  have hs2 := (lemma59_original_region_in_extended hL hs).1
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hparam.2]) (by linarith only [hL])
  have hs1 := lemma59_extended_disk_subset_omega1 hL hparam.2 hs2 (Metric.mem_ball_self hR)
  have hnorm := lemma59_extended_F_two_sided χ ψ s hL hψ.2 hs1
  exact ⟨hnorm.1, hnorm.2, lemma59_extended_F_ne_zero χ ψ s hL hψ.2 hs1,
    lemma59_extended_F_logDeriv_bound χ ψ s hL hparam.2 hψ.2 hs2⟩

end ZhangLS.Spec
