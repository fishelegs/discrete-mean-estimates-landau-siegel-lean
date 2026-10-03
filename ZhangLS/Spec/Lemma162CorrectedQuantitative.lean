import ZhangLS.Spec.Lemma162CorrectedCenter
import ZhangLS.Spec.Lemma162CauchyBounds
import ZhangLS.Spec.Lemma162ActualOldValueWitness

/-! Completed bounded quantitative repair component. This carries the same
actual shifted Dirichlet series through the center and thin-strip estimates;
it makes no claim about Mellin inversion, residues, unsmoothing or o(p). -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 1500000

/-- Exact stronger center error plus the printed O(L⁻⁴) rate, for corrected V. -/
theorem lemma162_paper_corrected_center_four (c : ℝ) (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
      ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
        ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c)
          (lemma162PaperShift D c j) 1-lemma162CorrectedCenterMain χ‖≤
            (lemma162CorrectedCenterAlphaConstant*Real.pi)/lemma23PaperL D^4 := by
  obtain ⟨D₀,hD₀,hsection,h⟩ := lemma162_paper_corrected_center c hc
  refine ⟨D₀,hD₀,hsection,?_⟩
  intro D hD χ j
  have hL := (lemma44_parameters_at_explicit_threshold (hsection.trans hD)).1
  apply (h D hD χ j).trans
  exact div_le_div_of_nonneg_left
    (mul_pos lemma162_corrected_center_alpha_constant_pos Real.pi_pos).le
    (pow_pos (by linarith : 0<lemma23PaperL D) 4)
    (pow_le_pow_right₀ (by linarith : 1≤lemma23PaperL D) (by norm_num : (4:ℕ)≤9))

/-- A single threshold for the actual identity, explicit strip bound, absolute
Cauchy disk, all derivative orders, and the finite-shift center comparison.
The constants are declared before c′ and independent of D, χ, and j. -/
def Lemma162CorrectedQuantitativeAt (c : ℝ) : Prop :=
  ∃ D₀ : ℕ, 3≤D₀ ∧ lemma23SectionFourModulusThreshold≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, ∀ j : Fin 2,
      Lemma162ShiftedContinuation χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)
        (lemma162GeneralMEulerProduct χ (lemma52PaperBetaOne D c))
        (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j)) ∧
      (∀ s : ℂ, 9/10≤s.re → 1-(Real.log D)⁻¹≤s.re →
        ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) s‖≤
          lemma162ThinStripConstant*(1+Real.log (Real.log D))^18) ∧
      (∀ s : ℂ, ‖s-1‖≤(10*lemma23PaperL D)⁻¹ →
        ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) s‖≤
          lemma162SectorConstant) ∧
      (∀ n : ℕ, ‖iteratedDeriv n (lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c)
        (lemma162PaperShift D c j)) 1‖≤n.factorial*lemma162SectorConstant*(10*lemma23PaperL D)^n) ∧
      ‖lemma162CorrectedEulerProduct χ (lemma52PaperBetaOne D c) (lemma162PaperShift D c j) 1-
        lemma162CorrectedCenterMain χ‖≤(lemma162CorrectedCenterAlphaConstant*Real.pi)/lemma23PaperL D^9

theorem lemma162_corrected_quantitative_proved (c : ℝ) (hc : 0<c) :
    Lemma162CorrectedQuantitativeAt c := by
  obtain ⟨D₁,hD₁,hactual⟩ := lemma162_paper_corrected_analytic_bridge c hc
  obtain ⟨D₂,hD₂,hs₂,hstrip⟩ := lemma162_paper_thin_strip_bound c hc
  obtain ⟨D₃,hD₃,hs₃,hdisk⟩ := lemma162_paper_disk_bound c hc
  obtain ⟨D₄,hD₄,hs₄,hderiv⟩ := lemma162_paper_cauchy_bounds c hc
  obtain ⟨D₅,hD₅,hs₅,hcenter⟩ := lemma162_paper_corrected_center c hc
  refine ⟨max D₁ (max D₂ (max D₃ (max D₄ D₅))),?_,?_,?_⟩
  · exact hD₂.trans ((le_max_left _ _).trans (le_max_right _ _))
  · exact hs₂.trans ((le_max_left _ _).trans (le_max_right _ _))
  · intro D hD χ j
    have h1 : D₁≤D := (le_max_left _ _).trans hD
    have ht : max D₂ (max D₃ (max D₄ D₅))≤D := (le_max_right _ _).trans hD
    have h2 : D₂≤D := (le_max_left _ _).trans ht
    have hu : max D₃ (max D₄ D₅)≤D := (le_max_right _ _).trans ht
    have h3 : D₃≤D := (le_max_left _ _).trans hu
    have hv : max D₄ D₅≤D := (le_max_right _ _).trans hu
    have h4 : D₄≤D := (le_max_left _ _).trans hv
    have h5 : D₅≤D := (le_max_right _ _).trans hv
    exact ⟨(hactual D h1 χ j).1,hstrip D h2 χ j,(hdisk D h3 χ j).2,
      hderiv D h4 χ j,hcenter D h5 χ j⟩

/-- The repair accepts the very same c′ furnished by the original Lemma5.2. -/
theorem lemma162_corrected_quantitative_shared_constant :
    ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧ Lemma162CorrectedQuantitativeAt c := by
  obtain ⟨c,hc,hcompatible,C,hC,D₀,hrest⟩ := lemma52_proved
  exact ⟨c,hc,hcompatible,lemma162_corrected_quantitative_proved c hc⟩

end ZhangLS.Spec
