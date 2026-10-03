import ZhangLS.Spec.ActualPhaseRectangle
import ZhangLS.Spec.Proposition21

/-! Named regressions for the actual source objects and strict endpoints. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex ComplexConjugate Set
open scoped Real Classical

theorem actualPhase_regression_source_shifts (D : ℕ) (c : ℝ) :
    lemma52PaperBetaThree D c = lemma52PaperBetaOne D c + lemma52PaperBetaTwo D c := by
  unfold lemma52PaperBetaOne lemma52PaperBetaTwo lemma52PaperBetaThree
    lemma23PaperOffsetOne lemma23PaperOffsetTwo lemma23PaperOffsetThree
  push_cast
  ring

theorem actualPhase_regression_cstar {p : ℕ} [NeZero p]
    (D : ℕ) (c : ℝ) (ψ : DirichletCharacter ℂ p) (Y f : ℂ → ℂ) (ρ : ℂ) :
    actualPhaseResidue D c ψ Y f ρ =
      (-I * (lemma23DirichletNormalizedM ψ Y (ρ+lemma52PaperBetaOne D c) *
        lemma23DirichletNormalizedM ψ Y (ρ+lemma52PaperBetaTwo D c) *
        lemma23DirichletNormalizedM ψ Y (ρ+lemma52PaperBetaThree D c)) /
        deriv (lemma23DirichletNormalizedM ψ Y) ρ) * f ρ * lemma81Omega D ρ := by
  unfold actualPhaseResidue lemma23ActualCoefficient lemma23ComplexCoefficient
    criticalLinePoint lemma52PaperBetaOne lemma52PaperBetaTwo lemma52PaperBetaThree
  ring

theorem actualPhase_regression_upper_zero_endpoint {p : ℕ} [NeZero p]
    (D : ℕ) (ψ : DirichletCharacter ℂ p) (hψ : ψ ≠ 1) :
    (⟨1/2,(lemma23PaperCenter D).im+lemma23PaperL D^405⟩ : ℂ) ∉
      lemma81ZeroFinset D ψ := by
  intro hm
  have hh := ((lemma81_mem_original_zero_finset ψ hψ _).mp hm).1.2
  change |((lemma23PaperCenter D).im+lemma23PaperL D^405)-(lemma23PaperCenter D).im| <
    lemma23PaperL D^405 at hh
  rw [add_sub_cancel_left] at hh
  exact (not_lt_of_ge (le_abs_self _)) hh

theorem actualPhase_regression_lower_zero_endpoint {p : ℕ} [NeZero p]
    (D : ℕ) (ψ : DirichletCharacter ℂ p) (hψ : ψ ≠ 1) :
    (⟨1/2,(lemma23PaperCenter D).im-lemma23PaperL D^405⟩ : ℂ) ∉
      lemma81ZeroFinset D ψ := by
  intro hm
  have hh := ((lemma81_mem_original_zero_finset ψ hψ _).mp hm).1.2
  change |((lemma23PaperCenter D).im-lemma23PaperL D^405)-(lemma23PaperCenter D).im| <
    lemma23PaperL D^405 at hh
  rw [sub_sub_cancel_left,abs_neg] at hh
  exact (not_lt_of_ge (le_abs_self _)) hh

theorem actualPhase_regression_original_polynomial_endpoint (D n : ℕ)
    (hn : (n : ℝ) = lemma81Cutoff D) : n ∉ lemma81PolynomialIndices D := by
  intro hm
  have hh := (Finset.mem_filter.mp hm).2
  rw [hn] at hh
  exact (lt_irrefl _) hh

theorem actualPhase_regression_psi1 {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma81GoodFamily χ = proposition21ActualPsi1Family χ := by
  ext ψ
  rcases ψ with ⟨p,ψ⟩
  exact (lemma81_mem_good_family χ ⟨p,ψ⟩).trans
    (proposition21_mem_psi1 χ p ψ).symm

theorem actualPhase_regression_psi2 {D : ℕ} (χ : RealPrimitiveCharacter D) :
    (proposition21ActualPsi2Family χ : Set (lemma33CharacterIndex D)) =
      (lemma33ActualFamily D : Set (lemma33CharacterIndex D)) \
        (lemma81GoodFamily χ : Set (lemma33CharacterIndex D)) := by
  rw [actualPhase_regression_psi1]
  exact proposition21_psi2_is_complement χ

theorem actualPhase_regression_normalizer {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) (a b : ℕ → ℂ) :
    actualPhaseCOne χ c Y a b =
      (∑ ψ ∈ lemma81GoodFamily χ, actualPhaseCZeroSum χ c ψ.2 (Y ψ) a b) /
        ((((6/Real.pi^2) * realLDerivAtOne χ^2 *
          ∏ p ∈ D.primeFactors, (p : ℝ)/((p : ℝ)+1)) * lemma33ActualPrimeMass D : ℝ) : ℂ) := rfl

theorem actualPhase_regression_T_conjugation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (a j : ℕ → ℂ) {s : ℂ} (hs : s.re = 1/2) :
    actualPhaseTTest χ ψ a j s =
      actualPhaseRoot χ ψ * lemma81Polynomial D a ψ s *
        conj (lemma81Polynomial D j ψ s) :=
  actualPhase_TTest_on_critical_line χ ψ a j hs

end ZhangLS.Spec
