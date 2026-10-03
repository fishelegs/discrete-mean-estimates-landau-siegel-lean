import ZhangLS.Spec.Proposition71PrincipalUniformError
import ZhangLS.Spec.Lemma52

/-! Final assembly of the original uniform Proposition7.1 target from the
proved original principal reduction, actual contour errors and genuine
residue arithmetic. The O(E) constant precedes epsilon and all coefficient
sequences and genuine characters remain uniformly quantified. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped Classical
set_option maxHeartbeats 3500000

/-- Every fixed positive shift constant has the original uniform mean-value
formula; the O(E) constant is chosen before epsilon. -/
theorem proposition71_at_every_positive_constant {c : ℝ} (hc : 0<c) :
    Proposition71AtConstant c := by
  intro B₁ B₂ hB₁ hB₂
  obtain ⟨C,hC,Nr,hNr,hresidue⟩ := proposition71_actual_residue_mean_error hc
  refine ⟨C,hC,?_⟩
  intro ε hε
  obtain ⟨Nf,hNf,hfront⟩ := proposition71_original_principal_reduction c hc B₁ B₂ hB₁ hB₂
    (ε/2) (by positivity)
  obtain ⟨Nc,hNc,hcontour⟩ := proposition71_principal_residue_little_o hc B₁ B₂ hB₁ hB₂
    (ε/2) (by positivity)
  refine ⟨max Nf (max Nc Nr),hNf.trans (le_max_left _ _),?_⟩
  intro D hD χ hA a₁ a₂ ha₁ ha₂
  have hDf := (le_max_left _ _).trans hD
  have hDc := (le_max_left _ _).trans ((le_max_right _ _).trans hD)
  have hDr := (le_max_right _ _).trans ((le_max_right _ _).trans hD)
  have hf := hfront D hDf χ hA a₁ a₂ ha₁ ha₂
  have hc' := hcontour D hDc a₁ a₂ ha₁ ha₂
  have hr := hresidue D hDr a₁ a₂
  have he : lemma81ThetaOne χ c a₁ a₂-proposition71MainTerm D c a₁ a₂=
      (lemma81ThetaOne χ c a₁ a₂-proposition71PrincipalMean D c a₁ a₂)+
      (proposition71PrincipalMean D c a₁ a₂-proposition71ResidueArithmeticMean D c a₁ a₂)+
      (proposition71ResidueArithmeticMean D c a₁ a₂-proposition71MainTerm D c a₁ a₂) := by ring
  rw [he]
  apply (norm_add_le _ _).trans
  have hh := (norm_add_le _ _).trans (add_le_add hf hc')
  exact (add_le_add hh hr).trans_eq (by ring)

/-- The original Proposition7.1, with the original compatible c, strict
support, genuine characters, actual main coefficients and E, and unchanged
uniform quantifier order. -/
theorem proposition71_proved : Proposition71Target := by
  obtain ⟨c,hc,hcompatible,_⟩ := lemma52_proved
  exact ⟨c,hc,hcompatible,proposition71_at_every_positive_constant hc⟩

end ZhangLS.Spec
