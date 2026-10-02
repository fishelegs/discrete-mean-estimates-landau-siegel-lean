import ZhangLS.Spec.Lemma171ContourInfinite
import ZhangLS.Spec.Lemma171LeftAbsorption
import ZhangLS.Spec.Lemma171GaussianUnsmoothing

/-!
# Complete original Lemma 17.1

The actual strict short harmonic sum is a+o(1), uniformly over real primitive
characters satisfying the original normalized assumption (A). The proof combines
proved unsmoothing, the actual infinite Gaussian contour shift, the exact residue
with a uniform error, and a uniform bound for the actual left integral.
All modulus thresholds are chosen before the modulus and character.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

lemma lemma171_uniform_left_integral (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
      ∀ χ : RealPrimitiveCharacter D, ‖lemma171VerticalIntegral χ (-1/4)‖ < ε := by
  obtain ⟨D₀,hD₀,hsmall⟩ := lemma171_left_majorant_uniform ε hε
  refine ⟨D₀,hD₀,?_⟩
  intro D hD χ
  exact (lemma171_left_vertical_norm_le_majorant χ (by omega)).trans_lt (hsmall D hD)

/-- Zhang's original Lemma 17.1, retaining n<D⁴ and uniform o(1) under (A). -/
theorem lemma171_proved : Lemma171Target := by
  intro ε hε
  have hε3 : 0 < ε/3 := by positivity
  obtain ⟨D₁,hD₁,hunsmooth⟩ := lemma171_unsmoothing_uniform (ε/3) hε3
  obtain ⟨D₂,hD₂,hresidue⟩ := lemma171_uniform_residue_error (ε/3) hε3
  obtain ⟨D₃,hD₃,hleft⟩ := lemma171_uniform_left_integral (ε/3) hε3
  refine ⟨max D₁ (max D₂ D₃),hD₁.trans (le_max_left _ _),?_⟩
  intro D hD χ hA
  have hd1 : D₁ ≤ D := (le_max_left _ _).trans hD
  have hd2 : D₂ ≤ D := (le_max_left D₂ D₃).trans ((le_max_right _ _).trans hD)
  have hd3 : D₃ ≤ D := (le_max_right D₂ D₃).trans ((le_max_right _ _).trans hD)
  have hm := hunsmooth D hd1 χ hA
  have hr := hresidue D hd2 χ hA
  have hl := hleft D hd3 χ
  have hs := lemma171_smoothed_sum_eq_residue_add_left χ (by omega : 1 < D)
  have he : (lemma171ShortHarmonicSum χ : ℂ)-(lemma171MainTerm χ : ℂ) =
      ((lemma171ShortHarmonicSum χ-lemma171SmoothedSum χ : ℝ) : ℂ) +
        (lemma171ActualResidue χ-(lemma171MainTerm χ : ℂ))+
          lemma171VerticalIntegral χ (-1/4) := by
    push_cast
    rw [hs]
    ring
  have hm' : ‖((lemma171ShortHarmonicSum χ-lemma171SmoothedSum χ : ℝ) : ℂ)‖ < ε/3 := by
    simpa only [Complex.norm_real,Real.norm_eq_abs,abs_sub_comm] using hm
  calc
    |lemma171Error χ| = ‖(lemma171ShortHarmonicSum χ : ℂ)-(lemma171MainTerm χ : ℂ)‖ := by
      rw [← Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]
      rfl
    _ ≤ ‖((lemma171ShortHarmonicSum χ-lemma171SmoothedSum χ : ℝ) : ℂ)‖ +
        ‖lemma171ActualResidue χ-(lemma171MainTerm χ : ℂ)‖+
          ‖lemma171VerticalIntegral χ (-1/4)‖ := by rw [he]; exact norm_add₃_le
    _ < ε := by linarith

/-- Fully expanded original-paper statement, with actual coefficient and constant. -/
theorem lemma171_original_uniform :
    ∀ ε : ℝ, 0 < ε → ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
        NormalizedAssumptionA χ →
          |(∑ n ∈ Finset.Ico 1 (D^4), (lemma23NuArithmeticFunction χ n).re^2/(n : ℝ)) -
            (6/Real.pi^2)*realLDerivAtOne χ^2*
              ∏ p ∈ D.primeFactors, (p : ℝ)/((p : ℝ)+1)| < ε :=
  lemma171_target_iff_paper.mp lemma171_proved

end ZhangLS.Spec
