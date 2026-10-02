import ZhangLS.Spec.Lemma32FiniteShift
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Set Filter
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_mellin_normalizing_factor :
    (2*Real.pi*I : ℂ)⁻¹*I = ((1/(2*Real.pi) : ℝ) : ℂ) := by
  have hp : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
  push_cast
  field_simp [hp,Complex.I_ne_zero]

lemma lemma32_actual_normalized_finite_shift {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (a T : ℝ) (ha : -1/2 < a) (han : a < 0) (hT : 0 < T) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*
      ((∫ t : ℝ in -T..T, lemma32CircleIntegrand χ (1+(t : ℂ)*I))-
        ∫ t : ℝ in -T..T, lemma32CircleIntegrand χ ((a : ℂ)+(t : ℂ)*I))+
    (2*Real.pi*I : ℂ)⁻¹*
      ((∫ x : ℝ in a..1, lemma32CircleIntegrand χ ((x : ℂ)-(T : ℂ)*I))-
        ∫ x : ℝ in a..1, lemma32CircleIntegrand χ ((x : ℂ)+(T : ℂ)*I)) =
      lemma32ActualResidue χ := by
  have hf := lemma32_actual_finite_rectangle_residue χ hD a T ha han hT
  have hn : (2*Real.pi*I : ℂ)⁻¹*
      lemma44GeneralRectangleBoundaryIntegral (lemma32CircleIntegrand χ) a 1 T =
        lemma32ActualResidue χ := by
    rw [hf,← mul_assoc,inv_mul_cancel₀ Complex.two_pi_I_ne_zero,one_mul]
  unfold lemma44GeneralRectangleBoundaryIntegral at hn
  simp only [Complex.ofReal_one] at hn
  calc
    _ = (2*Real.pi*I : ℂ)⁻¹*
      ((∫ x : ℝ in a..1, lemma32CircleIntegrand χ ((x : ℂ)-(T : ℂ)*I))-
        (∫ x : ℝ in a..1, lemma32CircleIntegrand χ ((x : ℂ)+(T : ℂ)*I))+
        I*(∫ t : ℝ in -T..T, lemma32CircleIntegrand χ (1+(t : ℂ)*I))-
        I*(∫ t : ℝ in -T..T, lemma32CircleIntegrand χ ((a : ℂ)+(t : ℂ)*I))) := by
      rw [← lemma32_mellin_normalizing_factor]
      ring
    _ = _ := hn

end ZhangLS.Spec
