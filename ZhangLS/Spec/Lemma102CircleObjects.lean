import ZhangLS.Spec.Lemma102Perron
import ZhangLS.Spec.Lemma84ArithmeticCircle
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

noncomputable def lemma102PaperCircle {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) (x : ℝ) : ℂ :=
  (2*Real.pi*I:ℂ)⁻¹ * circleIntegral
    (lemma84AnalyticCircleIntegrand χ (lemma83PaperBeta D c (j+1))
      (lemma83PaperBeta D c (j+2)) 0
      (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x)
    0 (5*lemma44PaperAlpha D)

lemma lemma102_zero_shift_norm {D : ℕ} (hα : 0<lemma44PaperAlpha D) :
    0≤‖(0:ℂ)‖ ∧ ‖(0:ℂ)‖≤3*lemma44PaperAlpha D := by
  simp only [norm_zero]
  constructor
  · exact le_rfl
  · positivity

end ZhangLS.Spec
