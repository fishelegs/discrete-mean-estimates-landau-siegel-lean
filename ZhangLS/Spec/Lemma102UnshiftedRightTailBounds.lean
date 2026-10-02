import ZhangLS.Spec.Lemma102CircleObjects
import ZhangLS.Spec.Lemma102UnshiftedRightLineBounds
import ZhangLS.Spec.Lemma84ContourKernelBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
set_option maxHeartbeats 1500000

lemma lemma102_unshifted_actual_integrand_eq_log_kernel {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) {b x : ℝ} (hx : 0 < x) (t : ℝ) :
    lemma84AnalyticCircleIntegrand χ (lemma83PaperBeta D c (j+1))
      (lemma83PaperBeta D c (j+2)) ((0:ℂ))
      (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x ((b:ℂ)+I*(t:ℂ)) =
      (dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ))+lemma83PaperBeta D c (j+1))*
        dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ))+lemma83PaperBeta D c (j+2))/
          dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ))))*
        lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r (1+((b:ℂ)+I*(t:ℂ)))*
          lemma84LogKernel b (Real.log x) ((0:ℂ)).im t := by
  unfold lemma84AnalyticCircleIntegrand
  rw [mul_div_assoc,lemma84_original_kernel_eq_log hx b _ (by simp)]
    <;> simp only [Complex.zero_im]

lemma lemma102_unshifted_actual_integrand_right_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) {b x : ℝ} (hb : 0 < b) (hx : 0 < x) (t : ℝ) :
    ‖lemma84AnalyticCircleIntegrand χ (lemma83PaperBeta D c (j+1))
      (lemma83PaperBeta D c (j+2)) ((0:ℂ))
      (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x ((b:ℂ)+I*(t:ℂ))‖ ≤
        lemma102_unshiftedRightLineMajorant b d r * ‖lemma84LogKernel b (Real.log x) ((0:ℂ)).im t‖ := by
  rw [lemma102_unshifted_actual_integrand_eq_log_kernel χ c j d r hx t,norm_mul]
  exact mul_le_mul_of_nonneg_right (lemma102_unshifted_actual_right_line_numerator_bound χ c j d r hb t) (norm_nonneg _)

/-- The true upper and lower initial-line tails, with all integral hypotheses proved. -/
lemma lemma102_unshifted_actual_right_tails {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (c : ℝ) (j : Fin 3) (d r : ℕ) {b x H : ℝ}
    (hb : 0 < b) (hx : 0 < x) (hH : 0 < H)
    (hm : |((0:ℂ)).im| ≤ H/2) :
    let f := fun t : ℝ => lemma84AnalyticCircleIntegrand χ
      (lemma83PaperBeta D c (j+1)) (lemma83PaperBeta D c (j+2)) ((0:ℂ))
      (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x ((b:ℂ)+I*(t:ℂ))
    ‖∫ t : ℝ in Ioi H, f t‖ + ‖∫ t : ℝ in Iic (-H), f t‖ ≤
      8*lemma102_unshiftedRightLineMajorant b d r*Real.exp (b*Real.log x)/H := by
  dsimp only
  let f := fun t : ℝ => lemma84AnalyticCircleIntegrand χ
    (lemma83PaperBeta D c (j+1)) (lemma83PaperBeta D c (j+2)) ((0:ℂ))
    (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x ((b:ℂ)+I*(t:ℂ))
  let K := lemma84LogKernel b (Real.log x) ((0:ℂ)).im
  let M := lemma102_unshiftedRightLineMajorant b d r
  have hM : 0 ≤ M := lemma102_unshifted_right_line_majorant_nonneg hb d r
  have hi : Integrable f := lemma102_unshifted_actual_right_line_integrable χ hD c j d r hb hx
  have hKi : Integrable K := lemma84_log_kernel_integrable hb _ _
  have hbound (S : Set ℝ) (hS : MeasurableSet S) :
      ‖∫ t : ℝ in S, f t‖ ≤ M*(∫ t : ℝ in S, ‖K t‖) := by
    apply (norm_integral_le_integral_norm _).trans
    have hh := setIntegral_mono_on hi.norm.integrableOn (hKi.norm.const_mul M).integrableOn hS
      (fun t _ => lemma102_unshifted_actual_integrand_right_bound χ c j d r hb hx t)
    simpa only [integral_const_mul] using hh
  have hu := (hbound (Ioi H) measurableSet_Ioi).trans
    (mul_le_mul_of_nonneg_left (lemma84_log_kernel_positive_tail hb hH (Real.log x) _ hm) hM)
  have hl := (hbound (Iic (-H)) measurableSet_Iic).trans
    (mul_le_mul_of_nonneg_left (lemma84_log_kernel_negative_tail hb hH (Real.log x) _ hm) hM)
  have hh := add_le_add hu hl
  exact hh.trans_eq (by dsimp [M]; ring)

end ZhangLS.Spec
