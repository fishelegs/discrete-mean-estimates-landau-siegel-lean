import ZhangLS.Spec.Lemma102ArithmeticCircle
import ZhangLS.Spec.Lemma84CircleBudget
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

/-- Sharp proved circle budget: the Taylor contribution has its genuine Π
factor, while the arithmetic perturbation saves one further power of L. -/
lemma lemma102_paper_circle_error_with_pi {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ)
    (hC : lemma58ErrorConstant ≤ lemma23PaperL D) {c : ℝ} (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (j : Fin 3) (d r K : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ))
    (hK : 3*lemma83FiniteShiftWeight ≤ (K : ℝ)) {x : ℝ}
    (hxT : lemma56PaperT D ≤ x) (hxP : x < lemma23PaperP D) :
    ‖lemma102PaperCircle χ c j d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j x‖ ≤
      lemma84TaylorCircleConstant*lemma23PaperL D^(-6 : ℤ)*‖lemma83Pi χ d r‖ +
        lemma84CorrectionCircleConstant*lemma23PaperL D^(-7 : ℤ)*
          (1+9*Real.log (lemma23PaperL D))^(K+2) := by
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 2 ≤ lemma23PaperL D := by
    change 2 ≤ Real.log (D:ℝ)
    linarith [lemma57_log_ge_ten_million hDN]
  have hX : 0 ≤ (1+9*Real.log (lemma23PaperL D))^(K+2) := by
    positivity [Real.log_nonneg (by linarith only [hL] : 1 ≤ lemma23PaperL D)]
  have hb := lemma84_circle_budget_algebra (lemma23PaperL D) lemma58ErrorConstant
    lemma83TotalShiftConstant ‖LDerivAtOne χ‖ ‖lemma83Pi χ d r‖
    ((1+9*Real.log (lemma23PaperL D))^(K+2)) (by linarith only [hL])
    lemma58_error_constant_pos.le lemma83_total_shift_constant_pos.le hX
    (lemma84_actual_derivative_norm_upper χ hD hL)
  have he : lemma44PaperAlpha D = Real.pi/lemma23PaperL D^9 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
  apply (lemma102_paper_circle_error_explicit χ hDN hA hC hc hsmall j d r K hd hr hcut hK hxT hxP).trans
  simpa only [lemma84CorrectionError,he,lemma84TaylorCircleConstant,lemma84CorrectionCircleConstant] using hb

end ZhangLS.Spec
