import ZhangLS.Spec.Lemma102CircleObjects
import ZhangLS.Spec.Lemma102CircleApproximation
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Metric
set_option maxHeartbeats 2000000

/-- All source arithmetic and analytic data instantiated. Identification with the sum still needs the contour shift/Perron estimate;
achieving the original final exponent also requires resolving the explicit Π
factor in this quantitative error. -/
lemma lemma102_paper_circle_error_explicit {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ)
    (hC : lemma58ErrorConstant ≤ lemma23PaperL D) {c : ℝ} (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (j : Fin 3) (d r K : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ))
    (hK : 3*lemma83FiniteShiftWeight ≤ (K : ℝ)) {x : ℝ}
    (hxT : lemma56PaperT D ≤ x) (hxP : x < lemma23PaperP D) :
    ‖lemma102PaperCircle χ c j d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma102LogMain D c j x‖ ≤
      (5*lemma44PaperAlpha D)*(Real.exp (5*Real.pi)/(4*lemma44PaperAlpha D^2))*
        ((8*lemma58ErrorConstant)*lemma23PaperL D^(-15 : ℤ)*
            (‖lemma83Pi χ d r‖+lemma84CorrectionError D K) +
          (13*‖LDerivAtOne χ‖*lemma44PaperAlpha D)*lemma84CorrectionError D K) := by
  have hL : 100 ≤ lemma23PaperL D := by
    change 100 ≤ Real.log (D:ℝ)
    linarith [lemma57_log_ge_ten_million hDN]
  have hLp : 0 < lemma23PaperL D := by linarith
  have hα := lemma83_alpha_small hL
  have hT : 1 ≤ lemma56PaperT D := by
    unfold lemma56PaperT
    apply Real.one_le_exp_iff.mpr
    exact Real.rpow_nonneg hLp.le _
  have hx : 1 ≤ x := hT.trans hxT
  have hb := lemma83_paper_beta_norm (by linarith only [hL] : 3 ≤ lemma23PaperL D) hc hsmall
  have hδ : 0 ≤ lemma84CorrectionError D K := by
    unfold lemma84CorrectionError
    positivity [hα.1,lemma83_total_shift_constant_pos,Real.log_nonneg (by linarith only [hL] : 1 ≤ lemma23PaperL D)]
  have hscale : lemma44PaperAlpha D*Real.log x ≤ Real.pi := by
    have hxlog := (Real.log_lt_log (lt_of_lt_of_le zero_lt_one hx) hxP).le
    unfold lemma23PaperP at hxlog
    rw [Real.log_exp] at hxlog
    have hh := mul_le_mul_of_nonneg_left hxlog hα.1.le
    have he : lemma44PaperAlpha D*lemma23PaperL D^9 = Real.pi := by
      unfold lemma44PaperAlpha lemma23PaperP
      rw [Real.log_exp,div_mul_cancel₀ _ (pow_ne_zero _ hLp.ne')]
    exact hh.trans_eq he
  exact lemma102_circle_approximation_with_pi χ hDN hA hC
    (lemma83PaperBeta D c (j+1)) (lemma83PaperBeta D c (j+2))
    (lemma83Pi χ d r) (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r)
    (lemma84CorrectionError D K) (hb _) (hb _) hδ hx hscale
    (lemma83_euler_correction_analyticOnNhd χ _ (lemma83_beta_re D c) j d r)
    (lemma84_actual_correction_strong_bound χ hc hL hsmall j d r K hd hr hcut hK)

end ZhangLS.Spec
