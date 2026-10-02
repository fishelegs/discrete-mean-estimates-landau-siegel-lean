import ZhangLS.Spec.Lemma84CircleApproximation
import ZhangLS.Spec.Lemma84DirichletBridge
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset Metric
set_option maxHeartbeats 2000000

noncomputable def lemma84CorrectionError (D K : ℕ) : ℝ :=
  lemma83TotalShiftConstant*lemma44PaperAlpha D*
    (1+9*Real.log (lemma23PaperL D))^(K+2)

/-- The genuine normalized circle integral after the Dirichlet-series bridge. -/
noncomputable def lemma84PaperCircle {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (μ d r : ℕ) (x : ℝ) : ℂ :=
  (2*Real.pi*I : ℂ)⁻¹ * circleIntegral
    (lemma84AnalyticCircleIntegrand χ (lemma83PaperBeta D c (j+1))
      (lemma83PaperBeta D c (j+2)) (lemma84SmoothingBeta D μ)
      (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x)
    0 (5*lemma44PaperAlpha D)

lemma lemma84_actual_correction_strong_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    {c : ℝ} (hc : 0 < c) (hL : 100 ≤ lemma23PaperL D)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (j : Fin 3) (d r K : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ))
    (hK : 3*lemma83FiniteShiftWeight ≤ (K : ℝ)) (s : ℂ)
    (hs : ‖s-1‖ ≤ 5*lemma44PaperAlpha D) :
    ‖lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r s-lemma83Pi χ d r‖ ≤
      lemma84CorrectionError D K := by
  have hα := lemma83_alpha_small hL
  have hLp : 0 < lemma23PaperL D := by linarith
  have hsre : 9/10 ≤ s.re := by
    have hh := (abs_le.mp ((Complex.abs_re_le_norm (s-1)).trans hs)).1
    simp only [Complex.sub_re,Complex.one_re] at hh
    linarith only [hh,hα.2]
  have hy : 1 < lemma23PaperL D^9 := one_lt_pow₀ (by linarith only [hL]) (by norm_num)
  have hscale : lemma44PaperAlpha D*lemma23PaperL D^9 ≤ Real.pi := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp,div_mul_cancel₀ _ (pow_ne_zero _ hLp.ne')]
  have hb := lemma83_paper_beta_norm (by linarith only [hL] : 3 ≤ lemma23PaperL D) hc hsmall
  have hh := lemma83_euler_correction_small_shift χ (lemma83PaperBeta D c) (lemma83_beta_re D c)
    j d r hd.ne' hr.ne' s hsre (lemma44PaperAlpha D) (lemma23PaperL D^9)
    hα.1.le (by linarith only [hα.2]) hb hs hy
    (lemma83_paper_cutoff_log hL hd hr hcut) hscale K hK
  simpa only [lemma84CorrectionError,Real.log_pow,Nat.cast_ofNat] using hh

/-- A uniform arithmetic majorant for Π, retaining rather than discarding
its possible polylogarithmic growth. -/
lemma lemma84_pi_polylog_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 100 ≤ lemma23PaperL D) (d r K : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ))
    (hK : 3*lemma83FiniteShiftWeight ≤ (K : ℝ)) :
    ‖lemma83Pi χ d r‖ ≤ lemma83PrimeProductScale*(1+9*Real.log (lemma23PaperL D))^K := by
  have hy : 1 < lemma23PaperL D^9 := one_lt_pow₀ (by linarith only [hL]) (by norm_num)
  have hh := lemma83_prime_product_uniform_le (d*r) (Nat.mul_pos hd hr) (lemma23PaperL D^9)
    lemma83FiniteShiftWeight K hy (lemma83_paper_cutoff_log hL hd hr hcut)
    lemma83_finite_shift_weight_pos.le hK
  exact (lemma83_pi_prime_product_bound χ d r hd.ne' hr.ne').trans
    (by simpa only [lemma83PrimeProductScale,Real.log_pow,Nat.cast_ofNat] using hh)

/-- All source arithmetic and analytic data instantiated. Identification with the sum still needs the contour shift/Perron estimate;
achieving the original final exponent also requires resolving the explicit Π
factor in this quantitative error. -/
lemma lemma84_paper_circle_error_explicit {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ)
    (hC : lemma58ErrorConstant ≤ lemma23PaperL D) {c : ℝ} (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (j : Fin 3) (μ d r K : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ))
    (hK : 3*lemma83FiniteShiftWeight ≤ (K : ℝ)) {x : ℝ}
    (hxT : lemma56PaperT D < x) (hxP : x < lemma23PaperP D) :
    ‖lemma84PaperCircle χ c j μ d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma84MainTerm D c j μ x‖ ≤
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
  have hx : 1 ≤ x := (hT.trans_lt hxT).le
  have hb := lemma83_paper_beta_norm (by linarith only [hL] : 3 ≤ lemma23PaperL D) hc hsmall
  have hm := lemma84_smoothing_beta_norm μ hα.1
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
  exact lemma84_circle_approximation_with_pi χ hDN hA hC
    (lemma83PaperBeta D c (j+1)) (lemma83PaperBeta D c (j+2)) (lemma84SmoothingBeta D μ)
    (lemma83Pi χ d r) (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r)
    (lemma84CorrectionError D K) (hb _) (hb _) hm.2 (norm_pos_iff.mp hm.1) hδ hx hscale
    (lemma83_euler_correction_analyticOnNhd χ _ (lemma83_beta_re D c) j d r)
    (lemma84_actual_correction_strong_bound χ hc hL hsmall j d r K hd hr hcut hK)

end ZhangLS.Spec
