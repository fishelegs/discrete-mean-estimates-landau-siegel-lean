import ZhangLS.Spec.Lemma84ArithmeticCircle
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

noncomputable def lemma84TaylorCircleConstant : ℝ :=
  10*lemma58ErrorConstant*Real.exp (5*Real.pi)/Real.pi
noncomputable def lemma84CorrectionCircleConstant : ℝ :=
  (10*lemma58ErrorConstant+260*Real.exp 1*Real.pi)*
    lemma83TotalShiftConstant*Real.exp (5*Real.pi)

lemma lemma84_circle_constants_pos :
    0 < lemma84TaylorCircleConstant ∧ 0 < lemma84CorrectionCircleConstant := by
  constructor <;> dsimp only [lemma84TaylorCircleConstant,lemma84CorrectionCircleConstant] <;>
    positivity [lemma58_error_constant_pos,lemma83_total_shift_constant_pos]

lemma lemma84_circle_budget_algebra (L E C A P X : ℝ)
    (hL : 1 ≤ L) (hE : 0 ≤ E) (hC : 0 ≤ C) (hX : 0 ≤ X)
    (hA : A ≤ 16*Real.exp 1*L^2) :
    (5*(Real.pi/L^9))*(Real.exp (5*Real.pi)/(4*(Real.pi/L^9)^2))*
      ((8*E)*L^(-15 : ℤ)*(P+C*(Real.pi/L^9)*X)+
        (13*A*(Real.pi/L^9))*(C*(Real.pi/L^9)*X)) ≤
      (10*E*Real.exp (5*Real.pi)/Real.pi)*L^(-6 : ℤ)*P +
        ((10*E+260*Real.exp 1*Real.pi)*C*Real.exp (5*Real.pi))*L^(-7 : ℤ)*X := by
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have heq : (5*(Real.pi/L^9))*(Real.exp (5*Real.pi)/(4*(Real.pi/L^9)^2))*
      ((8*E)*L^(-15 : ℤ)*(P+C*(Real.pi/L^9)*X)+
        (13*A*(Real.pi/L^9))*(C*(Real.pi/L^9)*X)) =
      (10*E*Real.exp (5*Real.pi)/Real.pi)*L^(-6 : ℤ)*P +
        10*E*C*Real.exp (5*Real.pi)*L^(-15 : ℤ)*X +
          (65/4)*A*C*Real.pi*Real.exp (5*Real.pi)*L^(-9 : ℤ)*X := by
    simp only [zpow_neg,zpow_ofNat]
    field_simp
    <;> ring
  rw [heq]
  have hpow : L^(-15 : ℤ) ≤ L^(-7 : ℤ) := zpow_le_zpow_right₀ hL (by norm_num)
  have hEterm := mul_le_mul_of_nonneg_right hpow
    (by positivity : 0 ≤ 10*E*C*Real.exp (5*Real.pi)*X)
  have hAterm := mul_le_mul_of_nonneg_right hA
    (by positivity : 0 ≤ (65/4)*C*Real.pi*Real.exp (5*Real.pi)*L^(-9 : ℤ)*X)
  have hcancel : L^2*L^(-9 : ℤ) = L^(-7 : ℤ) := by
    simpa using (zpow_add₀ hLp.ne' 2 (-9)).symm
  have hAterm' : (65/4)*A*C*Real.pi*Real.exp (5*Real.pi)*L^(-9 : ℤ)*X ≤
      260*Real.exp 1*C*Real.pi*Real.exp (5*Real.pi)*L^(-7 : ℤ)*X := by
    calc
      _ ≤ (65/4)*(16*Real.exp 1*L^2)*C*Real.pi*Real.exp (5*Real.pi)*L^(-9 : ℤ)*X := by
        nlinarith only [hAterm]
      _ = 260*Real.exp 1*C*Real.pi*Real.exp (5*Real.pi)*(L^2*L^(-9 : ℤ))*X := by ring
      _ = _ := by rw [hcancel]
  nlinarith only [hEterm,hAterm']

/-- Sharp proved circle budget: the Taylor contribution has its genuine Π
factor, while the arithmetic perturbation saves one further power of L. -/
lemma lemma84_paper_circle_error_with_pi {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ)
    (hC : lemma58ErrorConstant ≤ lemma23PaperL D) {c : ℝ} (hc : 0 < c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    (j : Fin 3) (μ d r K : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2 : ℤ))
    (hK : 3*lemma83FiniteShiftWeight ≤ (K : ℝ)) {x : ℝ}
    (hxT : lemma56PaperT D < x) (hxP : x < lemma23PaperP D) :
    ‖lemma84PaperCircle χ c j μ d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma84MainTerm D c j μ x‖ ≤
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
  apply (lemma84_paper_circle_error_explicit χ hDN hA hC hc hsmall j μ d r K hd hr hcut hK hxT hxP).trans
  simpa only [lemma84CorrectionError,he,lemma84TaylorCircleConstant,lemma84CorrectionCircleConstant] using hb

end ZhangLS.Spec
