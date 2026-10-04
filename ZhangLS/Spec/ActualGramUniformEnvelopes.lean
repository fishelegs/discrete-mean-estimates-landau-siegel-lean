import ZhangLS.Spec.ActualGramSecondProfileError

/-! Arithmetic envelopes for the actual fixed-profile integrals. Constants
are absolute; their only profile dependence is introduced by fixed density
bounds at the later common-threshold substitution. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex

noncomputable def actualGramUniformExponent : ℕ :=
  lemma84BoundaryXiExponent + lemma84PiExponent

noncomputable def actualGramUniformSecondBoundaryConstant : ℝ :=
  4*(lemma84BoundaryXiConstant+16*Real.exp 1*lemma83PrimeProductScale*(33+49*Real.pi))

lemma actualGramUniform_second_boundary_constant_pos :
    0 < actualGramUniformSecondBoundaryConstant := by
  unfold actualGramUniformSecondBoundaryConstant lemma83PrimeProductScale
  positivity [lemma84_boundary_xi_constant_pos]

noncomputable def actualGramUniformFirstBoundaryConstant : ℝ :=
  2 + 16*Real.exp 1*(1+10*Real.pi)

noncomputable def actualGramUniformMainConstant : ℝ :=
  16*Real.exp 1*lemma83PrimeProductScale*(1+8*Real.pi+16*Real.pi^2)

lemma actualGramUniform_first_boundary_constant_pos :
    0 < actualGramUniformFirstBoundaryConstant := by
  unfold actualGramUniformFirstBoundaryConstant
  positivity

lemma actualGramUniform_main_constant_pos : 0 < actualGramUniformMainConstant := by
  unfold actualGramUniformMainConstant lemma83PrimeProductScale
  positivity

lemma actualGramUniform_scale_bounds {D : ℕ} (hL : 1 ≤ lemma23PaperL D) :
    1 ≤ 1+9*Real.log (lemma23PaperL D) ∧
      1 ≤ Real.log (lemma56PaperT D) ∧
      lemma23PaperL D ≤ Real.log (lemma56PaperT D) := by
  refine ⟨by linarith [Real.log_nonneg hL], ?_, ?_⟩
  · rw [lemma56PaperT,Real.log_exp]
    exact Real.one_le_rpow hL (by norm_num)
  · rw [lemma56PaperT,Real.log_exp]
    have hh := Real.rpow_le_rpow_of_exponent_le hL (show (1:ℝ) ≤ 11/10 by norm_num)
    simpa only [Real.rpow_one] using hh

lemma actualGramUniform_first_boundary_bound {D : ℕ} (hL : 1 ≤ lemma23PaperL D) :
    actualGramFirstBoundaryBudget D ≤
      actualGramUniformFirstBoundaryConstant*(Real.log (lemma56PaperT D))^2 := by
  obtain ⟨hR,hH,hLH⟩ := actualGramUniform_scale_bounds hL
  have hs := pow_le_pow_left₀ (by linarith : 0 ≤ lemma23PaperL D) hLH 2
  have hc : 0 ≤ 16*Real.exp 1*(1+10*Real.pi) := by positivity
  have hh := mul_le_mul_of_nonneg_left hs hc
  unfold actualGramFirstBoundaryBudget actualGramUniformFirstBoundaryConstant
  nlinarith

lemma actualGramUniform_pi_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 100 ≤ lemma23PaperL D) (d r : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2:ℤ)) :
    ‖lemma83Pi χ d r‖ ≤ lemma83PrimeProductScale*
      (1+9*Real.log (lemma23PaperL D))^actualGramUniformExponent := by
  have hR := (actualGramUniform_scale_bounds (by linarith : 1 ≤ lemma23PaperL D)).1
  have hp := lemma84_pi_polylog_bound χ hL d r lemma84PiExponent hd hr hcut (Nat.le_ceil _)
  have hpow : (1+9*Real.log (lemma23PaperL D))^lemma84PiExponent ≤
      (1+9*Real.log (lemma23PaperL D))^actualGramUniformExponent :=
    pow_le_pow_right₀ hR (Nat.le_add_left _ _)
  exact hp.trans (mul_le_mul_of_nonneg_left hpow (by unfold lemma83PrimeProductScale; positivity))

lemma actualGramUniform_second_boundary_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hL : 100 ≤ lemma23PaperL D) (d r : ℕ) (hd : 0 < d) (hr : 0 < r)
    (hcut : (d*r : ℝ) < lemma23PaperP D*lemma56PaperT D^(-2:ℤ)) :
    actualGramSecondBoundaryBudget χ d r ≤
      actualGramUniformSecondBoundaryConstant*(1+9*Real.log (lemma23PaperL D))^actualGramUniformExponent*
        (Real.log (lemma56PaperT D))^4 := by
  obtain ⟨hR,hH,hLH⟩ := actualGramUniform_scale_bounds (by linarith : 1 ≤ lemma23PaperL D)
  have hL0 : 0 ≤ lemma23PaperL D := by linarith
  have hLH4 : lemma23PaperL D^2 ≤ (Real.log (lemma56PaperT D))^4 :=
    (pow_le_pow_left₀ hL0 hLH 2).trans (pow_le_pow_right₀ hH (by omega))
  have hp := actualGramUniform_pi_bound χ hL d r hd hr hcut
  have hpow : (1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent ≤
      (1+9*Real.log (lemma23PaperL D))^actualGramUniformExponent :=
    pow_le_pow_right₀ hR (Nat.le_add_right _ _)
  have hxi := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hpow lemma84_boundary_xi_constant_pos.le)
    (show 0 ≤ (Real.log (lemma56PaperT D))^4 by positivity)
  have hm := mul_le_mul hLH4 hp (norm_nonneg _) (by positivity)
  have hm' := mul_le_mul_of_nonneg_left hm
    (show 0 ≤ 16*Real.exp 1*(33+49*Real.pi) by positivity)
  have hbase : 0 ≤
      (lemma84BoundaryXiConstant+16*Real.exp 1*lemma83PrimeProductScale*(33+49*Real.pi))*
        (1+9*Real.log (lemma23PaperL D))^actualGramUniformExponent*
        (Real.log (lemma56PaperT D))^4 := by
    unfold lemma83PrimeProductScale
    positivity [lemma84_boundary_xi_constant_pos]
  unfold actualGramSecondBoundaryBudget actualGramUniformSecondBoundaryConstant
  nlinarith only [hxi,hm',hbase]

end ZhangLS.Spec
