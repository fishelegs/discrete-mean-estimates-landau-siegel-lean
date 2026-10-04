import ZhangLS.Spec.ActualGramUniformAssembly

/-! Exact scalar accounting for the four genuine weighted residual products.
The leading budget has square C² R^(2K) L^-19. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace ZhangLS.Spec
open Complex Filter Topology

noncomputable def actualGramUniformWeightConstant : ℝ :=
  Real.exp (12/Real.log 2)*Real.exp (2/Real.log 2)

noncomputable def actualGramUniformResidualConstant (C : ℝ) : ℝ :=
  4*actualGramUniformWeightConstant*C^2*
    (lemma84CompanionConstant*actualGramUniformSecondBoundaryConstant+
      3*lemma84CompanionConstant+
      actualGramUniformFirstBoundaryConstant*actualGramUniformMainConstant+
      lemma82ErrorConstant*actualGramUniformMainConstant)

lemma actualGramUniform_residual_constant_nonneg (C : ℝ) :
    0 ≤ actualGramUniformResidualConstant C := by
  unfold actualGramUniformResidualConstant actualGramUniformWeightConstant
  positivity [lemma84_companion_constant_pos, actualGramUniform_second_boundary_constant_pos,
    actualGramUniform_first_boundary_constant_pos, actualGramUniform_main_constant_pos,
    lemma82_error_constant_pos]

/-- The three smaller scalar powers are dominated by H^5 L^-15; only
H≥L≥1 is used, so no fractional-power algebra is concealed. -/
lemma actualGramUniform_decay_comparison {L H : ℝ} (hL : 1 ≤ L) (hLH : L ≤ H) :
    L^(-11:ℤ) ≤ H^5*L^(-15:ℤ) ∧
      H^3*L^(-16:ℤ) ≤ H^5*L^(-15:ℤ) ∧
      L^(-13:ℤ) ≤ H^5*L^(-15:ℤ) := by
  have hLp : 0 < L := by linarith
  have hH : 1 ≤ H := hL.trans hLH
  have hp : 0 ≤ L^(-15:ℤ) := by positivity
  have h4 : L^4 ≤ H^5 :=
    (pow_le_pow_left₀ hLp.le hLH 4).trans (pow_le_pow_right₀ hH (by omega))
  have h2 : L^2 ≤ H^5 :=
    (pow_le_pow_left₀ hLp.le hLH 2).trans (pow_le_pow_right₀ hH (by omega))
  have h3 : H^3/L ≤ H^5 :=
    (div_le_self (by positivity) hL).trans (pow_le_pow_right₀ hH (by omega))
  refine ⟨?_,?_,?_⟩
  · calc
      L^(-11:ℤ) = L^4*L^(-15:ℤ) := by
        simp only [zpow_neg,zpow_ofNat]
        field_simp [hLp.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h4 hp
  · calc
      H^3*L^(-16:ℤ) = (H^3/L)*L^(-15:ℤ) := by
        simp only [zpow_neg,zpow_ofNat]
        field_simp [hLp.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h3 hp
  · calc
      L^(-13:ℤ) = L^2*L^(-15:ℤ) := by
        simp only [zpow_neg,zpow_ofNat]
        field_simp [hLp.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h2 hp

lemma actualGramUniform_four_term_comparison {L H R a b c d : ℝ} (k : ℕ)
    (hL : 1 ≤ L) (hLH : L ≤ H) (hR : 1 ≤ R)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    a*R^k*H^5*L^(-15:ℤ)+b*L^(-11:ℤ)+
      c*R^k*H^3*L^(-16:ℤ)+d*R^k*L^(-13:ℤ) ≤
      (a+b+c+d)*R^k*H^5*L^(-15:ℤ) := by
  have hH1 : 1 ≤ H := hL.trans hLH
  have hpow : 1 ≤ R^k := one_le_pow₀ hR
  have hbase : 0 ≤ H^5*L^(-15:ℤ) := by positivity
  obtain ⟨h11,h16,h13⟩ := actualGramUniform_decay_comparison hL hLH
  have h11' := h11.trans (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow hbase)
  have hb' := mul_le_mul_of_nonneg_left h11' hb
  have hc' := mul_le_mul_of_nonneg_left h16 (show 0 ≤ c*R^k by positivity)
  have hd' := mul_le_mul_of_nonneg_left h13 (show 0 ≤ d*R^k by positivity)
  nlinarith only [hb',hc',hd']

/-- All four powers follow by exact division by B=L^9. The repaired
second interior error contributes L^-11, not the unrepaired L^-12. -/
lemma actualGramUniform_weighted_budget {D : ℕ} (hL : 1 ≤ lemma23PaperL D) (C : ℝ) :
    (4*lemma84WeightScale (Real.log (lemma23PaperP D))*Real.log (lemma23PaperP D))*
      (actualGramUniformFirstNorm D C*actualGramUniformSecondError D C+
        actualGramUniformFirstError D C*actualGramUniformSecondMain D C) ≤
      actualGramUniformResidualConstant C*
        (1+9*Real.log (lemma23PaperL D))^(actualGramUniformExponent+42)*
        (Real.log (lemma56PaperT D))^5*lemma23PaperL D^(-15:ℤ) := by
  have hLp : 0 < lemma23PaperL D := by linarith
  obtain ⟨hR,hH,hLH⟩ := actualGramUniform_scale_bounds hL
  have hcmp := actualGramUniform_four_term_comparison actualGramUniformExponent hL hLH hR
    (show 0 ≤ lemma84CompanionConstant*actualGramUniformSecondBoundaryConstant by
      positivity [lemma84_companion_constant_pos,actualGramUniform_second_boundary_constant_pos])
    (show 0 ≤ 3*lemma84CompanionConstant by positivity [lemma84_companion_constant_pos])
    (show 0 ≤ actualGramUniformFirstBoundaryConstant*actualGramUniformMainConstant by
      positivity [actualGramUniform_first_boundary_constant_pos,actualGramUniform_main_constant_pos])
    (show 0 ≤ lemma82ErrorConstant*actualGramUniformMainConstant by
      positivity [lemma82_error_constant_pos,actualGramUniform_main_constant_pos])
  have hm := mul_le_mul_of_nonneg_left hcmp
    (show 0 ≤ 4*actualGramUniformWeightConstant*C^2*(1+9*Real.log (lemma23PaperL D))^42 by
      unfold actualGramUniformWeightConstant
      positivity)
  convert hm using 1
  · unfold actualGramUniformFirstNorm actualGramUniformFirstError
      actualGramUniformSecondError actualGramUniformSecondMain lemma84WeightScale
      actualGramUniformWeightConstant
    simp only [lemma23PaperP,Real.log_exp,Real.log_pow,Nat.cast_ofNat,zpow_neg,zpow_ofNat]
    field_simp [hLp.ne'] <;> ring
  · unfold actualGramUniformResidualConstant
    rw [pow_add]
    ring

/-- Quantitative actual arithmetic residual, with no target-norm input. -/
theorem actualGramUniform_residual_quantitative (c : ℝ) (hc : 0 < c)
    (U : ActualGramUniformProfileData) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ D : ℕ, N ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      ‖actualGramUniformArithmeticResidual χ c j U‖ ≤
        actualGramUniformResidualConstant U.C*
          (1+9*Real.log (lemma23PaperL D))^(actualGramUniformExponent+42)*
          (Real.log (lemma56PaperT D))^5*lemma23PaperL D^(-15:ℤ) := by
  obtain ⟨N,hN,hbound⟩ := actualGramUniform_assembled_error c hc U
  refine ⟨N,hN,?_⟩
  intro D hDN χ hA j
  have hh := hbound D hDN
  exact (hh.2 χ hA j).trans (actualGramUniform_weighted_budget (by linarith [hh.1]) U.C)

end ZhangLS.Spec
