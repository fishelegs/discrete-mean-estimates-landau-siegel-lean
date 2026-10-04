import ZhangLS.Spec.ActualGramUniformBudget

/-! The actual fixed-profile arithmetic residual is o(alpha), uniformly after
one threshold. This concerns P7 arithmetic attachment, not the completed
fixed-H norm, Gram identification, nondegeneracy or strict gain. -/
set_option autoImplicit false
set_option maxHeartbeats 3500000
namespace ZhangLS.Spec
open Complex Finset Filter Topology Set
open scoped Classical ContDiff

lemma actualGramUniform_logT_tenth {D : ℕ} (hL : 0 < lemma23PaperL D) :
    (Real.log (lemma56PaperT D))^10 = lemma23PaperL D^11 := by
  rw [lemma56PaperT,Real.log_exp,←Real.rpow_natCast (lemma23PaperL D^(11/10:ℝ)) 10,
    ←Real.rpow_mul hL.le]
  norm_num only [Nat.cast_ofNat,show (11/10:ℝ)*10=11 by norm_num]
  exact Real.rpow_natCast _ 11

lemma actualGramUniform_budget_square (L H R C : ℝ) (K : ℕ)
    (hL : L ≠ 0) (hH : H^10 = L^11) :
    (C*R^K*H^5*L^(-15:ℤ))^2 = C^2*R^(2*K)*L^(-19:ℤ) := by
  have hr : (R^K)^2=R^(2*K) := by rw [←pow_mul]; congr 1; omega
  have hh : (H^5)^2=H^10 := by ring
  rw [mul_pow,mul_pow,mul_pow,hr,hh,hH]
  simp only [zpow_neg,zpow_ofNat]
  field_simp <;> ring

/-- The precise scalar ending reuses the square argument of the original
boundary proof, without importing its unrelated fixed-endpoint target. -/
theorem actualGramUniform_scalar_little_o (C : ℝ) (hC : 0 < C) (K : ℕ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ D : ℕ, N ≤ D →
      C*(1+9*Real.log (lemma23PaperL D))^K*(Real.log (lemma56PaperT D))^5*
        lemma23PaperL D^(-15:ℤ) ≤ ε*lemma44PaperAlpha D := by
  have hep : 0 < ε*Real.pi := mul_pos hε Real.pi_pos
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hp := ht.eventually (lemma83_polylog_eventually_le
    (C^2/(ε*Real.pi)^2) (by positivity) (2*K))
  obtain ⟨N,hN⟩ := eventually_atTop.mp (show ∀ᶠ D : ℕ in atTop,
      2 ≤ D ∧ 1 ≤ lemma23PaperL D ∧
        (C^2/(ε*Real.pi)^2)*(1+9*Real.log (lemma23PaperL D))^(2*K) ≤ lemma23PaperL D from by
    filter_upwards [eventually_ge_atTop (2:ℕ),ht.eventually_ge_atTop 1,hp]
      with D h2 h1 hp
    exact ⟨h2,h1,hp⟩)
  refine ⟨N,(hN N le_rfl).1,?_⟩
  intro D hDN
  obtain ⟨hD2,hL1,hpoly⟩ := hN D hDN
  have hLp : 0 < lemma23PaperL D := by linarith
  have hR : 0 ≤ 1+9*Real.log (lemma23PaperL D) := by linarith [Real.log_nonneg hL1]
  have hpoly' : C^2*(1+9*Real.log (lemma23PaperL D))^(2*K) ≤
      (ε*Real.pi)^2*lemma23PaperL D := by
    have hh := mul_le_mul_of_nonneg_left hpoly (sq_nonneg (ε*Real.pi))
    have he : (ε*Real.pi)^2*((C^2/(ε*Real.pi)^2)*(1+9*Real.log (lemma23PaperL D))^(2*K)) =
        C^2*(1+9*Real.log (lemma23PaperL D))^(2*K) := by field_simp
    rwa [he] at hh
  have hbudgetSq :
      (C*(1+9*Real.log (lemma23PaperL D))^K*(Real.log (lemma56PaperT D))^5*
        lemma23PaperL D^(-15:ℤ))^2 ≤ (ε*lemma44PaperAlpha D)^2 := by
    rw [actualGramUniform_budget_square _ _ _ _ _ hLp.ne' (actualGramUniform_logT_tenth hLp)]
    have hh := mul_le_mul_of_nonneg_right hpoly'
      (show 0 ≤ lemma23PaperL D^(-19:ℤ) by positivity)
    apply hh.trans_eq
    rw [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
    simp only [zpow_neg,zpow_ofNat]
    field_simp <;> ring
  have halpha : 0 ≤ ε*lemma44PaperAlpha D := by
    rw [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
    positivity
  have hbudget0 : 0 ≤ C*(1+9*Real.log (lemma23PaperL D))^K*
      (Real.log (lemma56PaperT D))^5*lemma23PaperL D^(-15:ℤ) := by
    rw [lemma56PaperT,Real.log_exp]
    positivity
  exact (sq_le_sq₀ hbudget0 halpha).mp hbudgetSq

/-- The common-threshold actual P7 arithmetic residual is o(alpha), without
assuming a target arithmetic norm or completed norm asymptotic. -/
theorem actualGramUniform_residual_little_o (c : ℝ) (hc : 0 < c)
    (U : ActualGramUniformProfileData) (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ D : ℕ, N ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      ‖actualGramUniformArithmeticResidual χ c j U‖ ≤ ε*lemma44PaperAlpha D := by
  obtain ⟨Nq,hNq,hq⟩ := actualGramUniform_residual_quantitative c hc U
  have hC : 0 < 1+actualGramUniformResidualConstant U.C := by
    linarith [actualGramUniform_residual_constant_nonneg U.C]
  obtain ⟨Ns,hNs,hs⟩ := actualGramUniform_scalar_little_o
    (1+actualGramUniformResidualConstant U.C) hC (actualGramUniformExponent+42) ε hε
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R:=ℝ))
  obtain ⟨NL,hNL⟩ := eventually_atTop.mp (ht.eventually_ge_atTop 1)
  refine ⟨max (max Nq Ns) NL, hNq.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro D hDN χ hA j
  have hqD : Nq ≤ D := (le_max_left _ _).trans ((le_max_left _ _).trans hDN)
  have hsD : Ns ≤ D := (le_max_right _ _).trans ((le_max_left _ _).trans hDN)
  have hLD : NL ≤ D := (le_max_right _ _).trans hDN
  have hL : 1 ≤ lemma23PaperL D := hNL D hLD
  have hR := (actualGramUniform_scale_bounds hL).1
  have hH := (actualGramUniform_scale_bounds hL).2.1
  apply (hq D hqD χ hA j).trans
  apply le_trans _ (hs D hsD)
  have hh := mul_le_mul_of_nonneg_right
    (show actualGramUniformResidualConstant U.C ≤ 1+actualGramUniformResidualConstant U.C by linarith)
    (show 0 ≤ (1+9*Real.log (lemma23PaperL D))^(actualGramUniformExponent+42)*
      (Real.log (lemma56PaperT D))^5*lemma23PaperL D^(-15:ℤ) by positivity)
  simpa only [mul_assoc] using hh

/-- Literal original strict-box P7 minus its exact ramified differential main
for any fixed smooth profiles in [251/500,201/400]. All profile constants
are selected before D; the final threshold is before D, χ and j. -/
theorem actualGramUniform_smooth_residual_little_o (c : ℝ) (hc : 0 < c)
    (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hsf : tsupport f ⊆ Icc (251/500 : ℝ) (201/400))
    (hsg : tsupport g ⊆ Icc (251/500 : ℝ) (201/400))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, 2 ≤ N ∧ ∀ D : ℕ, N ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      ‖proposition71ArithmeticSum D c j
        (actualGramProfileSequence χ (fun n => f (Real.log n/Real.log (lemma23PaperP D))))
        (actualGramProfileSequence χ (fun n => g (Real.log n/Real.log (lemma23PaperP D)))) -
        (LDerivAtOne χ^2/(Real.log (lemma23PaperP D) : ℂ)^2)*
          (∑ n ∈ lemma81PolynomialIndices D,
            (‖χ.evalNat n‖ : ℂ)*lemma83Lambda (lemma83PaperBeta D c) n (1-lemma83PaperBeta D c j)/
              (Nat.totient n : ℂ)*actualGramFiniteProfileKernel D c j
                (Real.log (lemma23PaperP D)) (201/400) f (deriv f) g (deriv g) n)‖ ≤
        ε*lemma44PaperAlpha D := by
  obtain ⟨U,hUf,hUfp,hUg,hUgp,hUb,hUC⟩ := actualGramUniform_smooth_data f g hf hg hsf hsg
  obtain ⟨N,hN,hbound⟩ := actualGramUniform_residual_little_o c hc U ε hε
  refine ⟨N,hN,?_⟩
  intro D hDN χ hA j
  simpa only [actualGramUniformArithmeticResidual,hUf,hUfp,hUg,hUgp,hUb] using hbound D hDN χ hA j

end ZhangLS.Spec
