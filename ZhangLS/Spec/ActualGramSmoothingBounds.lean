import ZhangLS.Spec.Lemma84CompanionBounds
import ZhangLS.Spec.Lemma84BoundaryMainBound
import ZhangLS.Spec.Lemma84Repaired

/-! Genuine arbitrary-real-x error envelopes for the original smoothing
kernels. The small-x branch uses the proved elementary/Perron bounds and
pays the displayed main term separately. Pi is never divided out. -/
set_option autoImplicit false
set_option maxHeartbeats 2500000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical

noncomputable def actualGramFirstBoundaryBudget (D : ℕ) : ℝ :=
  Real.log (lemma56PaperT D)*(1+Real.log (lemma56PaperT D))+
    (16*Real.exp 1*lemma23PaperL D^2)*(1+10*Real.pi)

noncomputable def actualGramSecondBoundaryBudget {D : ℕ} (χ : RealPrimitiveCharacter D)
    (d r : ℕ) : ℝ :=
  lemma84BoundaryXiConstant*(1+9*Real.log (lemma23PaperL D))^lemma84BoundaryXiExponent*
    (Real.log (lemma56PaperT D))^4+
  (16*Real.exp 1*lemma23PaperL D^2)*‖lemma83Pi χ d r‖*(33+49*Real.pi)

lemma actualGram_first_small_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) (μ : ℕ) {x : ℝ} (hx : 1≤x) (hxT : x≤lemma56PaperT D)
    (hxP : x<lemma23PaperP D) :
    ‖lemma82ShiftedSum χ c j μ x-LDerivAtOne χ*lemma82MainTerm D c j μ x‖ ≤
      actualGramFirstBoundaryBudget D := by
  have hk := lemma84_companion_elementary χ c j μ hx
  have hf := lemma84_companion_main_bound hL hc hsmall j μ hx hxP
  have hder : ‖LDerivAtOne χ‖≤16*Real.exp 1*lemma23PaperL D^2 :=
    lemma32_actual_first_derivative_bound χ hD (by change 2≤lemma23PaperL D; linarith)
      (by simp; positivity)
  have hlog : Real.log x≤Real.log (lemma56PaperT D) :=
    Real.log_le_log (by linarith) hxT
  have hxlog : 0≤Real.log x := Real.log_nonneg hx
  have hTlog : 0≤Real.log (lemma56PaperT D) := hxlog.trans hlog
  have hb : Real.log x*(1+Real.log x)≤
      Real.log (lemma56PaperT D)*(1+Real.log (lemma56PaperT D)) := by nlinarith
  apply (norm_sub_le _ _).trans
  rw [norm_mul]
  exact add_le_add (hk.trans hb)
    (mul_le_mul hder hf (norm_nonneg _) (by positivity))

lemma actualGram_second_small_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) (μ d r : ℕ) (hd : 0<d) (hr : 0<r)
    (hlog : Real.log (d*r : ℕ)≤lemma23PaperL D^9)
    {x : ℝ} (hx : 1≤x) (hxT : x≤lemma56PaperT D) (hxP : x<lemma23PaperP D) :
    ‖lemma84XiSum χ c j μ d r x-
      LDerivAtOne χ*lemma83Pi χ d r*lemma84MainTerm D c j μ x‖ ≤
      actualGramSecondBoundaryBudget χ d r := by
  have hk := lemma84_boundary_xi_small_x χ hD (by linarith) c j μ d r hd hr hlog hx hxT
  have hg := lemma84_boundary_g_main_bound (by linarith : 100≤lemma23PaperL D) hc hsmall j μ hx hxP
  have hder : ‖LDerivAtOne χ‖≤16*Real.exp 1*lemma23PaperL D^2 :=
    lemma32_actual_first_derivative_bound χ hD (by change 2≤lemma23PaperL D; linarith)
      (by simp; positivity)
  apply (norm_sub_le _ _).trans
  rw [norm_mul,norm_mul]
  exact add_le_add hk
    (mul_le_mul (mul_le_mul_of_nonneg_right hder (norm_nonneg _)) hg (norm_nonneg _)
      (by positivity))

/-- One source threshold controls every genuine real cutoff, both sides of
T, all original j and mu, and every allowed d,r. No fixed-Pmu endpoint result
is generalized here. The boundary includes x=1 and x=T. -/
theorem actualGram_smoothing_errors_uniform (c : ℝ) (hc : 0<c) :
    ∃ N : ℕ, 2≤N ∧ ∀ D : ℕ, N≤D → ∀ χ : RealPrimitiveCharacter D,
    NormalizedAssumptionA χ → ∀ j : Fin 3, ∀ μ d r : ℕ,
    (μ=6 ∨ μ=7) → 0<d → 0<r →
    (d*r : ℝ)<lemma23PaperP D*lemma56PaperT D^(-2 : ℤ) →
    ∀ x : ℝ, 1≤x → x<lemma23PaperP D →
    (‖lemma82ShiftedSum χ c j μ x-LDerivAtOne χ*lemma82MainTerm D c j μ x‖ ≤
      if x≤lemma56PaperT D then actualGramFirstBoundaryBudget D
      else lemma82ErrorConstant*lemma23PaperL D^(-6 : ℤ)) ∧
    (‖lemma84XiSum χ c j μ d r x-LDerivAtOne χ*lemma83Pi χ d r*lemma84MainTerm D c j μ x‖ ≤
      if x≤lemma56PaperT D then actualGramSecondBoundaryBudget χ d r
      else 3*lemma23PaperL D^(-5 : ℤ)) := by
  obtain ⟨N₁,hN₁,h₁⟩ := lemma82_uniform_threshold c hc
  obtain ⟨N₂,hN₂,h₂⟩ := lemma84_genuine_main_error_bounds c hc
  refine ⟨max N₁ N₂,hN₁.trans (le_max_left _ _),?_⟩
  intro D hD χ hA j μ d r hμ hd hr hcut x hx hxP
  have hD₁ : N₁≤D := (le_max_left _ _).trans hD
  have hD₂ : N₂≤D := (le_max_right _ _).trans hD
  have hp := h₁ D hD₁
  have hD1 : 1<D := by omega
  have hL : 2000≤lemma23PaperL D := hp.2.1
  have hsmall := hp.2.2.1
  by_cases hxT : x≤lemma56PaperT D
  · rw [if_pos hxT,if_pos hxT]
    have hT0 : 0<lemma56PaperT D := Real.exp_pos _
    have hT1 : 1≤lemma56PaperT D := Real.one_le_exp_iff.mpr (Real.rpow_nonneg (by linarith) _)
    have hT2 : 1≤lemma56PaperT D^2 := one_le_pow₀ hT1
    have hprod : (0 : ℝ)<(d*r : ℕ) := by exact_mod_cast Nat.mul_pos hd hr
    have hfrac : ((d*r : ℕ) : ℝ)<lemma23PaperP D/(lemma56PaperT D^2) := by
      simpa only [Nat.cast_mul,zpow_neg,zpow_ofNat,div_eq_mul_inv] using hcut
    have hmul := (lt_div_iff₀ (pow_pos hT0 2)).mp hfrac
    have hprodP : ((d*r : ℕ) : ℝ)<lemma23PaperP D := by
      nlinarith [mul_le_mul_of_nonneg_left hT2 hprod.le]
    have hlog : Real.log (d*r : ℕ)≤lemma23PaperL D^9 := by
      have hh := Real.log_le_log hprod hprodP.le
      simpa only [lemma23PaperP,Real.log_exp] using hh
    exact ⟨actualGram_first_small_error χ hD1 hL hc hsmall j μ hx hxT hxP,
      actualGram_second_small_error χ hD1 hL hc hsmall j μ d r hd hr hlog hx hxT hxP⟩
  · rw [if_neg hxT,if_neg hxT]
    have hTx : lemma56PaperT D<x := lt_of_not_ge hxT
    exact ⟨lemma82_at_parameters χ hD1 hL hA hc hsmall hx hxP (hp.2.2.2 x hTx) j μ,
      (h₂ D hD₂ χ hA j μ d r hd hr hcut x hTx hxP).2.1⟩

end ZhangLS.Spec
