import ZhangLS.Spec.Lemma82UniformThreshold

/-!
# Original Lemma 8.2 of arXiv:2211.02515v1

The strict finite character sum is evaluated by a proved Abel identity,
scaling and Cauchy's estimate, rather than the paper's Perron contour.
The exact weighted tail is bounded by 16D/x, then absorbed uniformly using
T<x. The local L and L′ approximation uses actual proved Taylor bounds
under (A). No contour estimate, conditional derivative series, or final
conclusion is assumed. The paper's citation to Lemma 5.6 is a misreference:
the actual local linearization is the completed Lemma 5.8.
-/

namespace ZhangLS.Spec
open Complex
open scoped Real
set_option maxHeartbeats 1000000

noncomputable def lemma82ErrorConstant : ℝ := 16 + lemma82LocalErrorConstant

lemma lemma82_error_constant_pos : 0 < lemma82ErrorConstant := by
  unfold lemma82ErrorConstant
  linarith [lemma82_local_error_constant_pos]

lemma lemma82_at_parameters {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 2000 ≤ lemma23PaperL D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D ≤ 1/10)
    {x : ℝ} (hx : 1 ≤ x) (hxp : x < lemma23PaperP D)
    (htail : (D:ℝ)/x ≤ lemma23PaperL D^(-6:ℤ)) (j : Fin 3) (μ : ℕ) :
    ‖lemma82ShiftedSum χ c j μ x-LDerivAtOne χ*lemma82MainTerm D c j μ x‖ ≤
      lemma82ErrorConstant*lemma23PaperL D^(-6:ℤ) := by
  let s : ℂ := 1+lemma82SmoothingBeta D μ-lemma82PaperBeta D c j
  let A : ℂ := (Real.log x : ℂ)*dirichletLFunction χ s+deriv (dirichletLFunction χ) s
  let Q : ℂ := (x:ℂ)^(lemma82SmoothingBeta D μ)
  have hs := lemma82_shift_in_disk hL hc hsmall j μ
  have hbridge := lemma82_original_analytic_bridge χ hD c j μ hx hs.2
  have hlocal := lemma82_local_analytic_error χ hD hL hA hx hxp hs.1
  have hQ : ‖Q‖=1 := by
    dsimp [Q]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (lt_of_lt_of_le zero_lt_one hx),
      lemma82_smoothing_beta_re,Real.rpow_zero]
  have hdecomp : lemma82ShiftedSum χ c j μ x-LDerivAtOne χ*lemma82MainTerm D c j μ x =
      (lemma82ShiftedSum χ c j μ x-Q*A) +
      Q*(A-LDerivAtOne χ*(1+(s-1)*(Real.log x : ℂ))) := by
    unfold lemma82MainTerm
    dsimp [Q,s]
    ring
  rw [hdecomp]
  apply (norm_add_le _ _).trans
  rw [norm_mul,hQ,one_mul]
  apply (add_le_add hbridge hlocal).trans
  have hh := mul_le_mul_of_nonneg_left htail (by norm_num : (0:ℝ)≤16)
  dsimp [lemma82ErrorConstant]
  rw [mul_div_assoc]
  nlinarith only [hh]

/-- Complete original target with strict T<x<P and the same original c′
shifts. C is absolute and is selected before c′, D, χ, x, j and μ. -/
theorem lemma82_original : Lemma82Target := by
  refine ⟨lemma82ErrorConstant,lemma82_error_constant_pos,?_⟩
  intro c hc
  obtain ⟨D₀,h2,hD₀⟩ := lemma82_uniform_threshold c hc
  refine ⟨D₀,h2,?_⟩
  intro D hD χ hA x hTx hxP j μ hμ
  have hh := hD₀ D hD
  have hT : 1 ≤ lemma56PaperT D := by
    unfold lemma56PaperT
    apply Real.one_le_exp_iff.mpr
    exact Real.rpow_nonneg (by linarith only [hh.2.1]) _
  exact lemma82_at_parameters χ (by omega) hh.2.1 hA hc hh.2.2.1
    (hT.trans hTx.le) hxP (hh.2.2.2 x hTx) j μ

end ZhangLS.Spec
