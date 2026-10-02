import ZhangLS.Spec.Lemma84CircleError
import ZhangLS.Spec.Lemma84PaperResidue
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set
set_option maxHeartbeats 2000000

noncomputable def lemma84AnalyticCircleIntegrand {D : ℕ} (χ : RealPrimitiveCharacter D)
    (a b m : ℂ) (U : ℂ → ℂ) (x : ℝ) (s : ℂ) : ℂ :=
  (dirichletLFunction χ (1+s+a)*dirichletLFunction χ (1+s+b)/dirichletLFunction χ (1+s)) *
    U (1+s) * (x : ℂ)^s/(s+m)^2

/-- The actual circle, with analyticity and nonvanishing established before
linearity of integration. Its error explicitly retains Π. -/
lemma lemma84_circle_approximation_with_pi {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ)
    (hC : lemma58ErrorConstant ≤ lemma23PaperL D)
    (a b m p : ℂ) (U : ℂ → ℂ) (δ : ℝ) {x : ℝ}
    (ha : ‖a‖ ≤ 3*lemma44PaperAlpha D) (hb : ‖b‖ ≤ 3*lemma44PaperAlpha D)
    (hm : ‖m‖ ≤ 3*lemma44PaperAlpha D) (hm0 : m ≠ 0) (hδ : 0 ≤ δ)
    (hx : 1 ≤ x) (hscale : lemma44PaperAlpha D*Real.log x ≤ Real.pi)
    (hUa : AnalyticOnNhd ℂ U {s : ℂ | 9/10 < s.re})
    (hU : ∀ s : ℂ, ‖s-1‖ ≤ 5*lemma44PaperAlpha D → ‖U s-p‖ ≤ δ) :
    ‖(2*Real.pi*I : ℂ)⁻¹ * circleIntegral (lemma84AnalyticCircleIntegrand χ a b m U x)
        0 (5*lemma44PaperAlpha D) - LDerivAtOne χ*p*
          (a*b/m^2+(1-a*b/m^2-(a-m)*(b-m)/m*(Real.log x : ℂ))*(x : ℂ)^(-m))‖ ≤
      (5*lemma44PaperAlpha D)*(Real.exp (5*Real.pi)/(4*lemma44PaperAlpha D^2))*
        ((8*lemma58ErrorConstant)*lemma23PaperL D^(-15 : ℤ)*(‖p‖+δ) +
          (13*‖LDerivAtOne χ‖*lemma44PaperAlpha D)*δ) := by
  let R := 5*lemma44PaperAlpha D
  let A := LDerivAtOne χ
  let f : ℂ → ℂ := lemma84AnalyticCircleIntegrand χ a b m U x
  let g : ℂ → ℂ := fun s => A*p*((s+a)*(s+b)/s*(x : ℂ)^s/(s+m)^2)
  have hD := lemma57_one_lt_of_explicit_threshold hDN
  have hL : 100 ≤ lemma23PaperL D := by
    change 100 ≤ Real.log (D:ℝ)
    linarith [lemma57_log_ge_ten_million hDN]
  have hα := lemma83_alpha_small hL
  have hR : 0 < R := by dsimp [R]; nlinarith only [hα.1]
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs (s : ℂ) (hs : s ∈ sphere 0 R) : ‖s‖ = R := by
    simpa using mem_sphere_iff_norm.mp hs
  have hs0 (s : ℂ) (h : s ∈ sphere 0 R) : s ≠ 0 := by
    intro he
    have hn := hs s h
    rw [he,norm_zero] at hn
    linarith
  have hsm (s : ℂ) (h : s ∈ sphere 0 R) : s+m ≠ 0 := by
    intro he
    have hn := hs s h
    rw [eq_neg_of_add_eq_zero_left he,norm_neg] at hn
    dsimp [R] at hn
    linarith only [hn,hm,hα.1]
  have hUcont : ContinuousOn (fun s => U (1+s)) (sphere 0 R) := by
    intro s hs'
    apply ((hUa (1+s) ?_).continuousAt.comp (by fun_prop)).continuousWithinAt
    have hn := hs s hs'
    have hre : -‖s‖ ≤ s.re := (abs_le.mp (Complex.abs_re_le_norm s)).1
    change 9/10 < (1+s).re
    simp only [Complex.add_re,Complex.one_re]
    dsimp [R] at hn
    rw [hn] at hre
    linarith only [hre,hα.2]
  have hLcont : Continuous (dirichletLFunction χ) :=
    (differentiable_dirichletLFunction_of_one_lt_modulus χ hD).continuous
  have hQcont : ContinuousOn (fun s => dirichletLFunction χ (1+s+a)*
      dirichletLFunction χ (1+s+b)/dirichletLFunction χ (1+s)) (sphere 0 R) := by
    apply ContinuousOn.div (by fun_prop) (by fun_prop)
    intro s hs'
    exact lemma84_actual_circle_denominator_ne_zero χ hDN hA hC (hs s hs')
  have hxcont : Continuous (fun s : ℂ => (x : ℂ)^s) := by
    simp_rw [lemma84_positive_cpow_eq_exp hxp]
    fun_prop
  have hf : CircleIntegrable f 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    exact ((hQcont.mul hUcont).mul hxcont.continuousOn).div (by fun_prop)
      (fun s hs' => pow_ne_zero _ (hsm s hs'))
  have hg : CircleIntegrable g 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    apply ContinuousOn.const_mul
    exact ((((continuousOn_id.add continuousOn_const).mul
      (continuousOn_id.add continuousOn_const)).div continuousOn_id hs0).mul
        hxcont.continuousOn).div (by fun_prop) (fun s hs' => pow_ne_zero _ (hsm s hs'))
  have hgval : (2*Real.pi*I : ℂ)⁻¹*circleIntegral g 0 R =
      A*p*(a*b/m^2+(1-a*b/m^2-(a-m)*(b-m)/m*(Real.log x : ℂ))*(x : ℂ)^(-m)) := by
    dsimp [g]
    rw [circleIntegral.integral_const_mul]
    rw [show (2*Real.pi*I : ℂ)⁻¹*(A*p*circleIntegral
      (fun s : ℂ => (s+a)*(s+b)/s*(x:ℂ)^s/(s+m)^2) 0 R) =
      A*p*((2*Real.pi*I : ℂ)⁻¹*circleIntegral
      (fun s : ℂ => (s+a)*(s+b)/s*(x:ℂ)^s/(s+m)^2) 0 R) by ring]
    simp_rw [lemma84_positive_cpow_eq_exp hxp]
    rw [lemma84_model_circle_integral a b m (Real.log x : ℂ) hm0 (by dsimp [R]; linarith only [hm,hα.1])]
  have heq : (2*Real.pi*I : ℂ)⁻¹*circleIntegral f 0 R -
      (2*Real.pi*I : ℂ)⁻¹*circleIntegral g 0 R =
      (2*Real.pi*I : ℂ)⁻¹*circleIntegral (fun s =>
        (dirichletLFunction χ (1+s+a)*dirichletLFunction χ (1+s+b)/dirichletLFunction χ (1+s)*U (1+s) -
          (A*(s+a)*(s+b)/s)*p)*exp (s*(Real.log x : ℂ))/(s+m)^2) 0 R := by
    rw [← mul_sub, ← circleIntegral.integral_sub hf hg]
    congr 1
    apply circleIntegral.integral_congr hR.le
    intro s _
    dsimp [f,g,lemma84AnalyticCircleIntegrand]
    rw [lemma84_positive_cpow_eq_exp hxp]
    ring
  rw [← hgval,heq]
  exact lemma84_actual_circle_error_with_pi χ hDN hA hC a b m p (fun s => U (1+s))
    δ (Real.log x) Real.pi ha hb hm hδ (Real.log_nonneg hx) hscale
    (fun s hs' => hU (1+s) (by simpa using (hs s hs').le))

end ZhangLS.Spec
