import ZhangLS.Spec.Lemma59ExtendedRouche

/-! # Full original actual L-function quotient for Lemma 5.9

Original Psi1, actual objects, original closed boundaries and all-zero
separation are retained. The final module proves the unchanged Lemma59Target.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Complex Metric Set in
theorem lemma59_ext46_actual_rouche_count_one_closed {m c : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hcmp : lemma46ModelErrorConstant < m * c)
    (hmodel : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      m * (1 - ‖z‖) ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re)
    (hrehi : ρ.re ≤ 1 / 2 + lemma44PaperAlpha D ^ 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13)
    (hzero : lemma45ActualA χ ψ ρ = 0) :
    let f := fun w => lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w)
    let R := lemma46InnerRadius D c
    (∑ z ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R)
      (MeromorphicOn.divisor f (closedBall 0 R))).toFinset,
      (((MeromorphicOn.divisor f (closedBall 0 R)) z).toNat : ℂ)) = 1 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  let a := lemma44PaperAlpha D
  let L := lemma23PaperL D
  let M := Real.log (lemma23PaperP D)
  let R := lemma46InnerRadius D c
  let c₀ : ℂ := (1 / 2 : ℂ) + I * (ρ.im : ℂ)
  let f : ℂ → ℂ := fun w => lemma45ActualA χ ψ (c₀ + w)
  have hp := lemma46_alpha_parameters hD
  have hap : 0 < a := hp.1
  have hLp : 0 < L := by linarith [(lemma45_parameters_at_threshold hD).1]
  have hM : 0 < M := by simp only [M, lemma23PaperP, Real.log_exp]; positivity
  have haM : a * M = Real.pi := by
    dsimp [a, M, lemma44PaperAlpha]
    exact div_mul_cancel₀ _ hM.ne'
  have hR := lemma46_inner_radius_bounds hD hc hsmall
  have hfa : AnalyticOnNhd ℂ f (closedBall 0 R) :=
    lemma59_ext46_actual_A_analyticOn_inner_disk χ ψ hD hψ
      (by simp [c₀]) (by simpa [c₀] using him) hR.2.2
  apply lemma23_rouche_model_divisor_sum_eq_one hM hR.2.1
    (by simpa only [lemma44PaperAlpha] using hR.2.2) f hfa
  intro w hw
  have hwn : ‖w‖ = R := by simpa [mem_sphere, dist_zero_right] using hw
  let u := w / (a : ℂ)
  have hun : ‖u‖ = 1 - c * a * L := by
    rw [norm_div, norm_real, Real.norm_of_nonneg hp.1.le, hwn]
    dsimp [R, lemma46InnerRadius]
    change a * (1 - c * a * L) / a = _
    field_simp [hap.ne']
  have hulo : 1 / 2 ≤ ‖u‖ := by rw [hun]; change c * a * L ≤ 1 / 2 at hsmall; linarith
  have huhi : ‖u‖ ≤ 1 := by
    rw [hun]
    linarith [mul_pos (mul_pos hc hap) hLp]
  have heq : lemma23ExponentialGapModel M w = lemma23ExponentialGapModel Real.pi u := by
    unfold lemma23ExponentialGapModel
    congr 2
    dsimp [u]
    rw [← haM]
    push_cast
    field_simp [show (a : ℂ) ≠ 0 by exact_mod_cast hap.ne']
  have hb := hmodel u hulo huhi
  rw [hun, ← heq] at hb
  have hwa : ‖w‖ < a := by rw [hwn]; exact hR.2.2
  have he := lemma59_ext46_actual_model_approximation_closed χ ψ hD hψ hre hrehi him hzero hwa
  change ‖f w - lemma23ExponentialGapModel M w‖ ≤ lemma46ModelErrorConstant * a * L at he
  apply he.trans_lt
  have hprod := mul_lt_mul_of_pos_right hcmp (mul_pos hp.1 hLp)
  have he' : m * c * (a * L) = m * (1 - (1 - c * a * L)) := by ring
  rw [he'] at hprod
  nlinarith only [hb, hprod]

open Complex Set in
theorem lemma59_ext45_actual_A_ne_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedZeroFreeRegion D s) : lemma45ActualA χ ψ s ≠ 0 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  intro hz
  have hb := lemma59_ext45_actual_A_lower_bound χ ψ hD hψ hs
  rw [hz, norm_zero] at hb
  have hp : 0 < (lemma23PaperL D ^ 9)⁻¹ / 4 := by
    have hL := (lemma23_sectionFour_parameters_at_explicit_threshold hD).1
    positivity
  linarith

open Complex Metric Set in
theorem lemma59_ext46_actual_rouche_count_one {m c : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hcmp : lemma46ModelErrorConstant < m * c)
    (hmodel : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      m * (1 - ‖z‖) ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re)
    (hrehi : ρ.re < 1 / 2 + lemma44PaperAlpha D ^ 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13)
    (hzero : lemma45ActualA χ ψ ρ = 0) :
    let f := fun w => lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w)
    let R := lemma46InnerRadius D c
    (∑ z ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R)
      (MeromorphicOn.divisor f (closedBall 0 R))).toFinset,
      (((MeromorphicOn.divisor f (closedBall 0 R)) z).toNat : ℂ)) = 1 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  exact lemma59_ext46_actual_rouche_count_one_closed hm hc hcmp hmodel χ ψ hD hψ hsmall hre hrehi.le him hzero

open Complex Metric Set Filter in
theorem lemma59_ext46_zero_analysis_at_contraction_closed {m c : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hcmp : lemma46ModelErrorConstant < m * c)
    (hmodel : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      m * (1 - ‖z‖) ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re)
    (hrehi : ρ.re ≤ 1 / 2 + lemma44PaperAlpha D ^ 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13)
    (hzero : lemma45ActualA χ ψ ρ = 0) :
    ρ.re = 1 / 2 ∧ deriv (lemma45ActualA χ ψ) ρ ≠ 0 ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
        lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) ≠ 0 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  let a := lemma44PaperAlpha D
  let R := lemma46InnerRadius D c
  let c₀ : ℂ := (1 / 2 : ℂ) + I * (ρ.im : ℂ)
  let x : ℂ := (ρ.re - 1 / 2 : ℝ)
  let f : ℂ → ℂ := fun w => lemma45ActualA χ ψ (c₀ + w)
  have hp := lemma46_alpha_parameters hD
  have hap : 0 < a := hp.1
  have hLp : 0 < lemma23PaperL D := by linarith [(lemma45_parameters_at_threshold hD).1]
  have hR := lemma46_inner_radius_bounds hD hc hsmall
  have hδ : 0 ≤ ρ.re - 1 / 2 := by linarith
  have hxn : ‖x‖ = ρ.re - 1 / 2 := by
    change ‖((ρ.re - 1 / 2 : ℝ) : ℂ)‖ = _
    rw [norm_real, Real.norm_of_nonneg hδ]
  have hxa : ‖x‖ < a / 2 := by
    rw [hxn]
    change ρ.re ≤ 1 / 2 + a ^ 2 at hrehi
    change 0 < a ∧ a < 1 / 4 ∧ _ at hp
    nlinarith only [hrehi, hp.1, hp.2.1]
  have hxR : ‖x‖ < R := hxa.trans_le hR.1
  have hxK : x ∈ closedBall 0 R := by simpa [mem_closedBall, dist_zero_right] using hxR.le
  have hcρ : c₀ + x = ρ := by apply Complex.ext <;> simp [c₀, x]
  have hfx : f x = 0 := by simpa [f, hcρ] using hzero
  have hf : AnalyticOnNhd ℂ f (closedBall 0 R) :=
    lemma59_ext46_actual_A_analyticOn_inner_disk χ ψ hD hψ
      (by simp [c₀]) (by simpa [c₀] using him) hR.2.2
  have hcount := lemma59_ext46_actual_rouche_count_one_closed hm hc hcmp hmodel χ ψ hD hψ
    hsmall hre hrehi him hzero
  change (∑ z ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R)
      (MeromorphicOn.divisor f (closedBall 0 R))).toFinset,
      (((MeromorphicOn.divisor f (closedBall 0 R)) z).toNat : ℂ)) = 1 at hcount
  have hboundary : ∀ w ∈ sphere (0 : ℂ) R, f w ≠ 0 := by
    intro w hw
    -- The strict comparison is also available from Rouché. A count of one
    -- alone does not exclude a boundary zero, so use the approximation
    -- and the same uniform model lower bound here.
    have hn : ‖w‖ = R := by simpa [mem_sphere, dist_zero_right] using hw
    let u := w / (a : ℂ)
    have hun : ‖u‖ = 1 - c * a * lemma23PaperL D := by
      rw [norm_div, norm_real, Real.norm_of_nonneg hp.1.le, hn]
      dsimp [R, lemma46InnerRadius]
      change a * (1 - c * a * lemma23PaperL D) / a = _
      field_simp [hap.ne']
    have hu1 : 1 / 2 ≤ ‖u‖ := by rw [hun]; change c * a * lemma23PaperL D ≤ 1 / 2 at hsmall; linarith
    have hu2 : ‖u‖ ≤ 1 := by
      rw [hun]
      linarith [mul_pos (mul_pos hc hap) hLp]
    have hM : 0 < Real.log (lemma23PaperP D) := by
      simp only [lemma23PaperP, Real.log_exp]
      exact pow_pos hLp 9
    have haM : a * Real.log (lemma23PaperP D) = Real.pi := by
      dsimp [a, lemma44PaperAlpha]
      exact div_mul_cancel₀ _ hM.ne'
    have heq : lemma23ExponentialGapModel (Real.log (lemma23PaperP D)) w =
        lemma23ExponentialGapModel Real.pi u := by
      unfold lemma23ExponentialGapModel
      congr 2
      dsimp [u]
      rw [← haM]
      push_cast
      field_simp [show (a : ℂ) ≠ 0 by exact_mod_cast hap.ne']
    have hb := hmodel u hu1 hu2
    rw [hun, ← heq] at hb
    have haL : 0 < a * lemma23PaperL D := mul_pos hap hLp
    have hmarg := mul_lt_mul_of_pos_right hcmp haL
    have herr := lemma59_ext46_actual_model_approximation_closed χ ψ hD hψ hre hrehi him hzero
      (w := w) (by rw [hn]; exact hR.2.2)
    intro hfw
    change lemma45ActualA χ ψ (c₀ + w) = 0 at hfw
    change ‖lemma45ActualA χ ψ (c₀ + w) - _‖ ≤ _ at herr
    rw [hfw, zero_sub, norm_neg] at herr
    change _ ≤ lemma46ModelErrorConstant * a * lemma23PaperL D at herr
    nlinarith only [hb, herr, hmarg]
  have hsingle := lemma46_unique_simple_zero_of_count_one hR.2.1 hf hboundary hcount hxK hfx
  have hρstrip : Lemma59ExtendedLocalStrip D ρ :=
    lemma59_ext46_disk_subset_local_strip hD (c := c₀) (by simp [c₀])
      (by simpa [c₀] using him) (by
        rw [← hcρ, add_sub_cancel_left]
        nlinarith only [hxa, hp.1])
  have href := lemma59_ext46_actual_A_reflected_zero χ ψ hD hψ hρstrip hzero
  have hcx : c₀ + (-x) = 1 - starRingEnd ℂ ρ := by
    apply Complex.ext <;> simp [c₀, x] <;> ring
  have hnxK : -x ∈ closedBall 0 R := by
    simpa [mem_closedBall, dist_zero_right] using hxR.le
  have hfnx : f (-x) = 0 := by simpa [f, hcx] using href
  have hnx := hsingle.2 (-x) hnxK hfnx
  have hbeta : ρ.re = 1 / 2 := by
    have hh := congrArg Complex.re hnx
    simp [x] at hh
    linarith
  have hx0 : x = 0 := by simp [x, hbeta]
  refine ⟨hbeta, ?_, ?_⟩
  · have hd := hsingle.1
    change deriv (fun w => lemma45ActualA χ ψ (c₀ + w)) x ≠ 0 at hd
    rw [deriv_comp_const_add, hcρ] at hd
    exact hd
  · intro w hwp hwR hzw
    have hwK : w ∈ closedBall 0 R := by simpa [mem_closedBall, dist_zero_right] using hwR.le
    have he := hsingle.2 w hwK hzw
    rw [hx0] at he
    rw [he, norm_zero] at hwp
    exact lt_irrefl 0 hwp

open Complex Set in
theorem lemma59_ext45_actual_product_ne_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedZeroFreeRegion D s) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    DirichletCharacter.LFunction ψ s *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s ≠ 0 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  intro hz
  apply lemma59_ext45_actual_A_ne_zero χ ψ hD hψ hs
  simp only [lemma45ActualA, hz, zero_div]

open Complex Metric Set Filter in
theorem lemma59_ext46_zero_analysis_at_contraction {m c : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hcmp : lemma46ModelErrorConstant < m * c)
    (hmodel : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      m * (1 - ‖z‖) ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re)
    (hrehi : ρ.re < 1 / 2 + lemma44PaperAlpha D ^ 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13)
    (hzero : lemma45ActualA χ ψ ρ = 0) :
    ρ.re = 1 / 2 ∧ deriv (lemma45ActualA χ ψ) ρ ≠ 0 ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
        lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) ≠ 0 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  exact lemma59_ext46_zero_analysis_at_contraction_closed hm hc hcmp hmodel χ ψ hD hψ hsmall hre hrehi.le him hzero

open Complex Metric Set Filter in
theorem lemma59_ext46_proved : Lemma59ExtendedLemma46Target := by
  obtain ⟨m, hm, hmodel⟩ := lemma46_model_uniform_inner_boundary
  let c := (lemma46ModelErrorConstant + 1) / m
  have hc : 0 < c := div_pos (by linarith [lemma46_model_error_constant_pos]) hm
  have hcmp : lemma46ModelErrorConstant < m * c := by
    dsimp [c]
    rw [mul_div_cancel₀ _ hm.ne']
    linarith
  obtain ⟨D₀, hD₀, hsmall⟩ := lemma46_exists_contraction_threshold hc
  refine ⟨c, hc, D₀, ?_⟩
  intro D p hp χ ψ hD hψ ρ hre hrehi him hzero
  refine ⟨(lemma46_inner_radius_bounds (hD₀.trans hD) hc (hsmall D hD)).2.1, ?_⟩
  exact lemma59_ext46_zero_analysis_at_contraction hm hc hcmp hmodel χ ψ
    (hD₀.trans hD) hψ (hsmall D hD) hre hrehi him hzero

open Complex ComplexConjugate Metric Set in
theorem lemma59_ext48_actual_zero_in_thin_slab {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedZeroOmega D s) (hzero : lemma48ActualProduct χ ψ s = 0) :
    |s.re - 1 / 2| ≤ lemma44PaperAlpha D ^ 2 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hbounds (z : ℂ) (hz : Lemma59ExtendedZeroOmega D z)
      (hzzero : lemma48ActualProduct χ ψ z = 0) :
      z.re ≤ 1 / 2 + lemma44PaperAlpha D ^ 2 := by
    by_contra h
    have hr : Lemma59ExtendedZeroFreeRegion D z :=
      ⟨lt_of_not_ge h, by linarith [(abs_lt.mp hz.1).2], hz.2⟩
    exact lemma59_ext45_actual_product_ne_zero χ ψ hD hψ hr hzzero
  have hu := hbounds s hs hzero
  have hr := lemma59_ext48_omega_reflection hs
  have hz := lemma48_actual_product_reflected_zero χ ψ hL hψ.1
    (lemma59_ext48_omega_height_pos hL hs) hzero
  have hl := hbounds (1 - conj s) hr hz
  simp only [sub_re, one_re, conj_re] at hl
  exact abs_le.mpr ⟨by linarith, by linarith⟩

open Complex ComplexConjugate Metric Set in
theorem lemma59_ext48_actual_Z_inv_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedZeroOmega D s) (hzero : lemma48ActualProduct χ ψ s = 0) :
    ‖(lemma44ActualZtilde χ ψ s)⁻¹‖ ≤ Real.exp 3 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hslab := lemma59_ext48_actual_zero_in_thin_slab χ ψ hD hψ hs hzero
  have hr := lemma59_ext48_thin_slab_regions hD hs hslab
  have him := lemma59_ext48_omega_height_pos hL hs
  have hreflection := lemma47_actual_Z_reflection χ ψ hL hψ.1 him.ne'
  have he : (lemma44ActualZtilde χ ψ s)⁻¹ =
      conj (lemma44ActualZtilde χ ψ (1 - conj s)) := by
    have hn := lemma44ActualZtilde_ne_zero χ ψ hL hψ.1 him
    apply (mul_left_cancel₀ hn)
    simpa only [mul_inv_cancel₀ hn] using hreflection.symm
  rw [he, norm_conj]
  have hb := lemma59_ext44ActualZtilde_norm_on_omega3 χ ψ hD hψ.1 hr.2.2
  apply hb.trans
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [sub_re, one_re, conj_re]
  have ha := lemma46_alpha_parameters hD
  have hM : 0 < Real.log (lemma23PaperP D) := by
    simp only [lemma23PaperP, Real.log_exp]
    positivity
  have haM : lemma44PaperAlpha D * Real.log (lemma23PaperP D) = Real.pi := by
    unfold lemma44PaperAlpha
    exact div_mul_cancel₀ _ hM.ne'
  have hm := mul_le_mul_of_nonneg_right (abs_le.mp hslab).2 hM.le
  have ha2M : lemma44PaperAlpha D ^ 2 * Real.log (lemma23PaperP D) =
      lemma44PaperAlpha D * Real.pi := by rw [← haM]; ring
  rw [ha2M] at hm
  nlinarith only [hm, ha.1, ha.2.1, Real.pi_le_four]

open Complex ComplexConjugate in
theorem lemma59_ext_prop22_actual_zero_analysis {m c : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hcmp : lemma46ModelErrorConstant < m * c)
    (hmodel : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      m * (1 - ‖z‖) ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hρ : Lemma59ExtendedZeroOmega D ρ) (hzero : lemma48ActualProduct χ ψ ρ = 0) :
    ρ.re = 1 / 2 ∧ deriv (lemma48ActualProduct χ ψ) ρ ≠ 0 ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
        lemma48ActualProduct χ ψ (ρ + w) ≠ 0 := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hslab := lemma59_ext48_actual_zero_in_thin_slab χ ψ hD hψ hρ hzero
  have hA : lemma45ActualA χ ψ ρ = 0 := by
    change lemma48ActualProduct χ ψ ρ / _ = 0
    rw [hzero, zero_div]
  have hbeta : ρ.re = 1 / 2 := by
    by_cases hre : 1 / 2 ≤ ρ.re
    · exact (lemma59_ext46_zero_analysis_at_contraction_closed hm hc hcmp hmodel χ ψ hD hψ
        hsmall hre (by linarith [(abs_le.mp hslab).2]) hρ.2 hA).1
    · have hrΩ := lemma59_ext48_omega_reflection hρ
      have hrP := lemma48_actual_product_reflected_zero χ ψ hL hψ.1
        (lemma59_ext48_omega_height_pos hL hρ) hzero
      have hrA : lemma45ActualA χ ψ (1 - conj ρ) = 0 := by
        change lemma48ActualProduct χ ψ (1 - conj ρ) / _ = 0
        rw [hrP, zero_div]
      have hr := lemma59_ext46_zero_analysis_at_contraction_closed hm hc hcmp hmodel χ ψ hD hψ
        hsmall (ρ := 1 - conj ρ)
        (by simp only [sub_re, one_re, conj_re]; linarith)
        (by simp only [sub_re, one_re, conj_re]; linarith [(abs_le.mp hslab).1])
        hrΩ.2 hrA
      have he := hr.1
      simp only [sub_re, one_re, conj_re] at he
      linarith
  have ha := (lemma46_alpha_parameters hD).1
  have hz := lemma59_ext46_zero_analysis_at_contraction_closed hm hc hcmp hmodel χ ψ hD hψ
    hsmall (by rw [hbeta]) (by rw [hbeta]; linarith [sq_nonneg (lemma44PaperAlpha D)]) hρ.2 hA
  have hreg := lemma59_ext48_thin_slab_regions hD hρ hslab
  have hF := lemma59_extended_F_ne_zero χ ψ ρ hL100 hψ.2 hreg.2.1
  have hρne : ρ ≠ 1 := by intro he; rw [he] at hbeta; norm_num at hbeta
  have hpd := (proposition22_actual_product_analyticAt χ ψ hρne).differentiableAt
  have hfd := lemma44_short_polynomial_differentiable χ ψ ρ
  have hderiv : deriv (lemma45ActualA χ ψ) ρ =
      (deriv (lemma48ActualProduct χ ψ) ρ *
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) ρ -
        lemma48ActualProduct χ ψ ρ *
          deriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) ρ) /
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) ρ ^ 2 :=
    deriv_div hpd hfd hF
  refine ⟨hbeta, ?_, ?_⟩
  · intro hd
    apply hz.2.1
    rw [hderiv, hd, hzero]
    simp
  · intro w hw hwR hzw
    have hcenter : (1 / 2 : ℂ) + I * (ρ.im : ℂ) = ρ := by
      apply Complex.ext <;> simp [hbeta]
    apply hz.2.2 w hw hwR
    rw [hcenter]
    change lemma48ActualProduct χ ψ (ρ + w) / _ = 0
    rw [hzw, zero_div]

open Complex in
theorem lemma59_ext48_actual_inverse_factor_approximation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ : ℂ} (hρ : Lemma59ExtendedZeroOmega D ρ) (hzero : lemma48ActualProduct χ ψ ρ = 0) :
    ‖(lemma44ActualZtilde χ ψ ρ)⁻¹ +
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) ρ *
        lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - ρ)‖ ≤
      lemma48ErrorConstant * lemma23PaperL D ^ (-100 : ℤ) := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let L := lemma23PaperL D
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) ρ
  let G := lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) ρ
  let Fr := lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - ρ)
  let Z := lemma44ActualZtilde χ ψ ρ
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hLp : 0 < L := by dsimp [L]; linarith
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hr := lemma59_ext48_thin_slab_regions hD hρ
    (lemma59_ext48_actual_zero_in_thin_slab χ ψ hD hψ hρ hzero)
  have hZne : Z ≠ 0 := lemma44ActualZtilde_ne_zero χ ψ hL hψ.1
    (lemma59_ext48_omega_height_pos hL hρ)
  have hZi := lemma59_ext48_actual_Z_inv_bound χ ψ hD hψ hρ hzero
  change ‖Z⁻¹‖ ≤ Real.exp 3 at hZi
  have h41 := lemma59_ext_good_FG_bound χ ψ ρ hL100 hψ hr.2.1
  have hG : ‖G‖ ≤ 2 * L ^ 79 := by
    change ‖F‖ + ‖G‖ ≤ 2 * L ^ 79 at h41
    linarith [norm_nonneg F]
  have h42 := lemma59_ext_good_product_bound χ ψ ρ hL100 hψ hr.2.1
  have hFG : ‖1 - F * G‖ ≤ 4 * L ^ (-227 : ℤ) := by
    rw [norm_sub_rev]
    exact h42
  have h44 := lemma59_ext44_actual_approximate_functional_equation χ ψ hD hψ hr.1
  change ‖lemma48ActualProduct χ ψ ρ - (F + Z * Fr)‖ ≤
    lemma44ErrorConstant * L ^ (-179 : ℤ) at h44
  rw [hzero, zero_sub, norm_neg] at h44
  have hid : Z⁻¹ + G * Fr =
      Z⁻¹ * (1 - F * G) + Z⁻¹ * G * (F + Z * Fr) := by
    field_simp
    ring
  have hfirst : ‖Z⁻¹ * (1 - F * G)‖ ≤
      Real.exp 3 * (4 * L ^ (-227 : ℤ)) := by
    rw [norm_mul]
    exact mul_le_mul hZi hFG (norm_nonneg _) (Real.exp_nonneg _)
  have hsecond : ‖Z⁻¹ * G * (F + Z * Fr)‖ ≤
      Real.exp 3 * (2 * L ^ 79) * (lemma44ErrorConstant * L ^ (-179 : ℤ)) := by
    simp only [norm_mul]
    apply mul_le_mul
      (mul_le_mul hZi hG (norm_nonneg _) (Real.exp_nonneg _)) h44
      (norm_nonneg _) (by positivity)
  have hpow : L ^ 79 * L ^ (-179 : ℤ) = L ^ (-100 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLp.ne']
    norm_num
  have hpowle : L ^ (-227 : ℤ) ≤ L ^ (-100 : ℤ) :=
    zpow_le_zpow_right₀ hL1 (by norm_num)
  change ‖Z⁻¹ + G * Fr‖ ≤ _
  rw [hid]
  calc
    _ ≤ ‖Z⁻¹ * (1 - F * G)‖ + ‖Z⁻¹ * G * (F + Z * Fr)‖ := norm_add_le _ _
    _ ≤ Real.exp 3 * (4 * L ^ (-227 : ℤ)) +
        Real.exp 3 * (2 * L ^ 79) * (lemma44ErrorConstant * L ^ (-179 : ℤ)) :=
      add_le_add hfirst hsecond
    _ ≤ Real.exp 3 * (4 * L ^ (-100 : ℤ)) +
        Real.exp 3 * (2 * L ^ 79) * (lemma44ErrorConstant * L ^ (-179 : ℤ)) := by
      gcongr
    _ = lemma48ErrorConstant * L ^ (-100 : ℤ) := by
      dsimp only [lemma48ErrorConstant]
      calc
        _ = Real.exp 3 * 4 * L ^ (-100 : ℤ) +
            Real.exp 3 * 2 * lemma44ErrorConstant * (L ^ 79 * L ^ (-179 : ℤ)) := by ring
        _ = _ := by rw [hpow]; ring

open Complex in
theorem lemma59_ext48_at_explicit_constant {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ : ℂ} (hρ : Lemma59ExtendedZeroOmega D ρ) (hzero : lemma48ActualProduct χ ψ ρ = 0) :
    ‖(lemma44ActualZtilde χ ψ ρ)⁻¹ +
      lemma23ActualSectionFourG χ (fun n => ψ (n : ZMod p)) ρ *
        lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - ρ)‖ ≤
      (3 : ℝ) ^ 65 * lemma23PaperL D ^ (-100 : ℤ) := by
  have hL100 : 100 ≤ lemma23PaperL D := by
    have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
    have hh := Real.log_le_self (by linarith only [hp.1] : 0 ≤ lemma23PaperL D)
    linarith only [hp.2,hh]
  have hheightmargin := lemma59_extended_height_margin (by linarith only [hL100])
  have hL20nonneg := pow_nonneg (by linarith only [hL100] : 0 ≤ lemma23PaperL D) 20
  exact (lemma59_ext48_actual_inverse_factor_approximation χ ψ hD hψ hρ hzero).trans
    (mul_le_mul_of_nonneg_right lemma48_error_constant_le (by positivity))

open Complex in
theorem lemma59_ext48_proved : Lemma59ExtendedLemma48Target := by
  refine ⟨(3 : ℝ) ^ 65, by positivity,
    lemma23SectionFourModulusThreshold, ?_⟩
  intro D p hp χ ψ hD hψ ρ hρ hzero
  exact lemma59_ext48_at_explicit_constant χ ψ hD hψ hρ hzero

open Complex in
lemma lemma59_uniform_extended_actual_product_zeros :
    ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ,
    ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi1 χ ψ →
      lemma44PaperAlpha D / 2 ≤ lemma46InnerRadius D c ∧
      0 < lemma46InnerRadius D c ∧
      ∀ {ρ : ℂ}, Lemma59ExtendedZeroOmega D ρ → lemma48ActualProduct χ ψ ρ = 0 →
        ρ.re = 1 / 2 ∧ deriv (lemma48ActualProduct χ ψ) ρ ≠ 0 ∧
        ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
          lemma48ActualProduct χ ψ (ρ + w) ≠ 0 := by
  obtain ⟨m,hm,hmodel⟩ := lemma46_model_uniform_inner_boundary
  let c := (lemma46ModelErrorConstant + 1) / m
  have hc : 0 < c := div_pos (by linarith [lemma46_model_error_constant_pos]) hm
  have hcmp : lemma46ModelErrorConstant < m * c := by
    dsimp [c]
    rw [mul_div_cancel₀ _ hm.ne']
    linarith
  obtain ⟨D₀,hD₀,hsmall⟩ := lemma46_exists_contraction_threshold hc
  refine ⟨c,hc,D₀,?_⟩
  intro D p _ χ ψ hD hψ
  have hr := lemma46_inner_radius_bounds (hD₀.trans hD) hc (hsmall D hD)
  refine ⟨hr.1,hr.2.1,?_⟩
  intro ρ hρ hz
  exact lemma59_ext_prop22_actual_zero_analysis hm hc hcmp hmodel χ ψ
    (hD₀.trans hD) hψ (hsmall D hD) hρ hz

end ZhangLS.Spec
