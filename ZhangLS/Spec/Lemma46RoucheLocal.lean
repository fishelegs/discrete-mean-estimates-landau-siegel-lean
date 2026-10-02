import ZhangLS.Spec.Lemma46ModelApproximation
import ZhangLS.Spec.Lemma46ModelBoundary
import ZhangLS.Spec.Lemma46AnalyticSymmetry
import ZhangLS.Spec.Lemma46SingleZero

/-! # Strict Rouché comparison for the actual inner disk -/

namespace ZhangLS.Spec

open Complex Metric Set

set_option maxHeartbeats 1000000

noncomputable def lemma46InnerRadius (D : ℕ) (c : ℝ) : ℝ :=
  lemma44PaperAlpha D * (1 - c * lemma44PaperAlpha D * lemma23PaperL D)

theorem lemma46_inner_radius_bounds {D : ℕ} {c : ℝ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hc : 0 < c)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2) :
    lemma44PaperAlpha D / 2 ≤ lemma46InnerRadius D c ∧
      0 < lemma46InnerRadius D c ∧ lemma46InnerRadius D c < lemma44PaperAlpha D := by
  have hp := lemma46_alpha_parameters hD
  have hL : 0 < lemma23PaperL D := by linarith [(lemma45_parameters_at_threshold hD).1]
  have hpos : 0 < c * lemma44PaperAlpha D * lemma23PaperL D :=
    mul_pos (mul_pos hc hp.1) hL
  unfold lemma46InnerRadius
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith only [hp.1, hsmall, hpos]

theorem lemma46_actual_rouche_count_one_closed {m c : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hcmp : lemma46ModelErrorConstant < m * c)
    (hmodel : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      m * (1 - ‖z‖) ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re)
    (hrehi : ρ.re ≤ 1 / 2 + lemma44PaperAlpha D ^ 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hzero : lemma45ActualA χ ψ ρ = 0) :
    let f := fun w => lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w)
    let R := lemma46InnerRadius D c
    (∑ z ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R)
      (MeromorphicOn.divisor f (closedBall 0 R))).toFinset,
      (((MeromorphicOn.divisor f (closedBall 0 R)) z).toNat : ℂ)) = 1 := by
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
    lemma46_actual_A_analyticOn_inner_disk χ ψ hD hψ
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
  have he := lemma46_actual_model_approximation_closed χ ψ hD hψ hre hrehi him hzero hwa
  change ‖f w - lemma23ExponentialGapModel M w‖ ≤ lemma46ModelErrorConstant * a * L at he
  apply he.trans_lt
  have hprod := mul_lt_mul_of_pos_right hcmp (mul_pos hp.1 hLp)
  have he' : m * c * (a * L) = m * (1 - (1 - c * a * L)) := by ring
  rw [he'] at hprod
  nlinarith only [hb, hprod]

/-- Original strict-boundary interface, preserved for existing callers. -/
theorem lemma46_actual_rouche_count_one {m c : ℝ}
    (hm : 0 < m) (hc : 0 < c) (hcmp : lemma46ModelErrorConstant < m * c)
    (hmodel : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → ‖z‖ ≤ 1 →
      m * (1 - ‖z‖) ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re)
    (hrehi : ρ.re < 1 / 2 + lemma44PaperAlpha D ^ 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hzero : lemma45ActualA χ ψ ρ = 0) :
    let f := fun w => lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w)
    let R := lemma46InnerRadius D c
    (∑ z ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R)
      (MeromorphicOn.divisor f (closedBall 0 R))).toFinset,
      (((MeromorphicOn.divisor f (closedBall 0 R)) z).toNat : ℂ)) = 1 := by
  exact lemma46_actual_rouche_count_one_closed hm hc hcmp hmodel χ ψ hD hψ hsmall hre hrehi.le him hzero


end ZhangLS.Spec
