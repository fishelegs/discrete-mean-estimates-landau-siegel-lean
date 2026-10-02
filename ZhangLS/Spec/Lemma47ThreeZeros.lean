import ZhangLS.Spec.Lemma47ModelApproximation
import ZhangLS.Spec.Lemma47ModelBoundary

/-! # Lemma 4.7: exactly three zeros in the expanded circle -/

namespace ZhangLS.Spec

open Complex Metric Set

set_option maxHeartbeats 1000000

noncomputable def lemma47OuterRadius (D : ℕ) (c : ℝ) : ℝ :=
  lemma44PaperAlpha D * (1 + c * lemma44PaperAlpha D * lemma23PaperL D)

theorem lemma47_outer_radius_bounds {D : ℕ} {c : ℝ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hc : 0 < c)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2) :
    lemma44PaperAlpha D < lemma47OuterRadius D c ∧
      lemma47OuterRadius D c ≤ (3 / 2) * lemma44PaperAlpha D ∧
      lemma47OuterRadius D c < 2 * lemma44PaperAlpha D := by
  have ha := (lemma46_alpha_parameters hD).1
  have hL : 0 < lemma23PaperL D := by linarith [(lemma45_parameters_at_threshold hD).1]
  have hpos : 0 < c * lemma44PaperAlpha D * lemma23PaperL D :=
    mul_pos (mul_pos hc ha) hL
  unfold lemma47OuterRadius
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith only [ha, hsmall, hpos]

theorem lemma47_actual_strict_outer_comparison {m c : ℝ}
    (hc : 0 < c) (hcmp : lemma47ModelErrorConstant < m * c)
    (hmodel : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ 3 / 2 →
      m * (‖z‖ - 1) ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hzero : lemma45ActualA χ ψ ρ = 0) :
    ∀ w ∈ sphere (0 : ℂ) (lemma47OuterRadius D c),
      ‖lemma45ActualA χ ψ (ρ + w) -
        lemma23ExponentialGapModel (Real.log (lemma23PaperP D)) w‖ <
          ‖lemma23ExponentialGapModel (Real.log (lemma23PaperP D)) w‖ := by
  let a := lemma44PaperAlpha D
  let L := lemma23PaperL D
  let M := Real.log (lemma23PaperP D)
  let R := lemma47OuterRadius D c
  have hap : 0 < a := (lemma46_alpha_parameters hD).1
  have hLp : 0 < L := by linarith [(lemma45_parameters_at_threshold hD).1]
  have hM : 0 < M := by simp only [M, lemma23PaperP, Real.log_exp]; positivity
  have haM : a * M = Real.pi := by
    dsimp [a, M, lemma44PaperAlpha]
    exact div_mul_cancel₀ _ hM.ne'
  have hR := lemma47_outer_radius_bounds hD hc hsmall
  intro w hw
  have hwn : ‖w‖ = R := by simpa [mem_sphere, dist_zero_right] using hw
  let u := w / (a : ℂ)
  have hun : ‖u‖ = 1 + c * a * L := by
    rw [norm_div, norm_real, Real.norm_of_nonneg hap.le, hwn]
    dsimp [R, lemma47OuterRadius]
    change a * (1 + c * a * L) / a = _
    field_simp [hap.ne']
  have hulo : 1 ≤ ‖u‖ := by
    rw [hun]
    linarith [mul_pos (mul_pos hc hap) hLp]
  have huhi : ‖u‖ ≤ 3 / 2 := by
    rw [hun]
    change c * a * L ≤ 1 / 2 at hsmall
    linarith
  have heq : lemma23ExponentialGapModel M w = lemma23ExponentialGapModel Real.pi u := by
    unfold lemma23ExponentialGapModel
    congr 2
    dsimp [u]
    rw [← haM]
    push_cast
    field_simp [show (a : ℂ) ≠ 0 by exact_mod_cast hap.ne']
  have hb := hmodel u hulo huhi
  rw [hun, ← heq] at hb
  have he := lemma47_actual_model_approximation χ ψ hD hψ hre him hzero
    (w := w) (by rw [hwn]; exact hR.2.2)
  change ‖lemma45ActualA χ ψ (ρ + w) - lemma23ExponentialGapModel M w‖ ≤
    lemma47ModelErrorConstant * a * L at he
  apply he.trans_lt
  have hprod := mul_lt_mul_of_pos_right hcmp (mul_pos hap hLp)
  nlinarith only [hb, hprod]

theorem lemma47_actual_three_zeros_at_expansion {m c : ℝ}
    (hc : 0 < c) (hcmp : lemma47ModelErrorConstant < m * c)
    (hmodel : ∀ z : ℂ, 1 ≤ ‖z‖ → ‖z‖ ≤ 3 / 2 →
      m * (‖z‖ - 1) ≤ ‖lemma23ExponentialGapModel Real.pi z‖)
    {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    (hsmall : c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2)
    {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hzero : lemma45ActualA χ ψ ρ = 0) :
    let f := fun w => lemma45ActualA χ ψ (ρ + w)
    let R := lemma47OuterRadius D c
    (∀ w ∈ sphere (0 : ℂ) R, f w ≠ 0) ∧
    (∑ z ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R)
      (MeromorphicOn.divisor f (closedBall 0 R))).toFinset,
      (((MeromorphicOn.divisor f (closedBall 0 R)) z).toNat : ℂ)) = 3 := by
  let f := fun w => lemma45ActualA χ ψ (ρ + w)
  let R := lemma47OuterRadius D c
  let M := Real.log (lemma23PaperP D)
  have hR := lemma47_outer_radius_bounds hD hc hsmall
  have hM : 0 < M := by
    simp only [M, lemma23PaperP, Real.log_exp]
    exact pow_pos (by linarith [(lemma45_parameters_at_threshold hD).1]) 9
  have hfa := lemma47_actual_A_analyticOn_outer_disk χ ψ hD hψ hre him hR.2.2
  have hclose := lemma47_actual_strict_outer_comparison hc hcmp hmodel χ ψ hD hψ
    hsmall hre him hzero
  constructor
  · intro w hw hfw
    have hb := hclose w hw
    change ‖f w - _‖ < _ at hb
    change f w = 0 at hfw
    rw [hfw, zero_sub, norm_neg] at hb
    exact lt_irrefl _ hb
  · exact lemma23_rouche_model_divisor_sum_eq_three hM
      (by simpa only [lemma44PaperAlpha] using hR.1)
      (by simpa only [lemma44PaperAlpha] using hR.2.2) f hfa hclose

/-- The original Lemma 4.7. Boundary nonvanishing makes the closed-disk
divisor count exactly the count strictly inside the paper's circle.
The absolute constant and threshold precede all characters and zeros. -/
def Lemma47Target : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ ρ : ℂ,
    ρ.re = 1 / 2 →
    |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2 →
    lemma45ActualA χ ψ ρ = 0 →
    let f := fun w => lemma45ActualA χ ψ (ρ + w)
    let R := lemma47OuterRadius D c
    lemma44PaperAlpha D < R ∧ R < 2 * lemma44PaperAlpha D ∧
    (∀ w ∈ sphere (0 : ℂ) R, f w ≠ 0) ∧
    (∑ z ∈ (lemma23_support_finite_of_isCompact (isCompact_closedBall 0 R)
      (MeromorphicOn.divisor f (closedBall 0 R))).toFinset,
      (((MeromorphicOn.divisor f (closedBall 0 R)) z).toNat : ℂ)) = 3

theorem lemma47_proved : Lemma47Target := by
  obtain ⟨m, hm, hmodel⟩ := lemma47_model_uniform_outer_boundary
  let c := (lemma47ModelErrorConstant + 1) / m
  have hc : 0 < c := div_pos (by linarith [lemma47_model_error_constant_pos]) hm
  have hcmp : lemma47ModelErrorConstant < m * c := by
    dsimp [c]
    rw [mul_div_cancel₀ _ hm.ne']
    linarith
  obtain ⟨D₀, hD₀, hsmall⟩ := lemma46_exists_contraction_threshold hc
  refine ⟨c, hc, D₀, ?_⟩
  intro D p hp χ ψ hD hψ ρ hre him hzero
  have hsection := hD₀.trans hD
  have hR := lemma47_outer_radius_bounds hsection hc (hsmall D hD)
  exact ⟨hR.1, hR.2.2, lemma47_actual_three_zeros_at_expansion hc hcmp hmodel
    χ ψ hsection hψ (hsmall D hD) hre him hzero⟩

end ZhangLS.Spec
