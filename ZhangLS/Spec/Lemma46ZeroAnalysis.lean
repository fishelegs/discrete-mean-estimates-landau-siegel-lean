import ZhangLS.Spec.Lemma46RoucheLocal
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Lemma 4.6: critical-line position, simplicity, and the inner gap -/

namespace ZhangLS.Spec

open Complex Metric Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

theorem lemma46_zero_analysis_at_contraction_closed {m c : ℝ}
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
    ρ.re = 1 / 2 ∧ deriv (lemma45ActualA χ ψ) ρ ≠ 0 ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
        lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) ≠ 0 := by
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
    lemma46_actual_A_analyticOn_inner_disk χ ψ hD hψ
      (by simp [c₀]) (by simpa [c₀] using him) hR.2.2
  have hcount := lemma46_actual_rouche_count_one_closed hm hc hcmp hmodel χ ψ hD hψ
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
    have herr := lemma46_actual_model_approximation_closed χ ψ hD hψ hre hrehi him hzero
      (w := w) (by rw [hn]; exact hR.2.2)
    intro hfw
    change lemma45ActualA χ ψ (c₀ + w) = 0 at hfw
    change ‖lemma45ActualA χ ψ (c₀ + w) - _‖ ≤ _ at herr
    rw [hfw, zero_sub, norm_neg] at herr
    change _ ≤ lemma46ModelErrorConstant * a * lemma23PaperL D at herr
    nlinarith only [hb, herr, hmarg]
  have hsingle := lemma46_unique_simple_zero_of_count_one hR.2.1 hf hboundary hcount hxK hfx
  have hρstrip : Lemma46InLocalStrip D ρ :=
    lemma46_disk_subset_local_strip hD (c := c₀) (by simp [c₀])
      (by simpa [c₀] using him) (by
        rw [← hcρ, add_sub_cancel_left]
        nlinarith only [hxa, hp.1])
  have href := lemma46_actual_A_reflected_zero χ ψ hD hψ hρstrip hzero
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


/-- Original strict-boundary interface, preserved for existing callers. -/
theorem lemma46_zero_analysis_at_contraction {m c : ℝ}
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
    ρ.re = 1 / 2 ∧ deriv (lemma45ActualA χ ψ) ρ ≠ 0 ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
        lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) ≠ 0 := by
  exact lemma46_zero_analysis_at_contraction_closed hm hc hcmp hmodel χ ψ hD hψ hsmall hre hrehi.le him hzero

/-- Any fixed absolute contraction constant is small enough for all
sufficiently large moduli. This is the standing convention of the paper. -/
theorem lemma46_exists_contraction_threshold {c : ℝ} (hc : 0 < c) :
    ∃ D₀ : ℕ, lemma23SectionFourModulusThreshold ≤ D₀ ∧
      ∀ D : ℕ, D₀ ≤ D →
        c * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 / 2 := by
  have ht : Tendsto (fun D : ℕ => lemma23PaperL D) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp
    (ht.eventually (eventually_ge_atTop (2 * c * Real.pi + 200)))
  refine ⟨max lemma23SectionFourModulusThreshold N, le_max_left _ _, ?_⟩
  intro D hD
  have hsection : lemma23SectionFourModulusThreshold ≤ D := (le_max_left _ _).trans hD
  have hL := hN D ((le_max_right _ _).trans hD)
  let L := lemma23PaperL D
  let a := lemma44PaperAlpha D
  have hLp : 0 < L := by linarith [(lemma45_parameters_at_threshold hsection).1]
  have hL1 : 1 ≤ L := by linarith [(lemma45_parameters_at_threshold hsection).1]
  have h8 : L ≤ L ^ 8 := le_self_pow₀ hL1 (by norm_num)
  have ha : a * L ^ 9 = Real.pi := by
    dsimp [a, lemma44PaperAlpha, lemma23PaperP, L]
    rw [Real.log_exp]
    field_simp [show lemma23PaperL D ≠ 0 from hLp.ne']
  have he : c * a * L * L ^ 8 = c * Real.pi := by rw [← ha]; ring
  have h8lo : 2 * c * Real.pi ≤ L ^ 8 := by
    change 2 * c * Real.pi + 200 ≤ L at hL
    linarith
  have hm : c * a * L * L ^ 8 ≤ (1 / 2) * L ^ 8 := by rw [he]; linarith
  exact (mul_le_mul_iff_left₀ (pow_pos hLp 8)).mp hm

/-- The original statement, retaining only its genuine hypotheses and
the paper's sufficiently-large-modulus convention. The constant and
threshold are uniform over characters and zeros. -/
def Lemma46Target : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ ρ : ℂ,
    1 / 2 ≤ ρ.re → ρ.re < 1 / 2 + lemma44PaperAlpha D ^ 2 →
    |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2 →
    lemma45ActualA χ ψ ρ = 0 →
    0 < lemma46InnerRadius D c ∧
    ρ.re = 1 / 2 ∧ deriv (lemma45ActualA χ ψ) ρ ≠ 0 ∧
      ∀ w : ℂ, 0 < ‖w‖ → ‖w‖ < lemma46InnerRadius D c →
        lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) ≠ 0

/-- Lemma 4.6, with all approximation, boundary, symmetry and multiplicity
obligations proved from actual good-character membership. -/
theorem lemma46_proved : Lemma46Target := by
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
  exact lemma46_zero_analysis_at_contraction hm hc hcmp hmodel χ ψ
    (hD₀.trans hD) hψ (hsmall D hD) hre hrehi him hzero

end ZhangLS.Spec
