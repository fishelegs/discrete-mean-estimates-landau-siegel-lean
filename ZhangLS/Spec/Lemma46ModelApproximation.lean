import ZhangLS.Spec.Lemma46LocalGeometry
import ZhangLS.Spec.Lemma23ModelZeros

/-! # The actual local model comparison in Lemma 4.6 -/

namespace ZhangLS.Spec

open Complex Metric Set

set_option maxHeartbeats 2000000

/-- An absolute error constant, independent of the circle contraction. -/
noncomputable def lemma46ModelErrorConstant : ℝ :=
  1 + Real.exp 8 * (1 + 4 * 1100000)

theorem lemma46_model_error_constant_pos : 0 < lemma46ModelErrorConstant := by
  unfold lemma46ModelErrorConstant
  positivity

/-- Equation (4.12) on the inner disk. This smaller domain already
contains every contracted circle used in Lemma 4.6. -/
theorem lemma46_actual_model_approximation_closed {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re)
    (hrehi : ρ.re ≤ 1 / 2 + lemma44PaperAlpha D ^ 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hzero : lemma45ActualA χ ψ ρ = 0)
    {w : ℂ} (hw : ‖w‖ < lemma44PaperAlpha D) :
    ‖lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) -
      lemma23ExponentialGapModel (Real.log (lemma23PaperP D)) w‖ ≤
        lemma46ModelErrorConstant * lemma44PaperAlpha D * lemma23PaperL D := by
  let L := lemma23PaperL D
  let a := lemma44PaperAlpha D
  let M := Real.log (lemma23PaperP D)
  let c : ℂ := (1 / 2 : ℂ) + I * (ρ.im : ℂ)
  let s := c + w
  let δ := ρ.re - 1 / 2
  have hp := lemma46_alpha_parameters hD
  change 0 < a ∧ a < 1 / 4 ∧ 2 * a < L⁻¹ ∧
    1100000 * a * L ≤ 1 ∧ (L ^ 9)⁻¹ / 4 ≤ a * L at hp
  have hL : 200 ≤ L := (lemma45_parameters_at_threshold hD).1
  have hLp : 0 < L := by linarith
  have hM : M = L ^ 9 := by simp [M, lemma23PaperP, L]
  have haM : a * M = Real.pi := by
    change lemma44PaperAlpha D * Real.log (lemma23PaperP D) = Real.pi
    unfold lemma44PaperAlpha
    field_simp [show Real.log (lemma23PaperP D) ≠ 0 by change M ≠ 0; rw [hM]; positivity]
  have hδ : 0 ≤ δ ∧ δ ≤ a ^ 2 := ⟨by dsimp [δ]; linarith, by dsimp [δ, a]; linarith⟩
  have hc : c.re = 1 / 2 := by simp [c]
  have hci : |c.im - (lemma23PaperCenter D).im| < L ^ 405 + 2 := by
    simpa [c, L] using him
  have hrho : ρ - c = (δ : ℂ) := by
    apply Complex.ext <;> simp [c, δ]
  have hrhon : ‖ρ - c‖ = δ := by rw [hrho, norm_real, Real.norm_of_nonneg hδ.1]
  have hrhoa : ‖ρ - c‖ < a := by
    rw [hrhon]
    nlinarith only [hδ.2, hp.1, hp.2.1]
  have hs : ‖s - c‖ < a := by simpa [s] using hw
  have hx : ρ ∈ ball c (2 * a) := by
    rw [mem_ball, dist_eq_norm]
    linarith only [hrhoa, hp.1]
  have hy : s ∈ ball c (2 * a) := by
    rw [mem_ball, dist_eq_norm]
    linarith only [hs, hp.1]
  have hstrip (z : ℂ) (hz : z ∈ ball c (2 * a)) : Lemma46InLocalStrip D z :=
    lemma46_disk_subset_local_strip hD hc hci (by
      simpa only [mem_ball, dist_eq_norm] using hz)
  obtain ⟨e, he, heq⟩ := lemma46_exponential_transport_on_ball
    (a := ((2 * M : ℝ) : ℂ)) (by linarith only [hp.1] : 0 < 2 * a)
    (fun z hz => (lemma46_actual_B_differentiable_ne_zero χ ψ hD hψ (hstrip z hz)).1)
    (fun z hz => (lemma46_actual_B_differentiable_ne_zero χ ψ hD hψ (hstrip z hz)).2)
    (fun z hz => lemma46_equation411 χ ψ hD hψ (hstrip z hz)) hx hy
  change ‖e‖ ≤ 341600 * L * ‖s - ρ‖ at he
  have hdist : ‖s - ρ‖ ≤ 3 * a := by
    have ht := norm_sub_le (s - c) (ρ - c)
    rw [sub_sub_sub_cancel_right] at ht
    linarith only [ht, hs, hrhoa, hp.1]
  have he' : ‖e‖ ≤ 1024800 * a * L := by
    have hm := mul_le_mul_of_nonneg_left hdist (by positivity : 0 ≤ 341600 * L)
    nlinarith only [he, hm]
  let e' := e + ((2 * M * δ : ℝ) : ℂ)
  have hδM : 2 * M * δ ≤ 8 * a * L := by
    have hm := mul_le_mul_of_nonneg_left hδ.2
      (by rw [hM]; positivity : 0 ≤ 2 * M)
    have he : 2 * M * a ^ 2 = 2 * Real.pi * a := by rw [← haM]; ring
    rw [he] at hm
    have hpi := Real.pi_le_four
    nlinarith only [hm, hpi, hL, hp.1]
  have he'n : ‖e'‖ ≤ 1100000 * a * L := by
    have ht := norm_add_le e (((2 * M * δ : ℝ) : ℂ))
    rw [norm_real, Real.norm_of_nonneg (by rw [hM]; positivity)] at ht
    change ‖e'‖ ≤ _
    nlinarith only [ht, he', hδM, mul_pos hp.1 hLp]
  have he'1 : ‖e'‖ ≤ 1 := he'n.trans hp.2.2.2.1
  have hexp : ‖Complex.exp e' - 1‖ ≤ 2 * 1100000 * a * L :=
    (Complex.norm_exp_sub_one_le he'1).trans (by nlinarith only [he'n])
  let v := Complex.exp (-2 * w * (M : ℂ))
  have hv : ‖v‖ ≤ Real.exp 8 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hm : ‖-2 * w * (M : ℂ)‖ ≤ 2 * Real.pi := by
      rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg (by rw [hM]; positivity)]
      norm_num
      nlinarith only [hw, haM, show 0 < M by rw [hM]; positivity]
    exact (re_le_norm _).trans (hm.trans (by linarith [Real.pi_le_four]))
  have hBs : lemma45ActualB χ ψ s = lemma45ActualB χ ψ ρ * v * Complex.exp e' := by
    have heB := (div_eq_iff
      (lemma46_actual_B_differentiable_ne_zero χ ψ hD hψ (hstrip ρ hx)).2).mp heq
    have hsρ : s - ρ = w - (δ : ℂ) := by rw [← hrho]; dsimp [s]; ring
    rw [hsρ] at heB
    have harg : -((2 * M : ℝ) : ℂ) * (w - (δ : ℂ)) + e =
        -2 * w * (M : ℂ) + e' := by dsimp [e']; push_cast; ring
    rw [harg, Complex.exp_add] at heB
    dsimp [v]
    linear_combination heB
  have hregρ := lemma46_inner_disk_regions hD hc hci hrhoa
  have hregs := lemma46_inner_disk_regions hD hc hci hs
  have herrorρ := (lemma45_equation410 χ ψ hD hψ hregρ.1 hregρ.2).trans
    (lemma45_normalized_error_budget (by linarith : 3 ≤ lemma23PaperL D))
  have herrors := (lemma45_equation410 χ ψ hD hψ hregs.1 hregs.2).trans
    (lemma45_normalized_error_budget (by linarith : 3 ≤ lemma23PaperL D))
  have hρ : ‖lemma45ActualB χ ψ ρ + 1‖ ≤ a * L := by
    rw [hzero, zero_sub, norm_neg, add_comm] at herrorρ
    exact herrorρ.trans hp.2.2.2.2
  have hρ2 : ‖lemma45ActualB χ ψ ρ‖ ≤ 2 := by
    have ht := norm_sub_le (lemma45ActualB χ ψ ρ + 1) (1 : ℂ)
    rw [add_sub_cancel_right, norm_one] at ht
    have haL : a * L ≤ 1 := by
      nlinarith only [hp.2.2.2.1, mul_pos hp.1 hLp]
    linarith
  have hBerr : ‖lemma45ActualB χ ψ s + v‖ ≤
      Real.exp 8 * (1 + 4 * 1100000) * a * L := by
    rw [hBs]
    have heq' : lemma45ActualB χ ψ ρ * v * Complex.exp e' + v =
        v * ((lemma45ActualB χ ψ ρ + 1) +
          lemma45ActualB χ ψ ρ * (Complex.exp e' - 1)) := by ring
    rw [heq', norm_mul]
    have ht := norm_add_le (lemma45ActualB χ ψ ρ + 1)
      (lemma45ActualB χ ψ ρ * (Complex.exp e' - 1))
    rw [norm_mul] at ht
    have hm := mul_le_mul hρ2 hexp (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have hi : ‖(lemma45ActualB χ ψ ρ + 1) +
        lemma45ActualB χ ψ ρ * (Complex.exp e' - 1)‖ ≤
        (1 + 4 * 1100000) * a * L := by nlinarith only [ht, hρ, hm]
    have hb := mul_le_mul hv hi (norm_nonneg _) (Real.exp_nonneg 8)
    nlinarith only [hb]
  have hE : ‖lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s)‖ ≤ a * L :=
    herrors.trans hp.2.2.2.2
  have hid : lemma45ActualA χ ψ s - (1 - v) =
      (lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s)) +
      (lemma45ActualB χ ψ s + v) := by ring
  change ‖lemma45ActualA χ ψ s - (1 - v)‖ ≤ _
  rw [hid]
  have ht := norm_add_le
    (lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s))
    (lemma45ActualB χ ψ s + v)
  unfold lemma46ModelErrorConstant
  nlinarith only [ht, hE, hBerr]

/-- Original strict-boundary interface, preserved for existing callers. -/
theorem lemma46_actual_model_approximation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ : ℂ} (hre : 1 / 2 ≤ ρ.re)
    (hrehi : ρ.re < 1 / 2 + lemma44PaperAlpha D ^ 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hzero : lemma45ActualA χ ψ ρ = 0)
    {w : ℂ} (hw : ‖w‖ < lemma44PaperAlpha D) :
    ‖lemma45ActualA χ ψ ((1 / 2 : ℂ) + I * (ρ.im : ℂ) + w) -
      lemma23ExponentialGapModel (Real.log (lemma23PaperP D)) w‖ ≤
        lemma46ModelErrorConstant * lemma44PaperAlpha D * lemma23PaperL D := by
  exact lemma46_actual_model_approximation_closed χ ψ hD hψ hre hrehi.le him hzero hw


end ZhangLS.Spec
