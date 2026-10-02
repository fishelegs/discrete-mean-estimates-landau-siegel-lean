import ZhangLS.Spec.Lemma47OuterGeometry

/-! # Equation (4.12) on the full disk of radius `2α`

For a genuine critical-line zero, exponential transport controls `B`.
Reflection supplies (4.10) on the left portion outside `Ω₃`.
-/

namespace ZhangLS.Spec

open Complex ComplexConjugate Metric Set

set_option maxHeartbeats 2000000

noncomputable def lemma47ModelErrorConstant : ℝ :=
  2 * Real.exp 17 + Real.exp 16 * (1 + 4 * 1100000)

theorem lemma47_model_error_constant_pos : 0 < lemma47ModelErrorConstant := by
  unfold lemma47ModelErrorConstant
  positivity

theorem lemma47_actual_model_approximation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {ρ : ℂ} (hre : ρ.re = 1 / 2)
    (him : |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hzero : lemma45ActualA χ ψ ρ = 0)
    {w : ℂ} (hw : ‖w‖ < 2 * lemma44PaperAlpha D) :
    ‖lemma45ActualA χ ψ (ρ + w) -
      lemma23ExponentialGapModel (Real.log (lemma23PaperP D)) w‖ ≤
        lemma47ModelErrorConstant * lemma44PaperAlpha D * lemma23PaperL D := by
  let L := lemma23PaperL D
  let a := lemma44PaperAlpha D
  let M := Real.log (lemma23PaperP D)
  let s := ρ + w
  have hp := lemma46_alpha_parameters hD
  change 0 < a ∧ a < 1 / 4 ∧ 2 * a < L⁻¹ ∧
    1100000 * a * L ≤ 1 ∧ (L ^ 9)⁻¹ / 4 ≤ a * L at hp
  have hL : 200 ≤ L := (lemma45_parameters_at_threshold hD).1
  have hLp : 0 < L := by linarith
  have hM : M = L ^ 9 := by simp [M, lemma23PaperP, L]
  have hMp : 0 < M := by rw [hM]; positivity
  have haM : a * M = Real.pi := by
    dsimp [a, M, lemma44PaperAlpha]
    exact div_mul_cancel₀ _ hMp.ne'
  have hs : ‖s - ρ‖ < 2 * a := by simpa [s] using hw
  have hx : ρ ∈ ball ρ (2 * a) := mem_ball_self (by linarith only [hp.1])
  have hy : s ∈ ball ρ (2 * a) := by simpa [mem_ball, dist_eq_norm] using hs
  have hstrip (z : ℂ) (hz : z ∈ ball ρ (2 * a)) : Lemma46InLocalStrip D z :=
    lemma46_disk_subset_local_strip hD hre him (by
      simpa only [mem_ball, dist_eq_norm] using hz)
  obtain ⟨e, he, heq⟩ := lemma46_exponential_transport_on_ball
    (a := ((2 * M : ℝ) : ℂ)) (by linarith only [hp.1] : 0 < 2 * a)
    (fun z hz => (lemma46_actual_B_differentiable_ne_zero χ ψ hD hψ (hstrip z hz)).1)
    (fun z hz => (lemma46_actual_B_differentiable_ne_zero χ ψ hD hψ (hstrip z hz)).2)
    (fun z hz => lemma46_equation411 χ ψ hD hψ (hstrip z hz)) hx hy
  change ‖e‖ ≤ 341600 * L * ‖s - ρ‖ at he
  have he' : ‖e‖ ≤ 1100000 * a * L := by
    have hm := mul_le_mul_of_nonneg_left hs.le (by positivity : 0 ≤ 341600 * L)
    nlinarith only [he, hm, mul_pos hp.1 hLp]
  have he1 : ‖e‖ ≤ 1 := he'.trans hp.2.2.2.1
  have hexp : ‖Complex.exp e - 1‖ ≤ 2 * 1100000 * a * L :=
    (Complex.norm_exp_sub_one_le he1).trans (by nlinarith only [he'])
  let v := Complex.exp (-2 * w * (M : ℂ))
  have hv : ‖v‖ ≤ Real.exp 16 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hm : ‖-2 * w * (M : ℂ)‖ ≤ 4 * Real.pi := by
      rw [norm_mul, norm_mul, norm_real, Real.norm_of_nonneg hMp.le]
      norm_num
      nlinarith only [hw, haM, hMp]
    exact (re_le_norm _).trans (hm.trans (by linarith [Real.pi_le_four]))
  have hBs : lemma45ActualB χ ψ s = lemma45ActualB χ ψ ρ * v * Complex.exp e := by
    have heB := (div_eq_iff
      (lemma46_actual_B_differentiable_ne_zero χ ψ hD hψ (hstrip ρ hx)).2).mp heq
    have hsρ : s - ρ = w := by simp [s]
    rw [hsρ] at heB
    have harg : -((2 * M : ℝ) : ℂ) * w + e = -2 * w * (M : ℂ) + e := by
      push_cast
      ring
    rw [harg, Complex.exp_add] at heB
    dsimp [v]
    linear_combination heB
  have hregρ := lemma46_inner_disk_regions hD hre him
    (by simpa using hp.1 : ‖ρ - ρ‖ < a)
  have herrorρ := (lemma45_equation410 χ ψ hD hψ hregρ.1 hregρ.2).trans
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
  have hBnorm : ‖lemma45ActualB χ ψ s‖ ≤ 2 * Real.exp 17 := by
    rw [hBs, norm_mul, norm_mul]
    have heen : ‖Complex.exp e‖ ≤ Real.exp 1 := by
      rw [Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((re_le_norm e).trans he1)
    have hmul := mul_le_mul (mul_le_mul hρ2 hv (norm_nonneg _) (by norm_num))
      heen (norm_nonneg _) (by positivity : 0 ≤ 2 * Real.exp 16)
    apply hmul.trans_eq
    rw [mul_assoc, ← Real.exp_add]
    norm_num
  have hBerr : ‖lemma45ActualB χ ψ s + v‖ ≤
      Real.exp 16 * (1 + 4 * 1100000) * a * L := by
    rw [hBs]
    have hid : lemma45ActualB χ ψ ρ * v * Complex.exp e + v =
        v * ((lemma45ActualB χ ψ ρ + 1) +
          lemma45ActualB χ ψ ρ * (Complex.exp e - 1)) := by ring
    rw [hid, norm_mul]
    have ht := norm_add_le (lemma45ActualB χ ψ ρ + 1)
      (lemma45ActualB χ ψ ρ * (Complex.exp e - 1))
    rw [norm_mul] at ht
    have hm := mul_le_mul hρ2 hexp (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
    have hi : ‖(lemma45ActualB χ ψ ρ + 1) +
        lemma45ActualB χ ψ ρ * (Complex.exp e - 1)‖ ≤
        (1 + 4 * 1100000) * a * L := by nlinarith only [ht, hρ, hm]
    have hb := mul_le_mul hv hi (norm_nonneg _) (Real.exp_nonneg 16)
    nlinarith only [hb]
  have hE : ‖lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s)‖ ≤
      2 * Real.exp 17 * a * L := by
    have hω := lemma47_outer_disk_omega1 hD hre him hs
    by_cases hright : 1 / 2 ≤ s.re
    · have he := (lemma45_equation410 χ ψ hD hψ
        (lemma47_outer_right_omega3 hD hre him hs hright) hω).trans
        (lemma45_normalized_error_budget (by linarith : 3 ≤ lemma23PaperL D))
      have hexp1 : 1 ≤ Real.exp 17 := Real.one_le_exp_iff.mpr (by norm_num)
      exact (he.trans hp.2.2.2.2).trans (by
        nlinarith only [hexp1, mul_pos hp.1 hLp])
    · have hrs : ‖(1 - conj s) - ρ‖ < 2 * a := by
        rw [lemma47_reflection_distance hre]
        exact hs
      have hrω := lemma47_outer_disk_omega1 hD hre him hrs
      have hr3 := lemma47_outer_right_omega3 hD hre him hrs
        (by simp only [sub_re, one_re, conj_re]; linarith)
      have her := (lemma45_equation410 χ ψ hD hψ hr3 hrω).trans
        (lemma45_normalized_error_budget (by linarith : 3 ≤ lemma23PaperL D))
      rw [lemma47_actual_error_reflection χ ψ hD hψ (hstrip s hy), norm_mul, norm_conj]
      have hb := mul_le_mul hBnorm (her.trans hp.2.2.2.2)
        (norm_nonneg _) (by positivity : 0 ≤ 2 * Real.exp 17)
      nlinarith only [hb]
  have hid : lemma45ActualA χ ψ s - (1 - v) =
      (lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s)) +
      (lemma45ActualB χ ψ s + v) := by ring
  change ‖lemma45ActualA χ ψ s - (1 - v)‖ ≤ _
  rw [hid]
  have ht := norm_add_le (lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s))
    (lemma45ActualB χ ψ s + v)
  unfold lemma47ModelErrorConstant
  nlinarith only [ht, hE, hBerr]

end ZhangLS.Spec
