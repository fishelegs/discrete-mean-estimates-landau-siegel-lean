import ZhangLS.Spec.Lemma47Reflection

/-! # Analyticity and region inclusions on the expanded disk -/

namespace ZhangLS.Spec

open Complex ComplexConjugate Metric Set

set_option maxHeartbeats 1000000

theorem lemma47_outer_disk_omega1 {D : ℕ} {c s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hc : c.re = 1 / 2)
    (hci : |c.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hs : ‖s - c‖ < 2 * lemma44PaperAlpha D) : Lemma23InOmega1 D s := by
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2]) (by linarith only [hp.1])
  exact lemma23_omega2_disk_subset_omega1 hp.1 hp.2
    (lemma46_local_strip_regions hD (lemma46_disk_subset_local_strip hD hc hci hs)).1
    (mem_ball_self hR)

theorem lemma47_outer_right_omega3 {D : ℕ} {c s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hc : c.re = 1 / 2)
    (hci : |c.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hs : ‖s - c‖ < 2 * lemma44PaperAlpha D) (hre : 1 / 2 ≤ s.re) :
    Lemma44InOmega3 D s := by
  have ha := lemma46_alpha_parameters hD
  have hstrip := lemma46_disk_subset_local_strip hD hc hci hs
  have hr := (abs_re_le_norm (s - c)).trans_lt hs
  simp only [sub_re, hc] at hr
  refine ⟨by linarith only [ha.1, hre], ?_, hstrip.2⟩
  have hu := (abs_lt.mp hr).2
  linarith only [hu, ha.2.1]

theorem lemma47_reflection_distance {c s : ℂ} (hc : c.re = 1 / 2) :
    ‖(1 - conj s) - c‖ = ‖s - c‖ := by
  have he : (1 - conj s) - c = -conj (s - c) := by
    apply Complex.ext <;> simp [hc] <;> ring
  rw [he, norm_neg, norm_conj]

theorem lemma47_actual_A_analyticOn_outer_disk {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {c : ℂ} (hc : c.re = 1 / 2)
    (hci : |c.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    {R : ℝ} (hR : R < 2 * lemma44PaperAlpha D) :
    AnalyticOnNhd ℂ (fun w => lemma45ActualA χ ψ (c + w)) (closedBall 0 R) := by
  intro w hw
  have hs : ‖c + w - c‖ < 2 * lemma44PaperAlpha D := by
    simp only [add_sub_cancel_left]
    exact lt_of_le_of_lt (by simpa [mem_closedBall, dist_zero_right] using hw) hR
  have hω := lemma47_outer_disk_omega1 hD hc hci hs
  have hL := (lemma23_sectionFour_parameters_at_explicit_threshold hD).1
  have hF := lemma23_omega1_F_ne_zero χ ψ (c + w) hL hψ.2 hω
  have hstrip := lemma46_disk_subset_local_strip hD hc hci hs
  have him := (lemma46_local_strip_regions hD hstrip).2.2.2
  have hne : c + w ≠ 1 := by
    intro he
    rw [he] at him
    norm_num at him
  exact (lemma46_actual_A_analyticAt χ ψ hne hF).comp (by fun_prop)

/-- Exact transport of the normalized remainder. -/
theorem lemma47_actual_error_reflection {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma46InLocalStrip D s) :
    lemma45ActualA χ ψ s - (1 + lemma45ActualB χ ψ s) =
      lemma45ActualB χ ψ s * conj (lemma45ActualA χ ψ (1 - conj s) -
        (1 + lemma45ActualB χ ψ (1 - conj s))) := by
  obtain ⟨hA, hB⟩ := lemma47_actual_normalized_reflection χ ψ hD hψ hs
  simp only [map_sub, map_add, map_one]
  rw [hA]
  linear_combination hB

end ZhangLS.Spec
