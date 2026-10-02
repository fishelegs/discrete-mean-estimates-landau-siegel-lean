import ZhangLS.Spec.Lemma46ExponentialTransport

/-! # Regions and numerical margins for Lemma 4.6 -/

namespace ZhangLS.Spec

open Complex Metric Set

set_option maxHeartbeats 1000000

theorem lemma46_alpha_parameters {D : ℕ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) :
    0 < lemma44PaperAlpha D ∧ lemma44PaperAlpha D < 1 / 4 ∧
      2 * lemma44PaperAlpha D < (lemma23PaperL D)⁻¹ ∧
      1100000 * lemma44PaperAlpha D * lemma23PaperL D ≤ 1 ∧
      (lemma23PaperL D ^ 9)⁻¹ / 4 ≤ lemma44PaperAlpha D * lemma23PaperL D := by
  let L := lemma23PaperL D
  let a := lemma44PaperAlpha D
  have hL : 200 ≤ L := (lemma45_parameters_at_threshold hD).1
  have hLp : 0 < L := by linarith
  have ha : a = Real.pi / L ^ 9 := by
    simp only [a, lemma44PaperAlpha, lemma23PaperP, Real.log_exp, L]
  have ha9 : a * L ^ 9 = Real.pi := by rw [ha]; field_simp
  have h8 : 5000000 ≤ L ^ 8 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 200) hL 8
    norm_num at h
    linarith
  have h9 : 200 ≤ L ^ 9 :=
    hL.trans (le_self_pow₀ (by linarith : 1 ≤ L) (by norm_num))
  have hap : 0 < a := by rw [ha]; positivity
  have hasmall : a < 1 / 4 := by nlinarith only [ha9, h9, Real.pi_le_four]
  have h2 : 2 * a < L⁻¹ := by
    rw [inv_eq_one_div]
    apply (lt_div_iff₀ hLp).mpr
    have he : (2 * a * L) * L ^ 8 = 2 * Real.pi := by rw [← ha9]; ring
    nlinarith only [he, h8, Real.pi_le_four]
  have hsmall : 1100000 * a * L ≤ 1 := by
    have he : (1100000 * a * L) * L ^ 8 = 1100000 * Real.pi := by
      rw [← ha9]; ring
    nlinarith only [he, h8, Real.pi_le_four]
  have heps : (L ^ 9)⁻¹ / 4 ≤ a * L := by
    have he : a * L * L ^ 9 = Real.pi * L := by rw [← ha9]; ring
    have hi : (L ^ 9)⁻¹ / 4 * L ^ 9 = 1 / 4 := by field_simp
    have hmul : (L ^ 9)⁻¹ / 4 * L ^ 9 ≤ a * L * L ^ 9 := by
      rw [he, hi]
      nlinarith only [hL, Real.one_le_pi_div_two]
    exact (mul_le_mul_iff_left₀ (pow_pos hLp 9)).mp hmul
  exact ⟨hap, hasmall, h2, hsmall, heps⟩

theorem lemma46_disk_subset_local_strip {D : ℕ} {c s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hc : c.re = 1 / 2)
    (hci : |c.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hs : ‖s - c‖ < 2 * lemma44PaperAlpha D) : Lemma46InLocalStrip D s := by
  have hp := lemma46_alpha_parameters hD
  have hr : |s.re - 1 / 2| ≤ ‖s - c‖ := by
    simpa only [sub_re, hc] using abs_re_le_norm (s - c)
  have hi := abs_im_le_norm (s - c)
  have ht := abs_add_le (s.im - c.im) (c.im - (lemma23PaperCenter D).im)
  rw [sub_add_sub_cancel] at ht
  refine ⟨hr.trans_lt (hs.trans hp.2.2.1), ?_⟩
  simp only [sub_im] at hi
  linarith [hp.2.1]

theorem lemma46_inner_disk_regions {D : ℕ} {c s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hc : c.re = 1 / 2)
    (hci : |c.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2)
    (hs : ‖s - c‖ < lemma44PaperAlpha D) :
    Lemma44InOmega3 D s ∧ Lemma23InOmega1 D s := by
  have hp := lemma46_alpha_parameters hD
  have hs2 : ‖s - c‖ < 2 * lemma44PaperAlpha D := by linarith
  have hstrip := lemma46_disk_subset_local_strip hD hc hci hs2
  have hr := abs_lt.mp ((abs_re_le_norm (s - c)).trans_lt hs)
  simp only [sub_re, hc] at hr
  have hparams := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hparams.2]) (by linarith only [hparams.1])
  refine ⟨⟨by linarith, by linarith, hstrip.2⟩, ?_⟩
  exact lemma23_omega2_disk_subset_omega1 hparams.1 hparams.2
    (lemma46_local_strip_regions hD hstrip).1 (mem_ball_self hR)

end ZhangLS.Spec
