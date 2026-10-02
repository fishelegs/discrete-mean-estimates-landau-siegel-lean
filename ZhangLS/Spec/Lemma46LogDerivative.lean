import ZhangLS.Spec.Lemma45ZeroFree
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # The genuine local logarithmic derivative in Lemma 4.6 -/

namespace ZhangLS.Spec

open Complex ComplexConjugate Set

set_option maxHeartbeats 1000000

/-- A symmetric strip about the critical line, with the margin needed for
the local disks of Lemmas 4.6 and 4.7. -/
def Lemma46InLocalStrip (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| < (lemma23PaperL D)⁻¹ ∧
    |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 3

theorem lemma46_local_strip_regions {D : ℕ} {s : ℂ}
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hs : Lemma46InLocalStrip D s) :
    Lemma23InOmega2 D s ∧ Lemma23InOmega2 D (conj (1 - s)) ∧
      Lemma44InGammaRegion D s ∧ 0 < s.im := by
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hi : (lemma23PaperL D)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hr := abs_lt.mp hs.1
  have hs2 : Lemma23InOmega2 D s :=
    ⟨by linarith, by linarith, by linarith [hs.2]⟩
  have hs2r : Lemma23InOmega2 D (conj (1 - s)) := by
    simp only [Lemma23InOmega2, conj_re, sub_re, one_re,
      conj_im, sub_im, one_im, zero_sub, neg_neg]
    exact ⟨by linarith, by linarith, by linarith [hs.2]⟩
  have hgamma : Lemma44InGammaRegion D s :=
    ⟨by linarith [hs.1], hs.2.le⟩
  have hext : Lemma44InExtendedGammaRegion D s :=
    ⟨by linarith [hs.1], by linarith [hs.2, pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 405]⟩
  exact ⟨hs2, hs2r, hgamma,
    (lemma44_extended_gamma_region_height hp.1 hext).2.2.1⟩

/-- Conjugation transports the full complex logarithmic derivative, not
just its real part. -/
theorem lemma46_inverse_F_logDeriv {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    logDeriv (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) s =
      conj (logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)))
        (conj s)) := by
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))
  have heq : lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) =
      conj ∘ F ∘ conj := by
    funext z
    exact lemma45_short_sum_inv_eq_conj χ ψ z
  rw [heq, logDeriv, Pi.div_apply, deriv_conj_conj]
  simp only [Function.comp_apply, logDeriv, Pi.div_apply, map_div₀]
  rfl

theorem lemma46_actual_B_differentiable_ne_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma46InLocalStrip D s) :
    DifferentiableAt ℂ (lemma45ActualB χ ψ) s ∧ lemma45ActualB χ ψ s ≠ 0 := by
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hr := lemma46_local_strip_regions hD hs
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2]) (by linarith only [hp.1])
  have hF := lemma23_omega1_F_ne_zero χ ψ s hp.1 hψ.2
    (lemma23_omega2_disk_subset_omega1 hp.1 hp.2 hr.1 (Metric.mem_ball_self hR))
  have hFr := lemma23_omega1_F_ne_zero χ ψ (conj (1 - s)) hp.1 hψ.2
    (lemma23_omega2_disk_subset_omega1 hp.1 hp.2 hr.2.1 (Metric.mem_ball_self hR))
  have hFi : lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s) ≠ 0 := by
    rw [lemma45_short_sum_inv_eq_conj]
    exact (map_ne_zero conj).2 hFr
  have hZ := lemma44ActualZtilde_ne_zero χ ψ hp.1 hψ.1 hr.2.2.2
  constructor
  · exact ((lemma44ActualZtilde_differentiableAt χ ψ hr.2.2.2.ne').mul
      ((lemma44_short_polynomial_differentiable χ ψ⁻¹ (1 - s)).comp s
        (by fun_prop))).div (lemma44_short_polynomial_differentiable χ ψ s) hF
  · exact div_ne_zero (mul_ne_zero hZ hFi) hF

/-- Paper equation (4.11), with an absolute explicit constant. Every
nonvanishing and analytic input follows from genuine good-set membership. -/
theorem lemma46_equation411 {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma46InLocalStrip D s) :
    ‖logDeriv (lemma45ActualB χ ψ) s +
      ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ)‖ ≤
        341600 * lemma23PaperL D := by
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hr := lemma46_local_strip_regions hD hs
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2]) (by linarith only [hp.1])
  have hF := lemma23_omega1_F_ne_zero χ ψ s hp.1 hψ.2
    (lemma23_omega2_disk_subset_omega1 hp.1 hp.2 hr.1 (Metric.mem_ball_self hR))
  have hFr := lemma23_omega1_F_ne_zero χ ψ (conj (1 - s)) hp.1 hψ.2
    (lemma23_omega2_disk_subset_omega1 hp.1 hp.2 hr.2.1 (Metric.mem_ball_self hR))
  have hFi : lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s) ≠ 0 := by
    rw [lemma45_short_sum_inv_eq_conj]
    exact (map_ne_zero conj).2 hFr
  have hZ := lemma44ActualZtilde_ne_zero χ ψ hp.1 hψ.1 hr.2.2.2
  have hid := lemma23_logDeriv_reflection_quotient
    (lemma44ActualZtilde_differentiableAt χ ψ hr.2.2.2.ne')
    (lemma44_short_polynomial_differentiable χ ψ⁻¹ (1 - s))
    (lemma44_short_polynomial_differentiable χ ψ s) hZ hFi hF
  change logDeriv (lemma45ActualB χ ψ) s = _ at hid
  rw [hid]
  have hb := lemma23_lemma43_at_explicit_threshold χ ψ s hD hψ hr.1
  have hbr := lemma23_lemma43_at_explicit_threshold χ ψ (conj (1 - s)) hD hψ hr.2.1
  have hbi : ‖logDeriv (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)))
      (1 - s)‖ ≤ 140800 * lemma23PaperL D := by
    rw [lemma46_inverse_F_logDeriv, norm_conj]
    exact hbr
  have hz := lemma44_equation46 χ ψ hp.1 hψ.1 hr.2.2.1
  have heq : logDeriv (lemma44ActualZtilde χ ψ) s -
      logDeriv (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) (1 - s) -
      logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) s +
      ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ) =
      (logDeriv (lemma44ActualZtilde χ ψ) s +
        ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ)) -
      logDeriv (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) (1 - s) -
      logDeriv (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))) s := by ring
  rw [heq]
  exact (norm_sub_le _ _).trans (by
    have ht := norm_sub_le
      (logDeriv (lemma44ActualZtilde χ ψ) s +
        ((2 * Real.log (lemma23PaperP D) : ℝ) : ℂ))
      (logDeriv (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) (1 - s))
    linarith)

end ZhangLS.Spec
