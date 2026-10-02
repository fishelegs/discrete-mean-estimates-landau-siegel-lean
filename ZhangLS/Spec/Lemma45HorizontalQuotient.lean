import ZhangLS.Spec.Lemma45Normalization

/-! # Horizontal control of the actual short-polynomial quotient -/

namespace ZhangLS.Spec

open Complex ComplexConjugate Set Filter
open scoped Topology

set_option maxHeartbeats 1000000

/-- A local normalized principal logarithm differentiates the logarithmic
modulus without choosing a global branch. -/
theorem lemma45_hasDerivAt_horizontal_log_norm {f : ℂ → ℂ} {a t : ℝ}
    (hf : DifferentiableAt ℂ f ((a : ℂ) + I * (t : ℂ)))
    (hne : f ((a : ℂ) + I * (t : ℂ)) ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log ‖f ((x : ℂ) + I * (t : ℂ))‖)
      (logDeriv f ((a : ℂ) + I * (t : ℂ))).re a := by
  let z := (a : ℂ) + I * (t : ℂ)
  let g : ℂ → ℂ := fun w => f (w + I * (t : ℂ))
  let q : ℂ → ℂ := fun w => g w / g a
  have hg : HasDerivAt g (deriv f z) (a : ℂ) := by
    simpa only [mul_one] using hf.hasDerivAt.comp (a : ℂ)
      ((hasDerivAt_id (a : ℂ)).add_const (I * (t : ℂ)))
  have hga : g a ≠ 0 := hne
  have hqa : q a = 1 := by simp [q, hga]
  have hqd : HasDerivAt q (deriv f z / f z) (a : ℂ) := hg.div_const (g a)
  have hd := (hqd.clog (by rw [hqa]; exact Complex.one_mem_slitPlane)).real_of_complex
  have hderiv : HasDerivAt
      (fun x : ℝ => (Complex.log (q x)).re + Real.log ‖g a‖)
      (logDeriv f z).re a := by
    simpa only [hqa, div_one, logDeriv] using hd.add_const (Real.log ‖g a‖)
  apply hderiv.congr_of_eventuallyEq
  have hcont : ContinuousAt (fun x : ℝ => g x) a :=
    hg.continuousAt.comp Complex.continuous_ofReal.continuousAt
  filter_upwards [hcont.eventually_ne hga] with x hx
  change Real.log ‖g x‖ = (Complex.log (q x)).re + Real.log ‖g a‖
  rw [Complex.log_re]
  change Real.log ‖g x‖ = Real.log ‖g x / g a‖ + Real.log ‖g a‖
  rw [norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hga)]
  ring

/-- Comparing both sides of the critical line uses the same good character;
inverse-character membership in `Ψ₁` is not needed. -/
theorem lemma45_horizontal_F_quotient_bound {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hre : 1 / 2 ≤ s.re)
    (hnear : s.re < 1 / 2 + (lemma23PaperL D)⁻¹)
    (him : |s.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 2) :
    ‖lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s) /
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ ≤
        Real.exp (281600 * lemma23PaperL D * (s.re - 1 / 2)) := by
  let L := lemma23PaperL D
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p))
  let H : ℝ → ℝ := fun x => Real.log ‖F ((x : ℂ) + I * (s.im : ℂ))‖
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hL : 3 ≤ L := hp.1
  have hLp : 0 < L := by linarith
  have hR : 0 < lemma23LogDerivativeRadius D := by
    unfold lemma23LogDerivativeRadius
    exact div_pos (by linarith only [hp.2])
      (mul_pos (by norm_num) (by linarith only [hp.1]))
  have hregion (x : ℝ) (hx : x ∈ Icc (1 - s.re) s.re) :
      Lemma23InOmega2 D ((x : ℂ) + I * (s.im : ℂ)) := by
    simp only [Lemma23InOmega2, add_re, ofReal_re, mul_re, I_re, I_im,
      ofReal_im, mul_zero, zero_mul, sub_zero, add_zero, add_im, mul_im, one_mul,
      zero_add]
    refine ⟨by linarith [hx.1], ?_, by linarith⟩
    change x < 1 + L⁻¹
    linarith [hx.2]
  have hregion1 (x : ℝ) (hx : x ∈ Icc (1 - s.re) s.re) :
      Lemma23InOmega1 D ((x : ℂ) + I * (s.im : ℂ)) :=
    lemma23_omega2_disk_subset_omega1 hp.1 hp.2 (hregion x hx)
      (Metric.mem_ball_self hR)
  have hd (x : ℝ) (hx : x ∈ Icc (1 - s.re) s.re) :
      HasDerivAt H
        (logDeriv F ((x : ℂ) + I * (s.im : ℂ))).re x :=
    lemma45_hasDerivAt_horizontal_log_norm
      (lemma44_short_polynomial_differentiable χ ψ _)
      (lemma23_omega1_F_ne_zero χ ψ _ hp.1 hψ.2 (hregion1 x hx))
  have hcont : ContinuousOn H (Icc (1 - s.re) s.re) :=
    fun x hx => (hd x hx).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ H (interior (Icc (1 - s.re) s.re)) :=
    fun x hx => (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
  have hbound : ∀ x ∈ interior (Icc (1 - s.re) s.re),
      -140800 * L ≤ deriv H x := by
    intro x hx
    rw [(hd x (interior_subset hx)).deriv]
    have hb := lemma23_lemma43_at_explicit_threshold χ ψ _ hD hψ
      (hregion x (interior_subset hx))
    have hr := (abs_le.mp ((Complex.abs_re_le_norm _).trans hb)).1
    linarith
  have ho : 1 - s.re ≤ s.re := by linarith
  have hm := (convex_Icc (1 - s.re) s.re).mul_sub_le_image_sub_of_le_deriv
    hcont hdiff hbound (1 - s.re) ⟨le_rfl, ho⟩ s.re ⟨ho, le_rfl⟩ ho
  have hsEq : (s.re : ℂ) + I * (s.im : ℂ) = s := by
    apply Complex.ext <;> simp
  have hrEq : ((1 - s.re : ℝ) : ℂ) + I * (s.im : ℂ) = conj (1 - s) := by
    apply Complex.ext <;> simp
  have hn := lemma23_omega1_F_ne_zero χ ψ _ hp.1 hψ.2
    (hregion1 s.re ⟨ho, le_rfl⟩)
  have hnr := lemma23_omega1_F_ne_zero χ ψ _ hp.1 hψ.2
    (hregion1 (1 - s.re) ⟨le_rfl, ho⟩)
  rw [hsEq] at hn
  rw [hrEq] at hnr
  rw [lemma45_short_sum_inv_eq_conj, norm_div, norm_conj]
  have hlog : Real.log (‖F (conj (1 - s))‖ / ‖F s‖) ≤
      281600 * L * (s.re - 1 / 2) := by
    rw [Real.log_div (norm_ne_zero_iff.mpr hnr) (norm_ne_zero_iff.mpr hn)]
    dsimp only [H] at hm
    rw [hsEq, hrEq] at hm
    linarith
  rw [← Real.exp_log (div_pos (norm_pos_iff.mpr hnr) (norm_pos_iff.mpr hn))]
  exact Real.exp_le_exp.mpr hlog

end ZhangLS.Spec
