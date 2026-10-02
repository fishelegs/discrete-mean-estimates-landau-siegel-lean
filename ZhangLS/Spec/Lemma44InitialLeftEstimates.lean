import ZhangLS.Spec.Lemma44FiniteProductShift
import ZhangLS.Spec.Lemma44MiddleContour

/-!
# Local estimates on the initial left contour

At `Re(s+w)=-1/2`, the conductor factor and `B^w` combine to a loss of
only `exp(3L+9π/5)P^(1/5)`. A reflected tail saving `P^-1/2` will therefore
leave `P^-3/10`. All bounds are local on the already proved Gamma strip.
-/

namespace ZhangLS.Spec

open Complex

set_option maxHeartbeats 1000000

noncomputable def lemma44InitialLeftShift (s : ℂ) (v : ℝ) : ℂ :=
  ((-s.re - 1 / 2 : ℝ) : ℂ) + (v : ℂ) * I

@[simp] theorem lemma44_initial_left_shift_re (s : ℂ) (v : ℝ) :
    (lemma44InitialLeftShift s v).re = -s.re - 1 / 2 := by
  simp [lemma44InitialLeftShift]

@[simp] theorem lemma44_initial_left_shift_im (s : ℂ) (v : ℝ) :
    (lemma44InitialLeftShift s v).im = v := by
  simp [lemma44InitialLeftShift]

theorem lemma44_initial_left_shift_abs_re {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma44InOmega3 D s) (v : ℝ) :
    |(lemma44InitialLeftShift s v).re| ≤ 3 := by
  have ha := lemma44_alpha_pos_le_one hL
  have hre := lemma44_omega3_re_pos hL hs
  rw [lemma44_initial_left_shift_re]
  apply abs_le.mpr
  constructor <;> linarith only [hs.2.1, ha.2, hre]

theorem lemma44_initial_left_gamma_region {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma44InOmega3 D s)
    {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    Lemma44InExtendedGammaRegion D (s + lemma44InitialLeftShift s v) := by
  apply lemma44_truncated_shift_in_extended_gamma_region hL hs
  · exact (lemma44_initial_left_shift_abs_re hL hs v).trans (by norm_num)
  · simpa using hv

theorem lemma44_paper_gaussian_scale_log (D : ℕ) :
    Real.log (lemma44PaperGaussianScale D) = (9 / 5 : ℝ) * lemma23PaperL D ^ 9 := by
  rw [lemma44PaperGaussianScale, lemma23PaperP,
    Real.log_rpow (Real.exp_pos _), Real.log_exp]

theorem lemma44_initial_left_Z_scale_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44ActualZtilde χ ψ (s + lemma44InitialLeftShift s v)‖ *
      ‖exp (lemma44InitialLeftShift s v * (Real.log (lemma44PaperGaussianScale D) : ℂ))‖ ≤
        Real.exp (3 * lemma23PaperL D + (9 / 5 : ℝ) * Real.pi + lemma23PaperL D ^ 9 / 5) := by
  let L := lemma23PaperL D
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL0 : 0 < L := by linarith
  have hregion := lemma44_initial_left_gamma_region hL hs hv
  have hre : (s + lemma44InitialLeftShift s v).re = -1 / 2 := by simp; ring
  have hz := lemma44ActualZtilde_norm_le_left χ ψ hD hψ hregion
    (by rw [hre]; norm_num)
  rw [hre] at hz
  have hz' : ‖lemma44ActualZtilde χ ψ (s + lemma44InitialLeftShift s v)‖ ≤
      Real.exp (2 * L ^ 9 + 3 * L) := by
    convert hz using 1 <;> norm_num [lemma23PaperP, Real.log_exp, L]
  have hscale : ‖exp (lemma44InitialLeftShift s v *
      (Real.log (lemma44PaperGaussianScale D) : ℂ))‖ =
      Real.exp ((-s.re - 1 / 2) * ((9 / 5 : ℝ) * L ^ 9)) := by
    rw [norm_exp, mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero,
      lemma44_initial_left_shift_re, lemma44_paper_gaussian_scale_log]
    rfl
  have halpha : L ^ 9 * lemma44PaperAlpha D = Real.pi := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    dsimp [L]
    field_simp
  have hgap := mul_nonneg (pow_nonneg hL0.le 9)
    (show 0 ≤ s.re - (1 / 2 - lemma44PaperAlpha D) by linarith only [hs.1])
  rw [hscale]
  calc
    _ ≤ Real.exp (2 * L ^ 9 + 3 * L) *
        Real.exp ((-s.re - 1 / 2) * ((9 / 5 : ℝ) * L ^ 9)) :=
      mul_le_mul_of_nonneg_right hz' (Real.exp_pos _).le
    _ = Real.exp (2 * L ^ 9 + 3 * L + (-s.re - 1 / 2) * ((9 / 5 : ℝ) * L ^ 9)) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hgap, halpha])

theorem lemma44_initial_left_omega_bound {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma44InOmega3 D s) (v : ℝ) :
    ‖lemma57OmegaOne D (lemma44InitialLeftShift s v)‖ ≤ Real.exp 1 := by
  have habs := lemma44_initial_left_shift_abs_re hL hs v
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have h30 : 9 ≤ lemma23PaperL D ^ 30 := by
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 2
    have h230 := pow_le_pow_right₀ hL1 (show 2 ≤ 30 by norm_num)
    norm_num at h2
    exact h2.trans h230
  have hsquare : (-s.re - 1 / 2) ^ 2 ≤ 9 := by
    rw [lemma44_initial_left_shift_re] at habs
    have h := sq_le_sq₀ (abs_nonneg (-s.re - 1 / 2)) (by norm_num : (0 : ℝ) ≤ 3) |>.mpr habs
    norm_num only [sq_abs] at h
    exact h
  change ‖lemma57OmegaOne D (((-s.re - 1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ _
  rw [lemma44_Omega_norm_vertical]
  apply Real.exp_le_exp.mpr
  apply (div_le_one (by positivity : 0 < 4 * lemma23PaperL D ^ 30)).mpr
  nlinarith only [hsquare, h30, sq_nonneg v]

theorem lemma44_initial_left_denominator_bound {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma44InOmega3 D s) (v : ℝ) :
    ‖lemma44InitialLeftShift s v‖⁻¹ ≤ 2 := by
  have hre := lemma44_omega3_re_pos hL hs
  have hn := Complex.abs_re_le_norm (lemma44InitialLeftShift s v)
  rw [lemma44_initial_left_shift_re, abs_of_neg (by linarith : -s.re - 1 / 2 < 0)] at hn
  have hnorm : 0 < ‖lemma44InitialLeftShift s v‖ := by linarith only [hn, hre]
  apply (inv_le_comm₀ hnorm (by norm_num : (0 : ℝ) < 2)).mpr
  norm_num
  linarith only [hn, hre]

theorem lemma44_initial_left_exponential_budget {L : ℝ} (hL : 3 ≤ L) :
    L ^ 20 * Real.exp (3 * L - (3 / 10 : ℝ) * L ^ 9) ≤ L ^ (-180 : ℤ) := by
  have hL0 : 0 < L := by linarith
  have h8 : (3 : ℝ) ^ 8 ≤ L ^ 8 := pow_le_pow_left₀ (by norm_num) hL 8
  have h9 : 6561 * L ≤ L ^ 9 := by
    calc
      _ ≤ L ^ 8 * L := by nlinarith only [h8, hL0]
      _ = _ := by ring
  have hlog := Real.log_le_sub_one_of_pos hL0
  have h20 : L ^ 20 = Real.exp (20 * Real.log L) := by
    simpa [Real.exp_log hL0] using (Real.exp_nat_mul (Real.log L) 20).symm
  rw [h20, ← Real.exp_add]
  calc
    _ ≤ Real.exp (-180 * Real.log L) :=
      Real.exp_le_exp.mpr (by nlinarith only [h9, hlog, hL0])
    _ = L ^ (-180 : ℤ) := by
      rw [← Real.rpow_intCast, Real.rpow_def_of_pos hL0]
      congr 1
      norm_num
      ring

end ZhangLS.Spec
