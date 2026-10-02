import ZhangLS.Spec.Lemma44ReflectedLongSum
import ZhangLS.Spec.Lemma44GaussianLongSum
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The truncated middle-contour estimate in Lemma 4.4

The pointwise cancellation is integrated against the actual Gaussian
Mellin kernel. The pole denominator has logarithmic, rather than inverse
`α`, cost. The existing effective modulus threshold absorbs this cost
into one power of `L`, giving the paper's `L^-179` error scale.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set
open scoped Interval

set_option maxHeartbeats 1000000

theorem lemma44_integral_inverse_abs {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    (∫ v : ℝ in Ioc (-T) T, (a + |v|)⁻¹) = 2 * Real.log ((a + T) / a) := by
  have hc : Continuous (fun v : ℝ => (a + |v|)⁻¹) :=
    (continuous_const.add continuous_abs).inv₀ (fun v => by
      change a + |v| ≠ 0
      have h := abs_nonneg v
      linarith)
  have hpos : (∫ v : ℝ in (0 : ℝ)..T, (a + |v|)⁻¹) = Real.log ((a + T) / a) := by
    have he : (∫ v : ℝ in (0 : ℝ)..T, (a + |v|)⁻¹) =
        ∫ v : ℝ in (0 : ℝ)..T, (a + v)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro v hv
      rw [uIcc_of_le hT] at hv
      change (a + |v|)⁻¹ = (a + v)⁻¹
      rw [abs_of_nonneg hv.1]
    rw [he, intervalIntegral.integral_comp_add_left, add_zero]
    exact integral_inv_of_pos ha (by linarith)
  have hneg : (∫ v : ℝ in (-T)..(0 : ℝ), (a + |v|)⁻¹) =
      ∫ v : ℝ in (0 : ℝ)..T, (a + |v|)⁻¹ := by
    have h := intervalIntegral.integral_comp_neg (a := 0) (b := T)
      (fun v : ℝ => (a + |v|)⁻¹)
    simpa only [neg_zero, abs_neg] using h.symm
  rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T),
    ← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-T) 0) (hc.intervalIntegrable 0 T), hneg, hpos]
  ring

/-- Integrating `1/|w|` on the vertical line costs only a logarithm. -/
theorem lemma44_vertical_denominator_integral_le {a T : ℝ} (ha : 0 < a) (hT : 0 ≤ T) :
    (∫ v : ℝ in Ioc (-T) T, ‖-(a : ℂ) + (v : ℂ) * Complex.I‖⁻¹) ≤
      4 * Real.log ((a + T) / a) := by
  have hw (v : ℝ) : -(a : ℂ) + (v : ℂ) * Complex.I ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    linarith
  have hd : Continuous (fun v : ℝ => ‖-(a : ℂ) + (v : ℂ) * Complex.I‖⁻¹) := by
    have hc : Continuous (fun v : ℝ => ‖-(a : ℂ) + (v : ℂ) * Complex.I‖) := by fun_prop
    exact hc.inv₀ (fun v => norm_ne_zero_iff.mpr (hw v))
  have hc : Continuous (fun v : ℝ => 2 * (a + |v|)⁻¹) := by
    apply continuous_const.mul
    exact (continuous_const.add continuous_abs).inv₀ (fun v => by
      change a + |v| ≠ 0
      have h := abs_nonneg v
      linarith)
  calc
    _ ≤ ∫ v : ℝ in Ioc (-T) T, 2 * (a + |v|)⁻¹ := by
      apply integral_mono_ae
        (hd.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
      exact Filter.Eventually.of_forall (fun v => by
        have hp := norm_pos_iff.mpr (hw v)
        have hr := Complex.abs_re_le_norm (-(a : ℂ) + (v : ℂ) * Complex.I)
        have hi := Complex.abs_im_le_norm (-(a : ℂ) + (v : ℂ) * Complex.I)
        simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re, Complex.mul_re,
          Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero,
          abs_neg, abs_of_pos ha] at hr
        simp at hi
        have hden : a + |v| ≤ 2 * ‖-(a : ℂ) + (v : ℂ) * Complex.I‖ := by linarith
        calc
          _ = 2 / (2 * ‖-(a : ℂ) + (v : ℂ) * Complex.I‖) := by field_simp
          _ ≤ 2 / (a + |v|) := div_le_div_of_nonneg_left (by norm_num)
            (by linarith [abs_nonneg v]) hden
          _ = _ := by rw [div_eq_mul_inv])
    _ = 4 * Real.log ((a + T) / a) := by
      rw [integral_const_mul, lemma44_integral_inverse_abs ha hT]
      ring

theorem lemma44_middle_denominator_budget {D : ℕ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) :
    (∫ v : ℝ in Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20),
      ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖⁻¹) ≤ lemma23PaperL D := by
  let L := lemma23PaperL D
  let a := lemma44PaperAlpha D
  have hp := lemma44_parameters_at_explicit_threshold hD
  have hL3 : 3 ≤ L := hp.1
  have hLpos : 0 < L := by linarith
  have ha : 0 < a := (lemma44_alpha_pos_le_one hp.1).1
  have haeq : a = Real.pi / L ^ 9 := by simp [a, lemma44PaperAlpha, lemma23PaperP, L]
  have hr : (a + L ^ 20) / a ≤ L ^ 30 := by
    have hpi : 1 ≤ Real.pi := by linarith [Real.one_le_pi_div_two]
    have hpow : 1 ≤ L ^ 29 := one_le_pow₀ (by linarith : 1 ≤ L)
    have hratio : (a + L ^ 20) / a = 1 + L ^ 29 / Real.pi := by
      rw [haeq]
      field_simp
    rw [hratio]
    calc
      1 + L ^ 29 / Real.pi ≤ 2 * L ^ 29 := by
        have h := div_le_self (pow_nonneg hLpos.le 29) hpi
        linarith
      _ ≤ L * L ^ 29 := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = L ^ 30 := by ring
  have hlog : Real.log ((a + L ^ 20) / a) ≤ 30 * Real.log L := by
    have h := Real.log_le_log (by positivity : 0 < (a + L ^ 20) / a) hr
    simpa only [Real.log_pow, Nat.cast_ofNat] using h
  have hden := lemma44_vertical_denominator_integral_le ha (pow_nonneg hLpos.le 20)
  apply hden.trans
  have hlognon : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hsmall : 50000 * Real.log L + 4000 ≤ L / 2 := hp.2
  nlinarith only [hlog, hlognon, hsmall]

theorem lemma44_Omega_norm_vertical (D : ℕ) (σ v : ℝ) :
    ‖lemma57OmegaOne D ((σ : ℂ) + (v : ℂ) * Complex.I)‖ =
      Real.exp ((σ ^ 2 - v ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
  rw [lemma57OmegaOne, Complex.norm_exp]
  congr 1
  have hcast : 4 * (Real.log (D : ℝ) : ℂ) ^ 30 =
      ((4 * lemma23PaperL D ^ 30 : ℝ) : ℂ) := by
    dsimp [lemma23PaperL]
    push_cast
    ring
  have hsq : (((σ : ℂ) + (v : ℂ) * Complex.I) ^ 2).re = σ ^ 2 - v ^ 2 := by
    rw [pow_two, Complex.mul_re]
    simp
    ring
  have hinv : (((4 * lemma23PaperL D ^ 30 : ℝ) : ℂ))⁻¹ =
      (((4 * lemma23PaperL D ^ 30)⁻¹ : ℝ) : ℂ) := by norm_cast
  rw [hcast, div_eq_mul_inv, hinv, Complex.mul_re, hsq]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  ring

noncomputable def lemma44MiddleContourIntegrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (v : ℝ) : ℂ :=
  let w := -(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I
  lemma44ActualZtilde χ ψ (s + w) * lemma44LongDirichletSum χ ψ⁻¹ (1 - s - w) *
    Complex.exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ)) *
      lemma57OmegaOne D w / w

theorem lemma44_middle_integrand_norm_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44MiddleContourIntegrand χ ψ s v‖ ≤
      (5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ)) *
        ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖⁻¹ := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  have hprod := lemma44_middle_product_bound χ ψ hD hψ hs hv
  have hlogB : 0 ≤ Real.log (lemma44PaperGaussianScale D) := by
    have hP : 0 < lemma23PaperP D := Real.exp_pos _
    rw [lemma44PaperGaussianScale, Real.log_rpow hP, lemma23PaperP, Real.log_exp]
    positivity
  have hpower : ‖Complex.exp ((-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I) *
      (Real.log (lemma44PaperGaussianScale D) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.1.le) hlogB
  have homega : ‖lemma57OmegaOne D (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      Real.exp 1 := by
    have h := lemma44_Omega_norm_vertical D (-lemma44PaperAlpha D) v
    simp only [Complex.ofReal_neg, neg_sq] at h
    rw [h]
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * lemma23PaperL D ^ 30)).mpr
    have hp : 1 ≤ lemma23PaperL D ^ 30 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
    nlinarith only [ha.1, ha.2, hp, sq_nonneg v]
  dsimp only [lemma44MiddleContourIntegrand]
  rw [norm_div, norm_mul, norm_mul]
  have hm := mul_le_mul (mul_le_mul hprod hpower (norm_nonneg _) (by positivity)) homega
    (norm_nonneg _) (by positivity)
  have hc : (5 * Real.exp (2 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) * 1) *
      Real.exp 1 = 5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) := by
    rw [show (5 * Real.exp (2 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) * 1) *
      Real.exp 1 = 5 * (Real.exp (2 + 4 * Real.pi) * Real.exp 1) *
        lemma23PaperL D ^ (-180 : ℤ) by ring, ← Real.exp_add]
    rw [show 2 + 4 * Real.pi + 1 = 3 + 4 * Real.pi by ring]
  rw [hc] at hm
  have hd := div_le_div_of_nonneg_right hm
    (norm_nonneg (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I))
  simpa only [div_eq_mul_inv] using hd

theorem lemma44_middle_integrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    IntegrableOn (lemma44MiddleContourIntegrand χ ψ s)
      (Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  let w : ℝ → ℂ := fun v => -(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I
  have hwc : Continuous w := by dsimp [w]; fun_prop
  have hwne (v : ℝ) : w v ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [w] at hr
    exact ha.1.ne' hr
  have hrest : Continuous (fun v : ℝ => lemma44LongDirichletSum χ ψ⁻¹ (1 - s - w v) *
      Complex.exp (w v * (Real.log (lemma44PaperGaussianScale D) : ℂ)) *
        lemma57OmegaOne D (w v) / w v) := by
    have hnum : Continuous (fun v : ℝ => lemma44LongDirichletSum χ ψ⁻¹ (1 - s - w v) *
        Complex.exp (w v * (Real.log (lemma44PaperGaussianScale D) : ℂ)) *
          lemma57OmegaOne D (w v)) := by
      unfold lemma44LongDirichletSum lemma57OmegaOne
      fun_prop
    exact hnum.div₀ hwc hwne
  have hc : ContinuousOn (lemma44MiddleContourIntegrand χ ψ s)
      (Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)) := by
    intro v hv
    have hvabs : |v| ≤ lemma23PaperL D ^ 20 := abs_le.mpr hv
    have hz := lemma44_truncated_shift_in_extended_gamma_region hL hs
      (w := w v) (by
        simp only [w, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul,
          sub_zero, add_zero, abs_neg]
        rw [abs_of_pos ha.1]; linarith [ha.2]) (by simpa [w] using hvabs)
    have him := (lemma44_extended_gamma_region_height hL hz).2.2.1
    have hzd : ContinuousAt (lemma44ActualZtilde χ ψ) (s + w v) :=
      (lemma44ActualZtilde_differentiableAt χ ψ him.ne').continuousAt
    have hargC : ContinuousAt (fun u : ℝ => s + w u) v :=
      continuousAt_const.add hwc.continuousAt
    have hzc : ContinuousAt (fun u : ℝ => lemma44ActualZtilde χ ψ (s + w u)) v :=
      hzd.comp (f := fun u : ℝ => s + w u) hargC
    have h := hzc.mul hrest.continuousAt
    have heq : lemma44MiddleContourIntegrand χ ψ s =
        (fun u : ℝ => lemma44ActualZtilde χ ψ (s + w u)) *
          (fun u : ℝ => lemma44LongDirichletSum χ ψ⁻¹ (1 - s - w u) *
            Complex.exp (w u * (Real.log (lemma44PaperGaussianScale D) : ℂ)) *
              lemma57OmegaOne D (w u) / w u) := by
      funext u
      dsimp [lemma44MiddleContourIntegrand, w]
      ring
    rw [heq]
    exact h.continuousWithinAt
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

/-- The actual truncated middle piece has the paper's `O(L^-179)` scale.
This theorem does not identify it with the full shifted contour or its infinite tails. -/
theorem lemma44_truncated_middle_contour_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ v : ℝ in Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20),
        lemma44MiddleContourIntegrand χ ψ s v * Complex.I)‖ ≤
      5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-179 : ℤ) := by
  let C := 5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ)
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdc : Continuous (fun v : ℝ =>
      ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖⁻¹) := by
    have hc : Continuous (fun v : ℝ =>
        ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖) := by fun_prop
    apply hc.inv₀
    intro v
    apply norm_ne_zero_iff.mpr
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact ha.1.ne' hr
  have hm : IntegrableOn (fun v : ℝ => C *
      ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖⁻¹)
      (Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)) :=
    (hdc.const_mul C).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hb : ∀ᵐ v : ℝ ∂volume.restrict
      (Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)),
      ‖lemma44MiddleContourIntegrand χ ψ s v * Complex.I‖ ≤
        C * ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [norm_mul, Complex.norm_I, mul_one]
    exact lemma44_middle_integrand_norm_bound χ ψ hD hψ hs (abs_le.mpr ⟨hv.1.le, hv.2⟩)
  have hi := norm_integral_le_of_norm_le hm hb
  rw [integral_const_mul] at hi
  have hbudget := mul_le_mul_of_nonneg_left (lemma44_middle_denominator_budget hD) hC
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one]
    norm_num [Complex.norm_of_nonneg Real.pi_pos.le]
    have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.one_le_pi_div_two]
    have h := inv_le_one_of_one_le₀ hpi
    rw [abs_of_pos Real.pi_pos]
    convert h using 1
    ring
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∫ v : ℝ in Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20),
        lemma44MiddleContourIntegrand χ ψ s v * Complex.I‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ ≤ C * lemma23PaperL D := by simpa only [one_mul] using hi.trans hbudget
    _ = _ := by
      have hpow : lemma23PaperL D ^ (-180 : ℤ) * lemma23PaperL D =
          lemma23PaperL D ^ (-179 : ℤ) := by
        calc
          _ = lemma23PaperL D ^ (-180 : ℤ) * lemma23PaperL D ^ (1 : ℤ) := by rw [zpow_one]
          _ = _ := by
            rw [← zpow_add₀ (by linarith : lemma23PaperL D ≠ 0)]
            norm_num
      dsimp [C]
      rw [mul_assoc, hpow]

end ZhangLS.Spec
