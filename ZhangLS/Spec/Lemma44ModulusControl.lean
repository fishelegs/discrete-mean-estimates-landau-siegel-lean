import ZhangLS.Spec.Lemma44SectionFourGamma
import ZhangLS.Spec.Lemma44LongSum
import ZhangLS.Spec.Lemma23SectionFourLogDerivative
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Modulus control for the actual factor in Lemma 4.4

The conductor contribution is kept separate from the logarithmic Gamma
error. At the existing explicit Section 4 threshold the normalized
logarithmic derivative has negative real part. Horizontal integration of
an analytic logarithm then controls the modulus, including the thin strip
to the left of the critical line.
-/

namespace ZhangLS.Spec

open Complex Set

set_option maxHeartbeats 1000000

/-- The extra vertical margin allows the truncated contour shifts in Lemma 4.4. -/
def Lemma44InExtendedGammaRegion (D : ℕ) (s : ℂ) : Prop :=
  |s.re - 1 / 2| ≤ 100 ∧
    |s.im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3

theorem lemma44_extended_gamma_region_height {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma44InExtendedGammaRegion D s) :
    24 ≤ |s.im| ∧ |s.re| + 2 ≤ |s.im| / 4 ∧ 0 < s.im ∧
      Real.log (3 * |s.im|) ≤ 519 * Real.log (lemma23PaperL D) + 30 := by
  let L := lemma23PaperL D
  have hL3 : 3 ≤ L := hL
  have hL1 : 1 ≤ L := by linarith
  have hpow : L ^ 405 ≤ L ^ 519 := pow_le_pow_right₀ hL1 (by norm_num)
  have hpow3 : 3 ≤ L ^ 519 := hL3.trans (le_self_pow₀ hL1 (by norm_num))
  have hpow729 : 729 ≤ L ^ 519 := by
    have h₆ : (3 : ℝ) ^ 6 ≤ L ^ 6 := pow_le_pow_left₀ (by norm_num) hL3 6
    norm_num at h₆
    exact h₆.trans (pow_le_pow_right₀ hL1 (by norm_num))
  have him : |s.im - 2 * Real.pi * L ^ 519| ≤ 2 * L ^ 405 + 3 := hs.2
  have himlo : L ^ 519 ≤ s.im := by
    have h := (abs_le.mp him).1
    nlinarith [Real.one_le_pi_div_two]
  have himhi : s.im ≤ 11 * L ^ 519 := by
    have h := (abs_le.mp him).2
    nlinarith [Real.pi_le_four]
  have hspos : 0 < s.im := by linarith
  have hre : |s.re| ≤ 101 := by
    have h := abs_add_le (s.re - 1 / 2) (1 / 2 : ℝ)
    norm_num at h
    linarith [hs.1]
  rw [abs_of_pos hspos]
  refine ⟨by linarith, by linarith, hspos, ?_⟩
  calc
    Real.log (3 * s.im) ≤ Real.log (33 * L ^ 519) :=
      Real.log_le_log (by linarith : 0 < 3 * s.im) (by linarith)
    _ = Real.log 33 + 519 * Real.log L := by
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
      norm_num
    _ ≤ 519 * Real.log L + 30 := by
      have hlog : Real.log 33 ≤ 30 := by
        have hlog3 : Real.log 3 ≤ 2 :=
          by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
             norm_num at h; exact h
        have hlog11 : Real.log 11 ≤ 10 :=
          by have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 11)
             norm_num at h; exact h
        rw [show (33 : ℝ) = 3 * 11 by norm_num,
          Real.log_mul (by norm_num) (by norm_num)]
        linarith
      linarith

/-- The archimedean error is logarithmic in `L`, rather than linear in `L`. -/
theorem lemma44_actual_archimedean_error {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InExtendedGammaRegion D s) :
    ‖logDeriv (lemma44ActualZtilde χ ψ) s +
      ((lemma23PaperL D + 2 * Real.log (p : ℝ) : ℝ) : ℂ)‖ ≤
        50000 * Real.log (lemma23PaperL D) + 4000 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hpne : p ≠ 1 := hψ.1.ne_one
  have hDpne : D * p ≠ 1 := by
    intro h
    exact hpne (Nat.dvd_one.mp (h ▸ Nat.dvd_mul_left p D))
  have htwist := lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1
    (lemma44_family_coprime χ ψ hL hψ)
  have hh := lemma44_extended_gamma_region_height hL hs
  have hf := lemma44_productZ_logDeriv_bound ψ (lemma44CharacterTwist χ ψ)
    hψ.2.1 htwist hpne hDpne hh.1 hh.2.1
  change ‖logDeriv (lemma44ActualZtilde χ ψ) s + Complex.log (p : ℂ) +
    Complex.log ((D * p : ℕ) : ℂ)‖ ≤ _ at hf
  have hlogDp : Complex.log ((D * p : ℕ) : ℂ) =
      ((lemma23PaperL D + Real.log (p : ℝ) : ℝ) : ℂ) := by
    rw [← Complex.natCast_log, Nat.cast_mul, Real.log_mul
      (by exact_mod_cast χ.modulus_ne_zero) (by exact_mod_cast NeZero.ne p)]
    rfl
  have hlogp : Complex.log (p : ℂ) = ((Real.log (p : ℝ) : ℝ) : ℂ) :=
    (Complex.natCast_log (n := p)).symm
  have heq : logDeriv (lemma44ActualZtilde χ ψ) s +
      ((lemma23PaperL D + 2 * Real.log (p : ℝ) : ℝ) : ℂ) =
      logDeriv (lemma44ActualZtilde χ ψ) s + Complex.log (p : ℂ) +
        Complex.log ((D * p : ℕ) : ℂ) := by
    rw [hlogDp, hlogp]; push_cast; ring
  rw [heq]
  apply hf.trans
  have hπ : ‖Complex.log (Real.pi : ℂ)‖ ≤ 4 := by
    rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_nonneg (by linarith [Real.one_le_pi_div_two]))]
    exact (Real.log_le_self Real.pi_pos.le).trans Real.pi_le_four
  nlinarith [hh.2.2.2, Real.pi_le_four,
    Real.log_nonneg (by linarith : 1 ≤ lemma23PaperL D)]

/-- The already used computable modulus threshold makes the Gamma error at most `L/2`. -/
theorem lemma44_parameters_at_explicit_threshold {D : ℕ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) :
    3 ≤ lemma23PaperL D ∧
      50000 * Real.log (lemma23PaperL D) + 4000 ≤ lemma23PaperL D / 2 := by
  have hparams := lemma23_sectionFour_parameters_at_explicit_threshold hD
  have hpow_real : (3 : ℝ) ^ (3 ^ 200 : ℕ) ≤ (D : ℝ) := by exact_mod_cast hD
  have hlogthree : (1 : ℝ) ≤ Real.log 3 :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).mpr
      (le_of_lt Real.exp_one_lt_three)
  have hlogmono := Real.log_le_log (by positivity : 0 < (3 : ℝ) ^ (3 ^ 200 : ℕ)) hpow_real
  rw [Real.log_pow] at hlogmono
  have hLlarge : (300000 : ℝ) ^ 2 ≤ lemma23PaperL D := by
    have hn : (300000 : ℝ) ^ 2 ≤ (3 : ℝ) ^ 200 := by norm_num
    calc
      (300000 : ℝ) ^ 2 ≤ (3 : ℝ) ^ 200 := hn
      _ ≤ (3 : ℝ) ^ 200 * Real.log 3 := by
        simpa using mul_le_mul_of_nonneg_left hlogthree (by positivity : 0 ≤ (3 : ℝ) ^ 200)
      _ = ((3 ^ 200 : ℕ) : ℝ) * Real.log 3 := by rw [Nat.cast_pow]; norm_num
      _ ≤ lemma23PaperL D := hlogmono
  have hsqrt : (300000 : ℝ) ≤ Real.sqrt (lemma23PaperL D) := by
    have h := Real.sqrt_le_sqrt hLlarge
    rw [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 300000)] at h
    exact h
  have hlog := Real.log_le_rpow_div
    (by linarith : 0 ≤ lemma23PaperL D) (by norm_num : (0 : ℝ) < 1 / 2)
  rw [← Real.sqrt_eq_rpow] at hlog
  have hsq := Real.sq_sqrt (by linarith : 0 ≤ lemma23PaperL D)
  refine ⟨hparams.1, ?_⟩
  nlinarith only [hlog, hsqrt, hsq]

theorem lemma44ActualZtilde_differentiableAt {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (him : s.im ≠ 0) :
    DifferentiableAt ℂ (lemma44ActualZtilde χ ψ) s := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  exact (lemma23DirichletZ_differentiableAt_of_im_ne_zero ψ him).mul
    (lemma23DirichletZ_differentiableAt_of_im_ne_zero (lemma44CharacterTwist χ ψ) him)

theorem lemma44ActualZtilde_ne_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (him : 0 < s.im) : lemma44ActualZtilde χ ψ s ≠ 0 := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hpne : p ≠ 1 := hψ.1.ne_one
  have hDpne : D * p ≠ 1 := by
    intro h
    exact hpne (Nat.dvd_one.mp (h ▸ Nat.dvd_mul_left p D))
  exact mul_ne_zero (lemma23DirichletZ_ne_zero_of_im_pos ψ hψ.2.1 hpne him)
    (lemma23DirichletZ_ne_zero_of_im_pos (lemma44CharacterTwist χ ψ)
      (lemma44CharacterTwist_isPrimitive χ ψ hψ.2.1 (lemma44_family_coprime χ ψ hL hψ))
      hDpne him)

/-- An analytic logarithm supplies the real logarithmic modulus along any horizontal
line in the upper half-plane. The lift is derived from nonvanishing. -/
theorem lemma44_exists_horizontal_log_modulus {f : ℂ → ℂ}
    (hf : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, DifferentiableAt ℂ f z)
    (hne : ∀ z ∈ UpperHalfPlane.upperHalfPlaneSet, f z ≠ 0)
    {t : ℝ} (ht : 0 < t) :
    ∃ H : ℝ → ℝ,
      (∀ x : ℝ, Real.exp (H x) = ‖f ((x : ℂ) + Complex.I * (t : ℂ))‖) ∧
      (∀ x : ℝ, HasDerivAt H (logDeriv f ((x : ℂ) + Complex.I * (t : ℂ))).re x) := by
  obtain ⟨ℓ, _, hlift, hderiv⟩ := lemma23_exists_analytic_log_branch
    lemma23_upperHalfPlane_isSimplyConnected UpperHalfPlane.isOpen_upperHalfPlaneSet
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt) hne hf
  let H : ℝ → ℝ := fun x => (ℓ ((x : ℂ) + Complex.I * (t : ℂ))).re
  have hmem (x : ℝ) : (x : ℂ) + Complex.I * (t : ℂ) ∈
      UpperHalfPlane.upperHalfPlaneSet := by
    change 0 < ((x : ℂ) + Complex.I * (t : ℂ)).im
    simpa using ht
  refine ⟨H, ?_, ?_⟩
  · intro x
    have h := congrArg norm (hlift _ (hmem x))
    simpa only [Complex.norm_exp] using h
  · intro x
    have hd := (hderiv _ (hmem x)).comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const (Complex.I * (t : ℂ)))
    simpa only [Function.comp_def, mul_one, ← logDeriv_apply] using hd.real_of_complex

/-- At the effective threshold the conductor dominates the Gamma error. -/
theorem lemma44_logDeriv_real_bounds {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InExtendedGammaRegion D s) :
    -2 * Real.log (lemma23PaperP D) - 3 * lemma23PaperL D ≤
        (logDeriv (lemma44ActualZtilde χ ψ) s).re ∧
      (logDeriv (lemma44ActualZtilde χ ψ) s).re ≤ -2 * Real.log (lemma23PaperP D) := by
  have hparams := lemma44_parameters_at_explicit_threshold hD
  have hf := (lemma44_actual_archimedean_error χ ψ hparams.1 hψ hs).trans hparams.2
  have hre := Complex.abs_re_le_norm (logDeriv (lemma44ActualZtilde χ ψ) s +
    ((lemma23PaperL D + 2 * Real.log (p : ℝ) : ℝ) : ℂ))
  have hb := abs_le.mp (hre.trans hf)
  simp only [Complex.add_re, Complex.ofReal_re] at hb
  have hp := lemma44_family_log_bound hparams.1 ψ hψ
  constructor <;> linarith

/-- The actual factor to the right of the critical line has the required conductor decay. -/
theorem lemma44ActualZtilde_norm_le_right {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InExtendedGammaRegion D s) (hre : 1 / 2 ≤ s.re) :
    ‖lemma44ActualZtilde χ ψ s‖ ≤
      Real.exp ((1 - 2 * s.re) * Real.log (lemma23PaperP D)) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ht := (lemma44_extended_gamma_region_height hL hs).2.2.1
  obtain ⟨H, hHnorm, hHd⟩ := lemma44_exists_horizontal_log_modulus
    (fun z hz => lemma44ActualZtilde_differentiableAt χ ψ (ne_of_gt hz))
    (fun z hz => lemma44ActualZtilde_ne_zero χ ψ hL hψ hz) ht
  have hzero : H (1 / 2) = 0 := by
    have hn := lemma44ActualZtilde_norm_eq_one χ ψ hL hψ
      (s := ((1 / 2 : ℝ) : ℂ) + Complex.I * (s.im : ℂ)) (by simp)
    have he : Real.exp (H (1 / 2)) = Real.exp 0 := by
      rw [hHnorm, hn, Real.exp_zero]
    exact Real.exp_injective he
  have hregion (x : ℝ) (hx : x ∈ Icc (1 / 2) s.re) :
      Lemma44InExtendedGammaRegion D ((x : ℂ) + Complex.I * (s.im : ℂ)) := by
    simp only [Lemma44InExtendedGammaRegion, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero, add_zero, zero_add, Complex.add_im, Complex.mul_im, one_mul]
    refine ⟨?_, hs.2⟩
    rw [abs_of_nonneg (by linarith [hx.1])]
    have hr := (abs_le.mp hs.1).2
    linarith [hx.2]
  have hdiff : Differentiable ℝ H := fun x => (hHd x).differentiableAt
  have hbound : ∀ x ∈ interior (Icc (1 / 2) s.re),
      deriv H x ≤ -2 * Real.log (lemma23PaperP D) := by
    intro x hx
    rw [(hHd x).deriv]
    exact (lemma44_logDeriv_real_bounds χ ψ hD hψ (hregion x (interior_subset hx))).2
  have h := (convex_Icc (1 / 2 : ℝ) s.re).image_sub_le_mul_sub_of_deriv_le
    hdiff.continuous.continuousOn hdiff.differentiableOn hbound
    (1 / 2) ⟨le_rfl, hre⟩ s.re ⟨hre, le_rfl⟩ hre
  rw [hzero, sub_zero] at h
  have heq : (s.re : ℂ) + Complex.I * (s.im : ℂ) = s := by
    apply Complex.ext <;> simp
  have hn := hHnorm s.re
  rw [heq] at hn
  rw [← hn]
  apply Real.exp_le_exp.mpr
  nlinarith only [h]

/-- On the left, the extra loss is only `exp(3 L (1/2-σ))`. -/
theorem lemma44ActualZtilde_norm_le_left {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InExtendedGammaRegion D s) (hre : s.re ≤ 1 / 2) :
    ‖lemma44ActualZtilde χ ψ s‖ ≤
      Real.exp ((1 - 2 * s.re) * Real.log (lemma23PaperP D) +
        3 * lemma23PaperL D * (1 / 2 - s.re)) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ht := (lemma44_extended_gamma_region_height hL hs).2.2.1
  obtain ⟨H, hHnorm, hHd⟩ := lemma44_exists_horizontal_log_modulus
    (fun z hz => lemma44ActualZtilde_differentiableAt χ ψ (ne_of_gt hz))
    (fun z hz => lemma44ActualZtilde_ne_zero χ ψ hL hψ hz) ht
  have hzero : H (1 / 2) = 0 := by
    have hn := lemma44ActualZtilde_norm_eq_one χ ψ hL hψ
      (s := ((1 / 2 : ℝ) : ℂ) + Complex.I * (s.im : ℂ)) (by simp)
    have he : Real.exp (H (1 / 2)) = Real.exp 0 := by
      rw [hHnorm, hn, Real.exp_zero]
    exact Real.exp_injective he
  have hregion (x : ℝ) (hx : x ∈ Icc s.re (1 / 2)) :
      Lemma44InExtendedGammaRegion D ((x : ℂ) + Complex.I * (s.im : ℂ)) := by
    simp only [Lemma44InExtendedGammaRegion, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, mul_zero,
      zero_mul, sub_zero, add_zero, zero_add, Complex.add_im, Complex.mul_im, one_mul]
    refine ⟨?_, hs.2⟩
    rw [abs_of_nonpos (by linarith [hx.2])]
    have hr := (abs_le.mp hs.1).1
    linarith [hx.1]
  have hdiff : Differentiable ℝ H := fun x => (hHd x).differentiableAt
  have hbound : ∀ x ∈ interior (Icc s.re (1 / 2)),
      -2 * Real.log (lemma23PaperP D) - 3 * lemma23PaperL D ≤ deriv H x := by
    intro x hx
    rw [(hHd x).deriv]
    exact (lemma44_logDeriv_real_bounds χ ψ hD hψ (hregion x (interior_subset hx))).1
  have h := (convex_Icc s.re (1 / 2 : ℝ)).mul_sub_le_image_sub_of_le_deriv
    hdiff.continuous.continuousOn hdiff.differentiableOn hbound
    s.re ⟨le_rfl, hre⟩ (1 / 2) ⟨hre, le_rfl⟩ hre
  rw [hzero, zero_sub] at h
  have heq : (s.re : ℂ) + Complex.I * (s.im : ℂ) = s := by
    apply Complex.ext <;> simp
  have hn := hHnorm s.re
  rw [heq] at hn
  rw [← hn]
  apply Real.exp_le_exp.mpr
  nlinarith only [h]

theorem lemma44_omega3_subset_extended_gamma_region {D : ℕ} {s : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma44InOmega3 D s) :
    Lemma44InExtendedGammaRegion D s := by
  have ha := lemma44_alpha_pos_le_one hL
  refine ⟨?_, ?_⟩
  · apply abs_le.mpr
    constructor <;> linarith [hs.1, hs.2.1]
  · have hp : 0 ≤ lemma23PaperL D ^ 405 := by positivity
    linarith [hs.2.2]

/-- The horizontal loss in the thin left part of `Ω₃` is an absolute constant. -/
theorem lemma44_alpha_horizontal_loss {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    3 * lemma23PaperL D * lemma44PaperAlpha D ≤ 1 := by
  let L := lemma23PaperL D
  have hL3 : 3 ≤ L := hL
  have hLpos : 0 < L := by linarith
  have hp : 12 ≤ L ^ 8 := by
    have h₃ : (3 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL3 3
    have h₈ : L ^ 3 ≤ L ^ 8 := pow_le_pow_right₀ (by linarith : 1 ≤ L) (by norm_num)
    norm_num at h₃
    linarith only [h₃, h₈]
  change 3 * L * (Real.pi / Real.log (Real.exp (L ^ 9))) ≤ 1
  rw [Real.log_exp, ← mul_div_assoc]
  apply (div_le_iff₀ (pow_pos hLpos 9)).mpr
  simp only [one_mul]
  calc
    3 * L * Real.pi ≤ 12 * L := by nlinarith only [Real.pi_le_four, hLpos]
    _ ≤ L ^ 8 * L := mul_le_mul_of_nonneg_right hp hLpos.le
    _ = L ^ 9 := by ring

/-- Uniform modulus control needed by the approximate functional equation.
This is a proved coarse replacement for the modulus use of Stirling (4.5). -/
theorem lemma44ActualZtilde_norm_on_omega3 {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44ActualZtilde χ ψ s‖ ≤
      Real.exp 1 * Real.exp ((1 - 2 * s.re) * Real.log (lemma23PaperP D)) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hregion := lemma44_omega3_subset_extended_gamma_region hL hs
  by_cases hre : 1 / 2 ≤ s.re
  · have hb := lemma44ActualZtilde_norm_le_right χ ψ hD hψ hregion hre
    have he : 1 ≤ Real.exp (1 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num)
    apply hb.trans
    have hm := mul_le_mul_of_nonneg_right he (Real.exp_nonneg
      ((1 - 2 * s.re) * Real.log (lemma23PaperP D)))
    simpa only [one_mul] using hm
  · have hb := lemma44ActualZtilde_norm_le_left χ ψ hD hψ hregion (le_of_not_ge hre)
    have hsmall : 3 * lemma23PaperL D * (1 / 2 - s.re) ≤ 1 := by
      have hm := mul_le_mul_of_nonneg_left (show 1 / 2 - s.re ≤ lemma44PaperAlpha D by
        linarith [hs.1]) (by linarith : 0 ≤ 3 * lemma23PaperL D)
      exact hm.trans (lemma44_alpha_horizontal_loss hL)
    apply hb.trans
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by linarith only [hsmall])

/-- All Gaussian truncation shifts stay inside the proved Gamma strip. -/
theorem lemma44_truncated_shift_in_extended_gamma_region {D : ℕ} {s w : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma44InOmega3 D s)
    (hwre : |w.re| ≤ 15) (hwim : |w.im| ≤ lemma23PaperL D ^ 20) :
    Lemma44InExtendedGammaRegion D (s + w) := by
  have ha := lemma44_alpha_pos_le_one hL
  have hre : |s.re - 1 / 2| ≤ 2 := by
    apply abs_le.mpr
    constructor <;> linarith [hs.1, hs.2.1]
  have hp : lemma23PaperL D ^ 20 ≤ lemma23PaperL D ^ 405 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  constructor
  · change |s.re + w.re - 1 / 2| ≤ 100
    have ht := abs_add_le (s.re - 1 / 2) w.re
    rw [sub_add_eq_add_sub] at ht
    linarith
  · change |s.im + w.im - (lemma23PaperCenter D).im| ≤ _
    have ht := abs_add_le (s.im - (lemma23PaperCenter D).im) w.im
    rw [sub_add_eq_add_sub] at ht
    linarith [hs.2.2]

end ZhangLS.Spec
