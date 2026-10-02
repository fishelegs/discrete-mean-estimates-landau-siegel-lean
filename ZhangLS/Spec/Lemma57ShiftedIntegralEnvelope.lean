import ZhangLS.Spec.Lemma57ShiftedGammaGrowth

/-!
# The quantitative envelope of the shifted Mellin integral

The contour shift is unconditional, but its mere exponential strip bound is
not enough for Zhang's small-error estimate: the Gaussian has width
`(log D)^15`.  Here we extract the exact Gaussian damping on the shifted
line.  Subsequent quantitative work must estimate the *undamped* factor in
this weighted integral, rather than treating exponential growth as small.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory
open scoped Real

/-- The nonnegative weighted norm that remains after removing the exact
`D⁻²` Gaussian factor from the shifted line. -/
noncomputable def lemma57LeftGaussianEnvelope {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ℝ :=
  ∫ t : ℝ,
    ‖lemma57UndampedMellinFactor χ
      (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
      Real.exp (-(t ^ 2) / (4 * Real.log (D : ℝ) ^ 30))

theorem lemma57LeftGaussianEnvelope_nonneg {D : ℕ}
    (χ : RealPrimitiveCharacter D) :
    0 ≤ lemma57LeftGaussianEnvelope χ := by
  unfold lemma57LeftGaussianEnvelope
  exact integral_nonneg fun _ => mul_nonneg (norm_nonneg _) (Real.exp_pos _).le

/-- The exact norm identity on the shifted line, with the whole arithmetic
factor separated from Gaussian damping. -/
theorem lemma57LeftMellinIntegrand_norm
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (t : ℝ) :
    ‖lemma57MellinIntegrand χ
      (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I) * I‖ =
      Real.exp (-2 * Real.log (D : ℝ) +
        1 / (16 * Real.log (D : ℝ) ^ 30)) *
        (‖lemma57UndampedMellinFactor χ
          (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
          Real.exp (-(t ^ 2) / (4 * Real.log (D : ℝ) ^ 30))) := by
  rw [norm_mul, norm_I, mul_one,
    lemma57MellinIntegrand_eq_undamped_mul_gaussian, norm_mul,
    lemma57GaussianMellinFactor_norm_vertical hD]
  have hL : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast hD)
  have hexp :
      4 * Real.log (D : ℝ) * (-(1 : ℝ) / 2) +
          ((-(1 : ℝ) / 2) ^ 2 - t ^ 2) /
            (4 * Real.log (D : ℝ) ^ 30) =
        (-2 * Real.log (D : ℝ) +
            1 / (16 * Real.log (D : ℝ) ^ 30)) +
          (-(t ^ 2) / (4 * Real.log (D : ℝ) ^ 30)) := by
    have hden : Real.log (D : ℝ) ^ 30 ≠ 0 := by positivity
    field_simp
    ring
  rw [hexp, Real.exp_add]
  ring

/-- Unconditional quantitative envelope for the actual shifted integral.
The factor outside the weighted integral is exactly of order `D⁻²`; the
remaining integral still needs a stronger vertical-growth estimate. -/
theorem lemma57LeftVerticalIntegral_norm_le_envelope
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    ‖lemma57VerticalIntegral χ (-(1 : ℝ) / 2)‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (Real.exp (-2 * Real.log (D : ℝ) +
          1 / (16 * Real.log (D : ℝ) ^ 30)) *
          lemma57LeftGaussianEnvelope χ) := by
  unfold lemma57VerticalIntegral
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖∫ t : ℝ, lemma57MellinIntegrand χ
      (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I) * I‖ ≤
      ∫ t : ℝ, ‖lemma57MellinIntegrand χ
        (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I) * I‖ :=
      norm_integral_le_integral_norm _
    _ = Real.exp (-2 * Real.log (D : ℝ) +
          1 / (16 * Real.log (D : ℝ) ^ 30)) *
          lemma57LeftGaussianEnvelope χ := by
      rw [lemma57LeftGaussianEnvelope, ← integral_const_mul]
      congr 1
      funext t
      exact lemma57LeftMellinIntegrand_norm χ hD t

/-- A pointwise, genuinely quantitative sufficient condition on the
undamped factor.  Unlike the exponential strip estimate used to justify the
contour shift, the coefficient here must itself be controlled in `D`. -/
def Lemma57LeftSubGaussianGrowth {D : ℕ}
    (χ : RealPrimitiveCharacter D) (C : ℝ) : Prop :=
  ∀ t : ℝ,
    ‖lemma57UndampedMellinFactor χ
      (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      C * Real.exp (t ^ 2 / (8 * Real.log (D : ℝ) ^ 30))

/-- A sub-Gaussian pointwise estimate integrates to one explicit Gaussian
moment; no unproved integration estimate is hidden in the hypothesis. -/
theorem lemma57LeftGaussianEnvelope_le_of_subGaussian
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {C : ℝ} (hgrowth : Lemma57LeftSubGaussianGrowth χ C) :
    lemma57LeftGaussianEnvelope χ ≤
      C * Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30) := by
  let b : ℝ := 1 / (8 * Real.log (D : ℝ) ^ 30)
  have hL : 0 < Real.log (D : ℝ) :=
    Real.log_pos (by exact_mod_cast hD)
  have hb : 0 < b := by dsimp [b]; positivity
  have hmain :
      lemma57LeftGaussianEnvelope χ ≤
        ∫ t : ℝ, C * Real.exp (-b * t ^ 2) := by
    unfold lemma57LeftGaussianEnvelope
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t =>
        mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      ((integrable_exp_neg_mul_sq hb).const_mul C)
    apply Filter.Eventually.of_forall
    intro t
    have hpoint := hgrowth t
    have hgauss : 0 ≤ Real.exp (-(t ^ 2) /
        (4 * Real.log (D : ℝ) ^ 30)) := (Real.exp_pos _).le
    have hmul := mul_le_mul_of_nonneg_right hpoint hgauss
    calc
      ‖lemma57UndampedMellinFactor χ
        (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
          Real.exp (-(t ^ 2) /
            (4 * Real.log (D : ℝ) ^ 30)) ≤
        C * Real.exp (t ^ 2 / (8 * Real.log (D : ℝ) ^ 30)) *
          Real.exp (-(t ^ 2) /
            (4 * Real.log (D : ℝ) ^ 30)) := hmul
      _ = C * Real.exp (-b * t ^ 2) := by
        rw [mul_assoc, ← Real.exp_add]
        congr 1
        dsimp [b]
        have hden : Real.log (D : ℝ) ^ 30 ≠ 0 := by positivity
        field_simp
        ring_nf
  calc
    lemma57LeftGaussianEnvelope χ ≤
        ∫ t : ℝ, C * Real.exp (-b * t ^ 2) := hmain
    _ = C * Real.sqrt (Real.pi / b) := by
      rw [integral_const_mul, integral_gaussian]
    _ = C * Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30) := by
      congr 1
      dsimp [b]
      have hden : Real.log (D : ℝ) ^ 30 ≠ 0 := by positivity
      field_simp

/-- The corresponding explicit bound for the shifted contour integral. -/
theorem lemma57LeftVerticalIntegral_norm_le_of_subGaussian
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {C : ℝ} (hgrowth : Lemma57LeftSubGaussianGrowth χ C) :
    ‖lemma57VerticalIntegral χ (-(1 : ℝ) / 2)‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (Real.exp (-2 * Real.log (D : ℝ) +
          1 / (16 * Real.log (D : ℝ) ^ 30)) *
          (C * Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30))) := by
  exact (lemma57LeftVerticalIntegral_norm_le_envelope χ hD).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (lemma57LeftGaussianEnvelope_le_of_subGaussian χ hD hgrowth)
        (Real.exp_pos _).le)
      (norm_nonneg _))

end ZhangLS.Spec
