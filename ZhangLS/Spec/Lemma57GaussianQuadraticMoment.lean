import ZhangLS.Spec.Lemma57ResidueBudget

/-!
# A quadratic-growth criterion for the shifted Gaussian integral

Step 46 used a sub-Gaussian pointwise input. A polynomial bound is closer to
the analytic estimate required for the actual zeta and Dirichlet L-functions.
This module proves the Gaussian moment inequality for a quadratic polynomial
and transfers any such pointwise bound to the shifted integral. The pointwise
zeta/L bound itself is not asserted here.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory
open scoped Real

/-- A quadratic polynomial costs at most one inverse Gaussian-width factor
when half of the damping is reserved for integration. -/
theorem one_add_sq_mul_gaussian_le
    {b : ℝ} (hb : 0 < b) (t : ℝ) :
    (1 + t ^ 2) * Real.exp (-(2 * b) * t ^ 2) ≤
      (1 + b⁻¹) * Real.exp (-b * t ^ 2) := by
  have hx : 0 ≤ b * t ^ 2 := mul_nonneg hb.le (sq_nonneg t)
  have hexp := Real.add_one_le_exp (b * t ^ 2)
  have hExpOne : 1 ≤ Real.exp (b * t ^ 2) := by linarith
  have hbt : b * t ^ 2 ≤ Real.exp (b * t ^ 2) := by linarith
  have ht2 : t ^ 2 ≤ b⁻¹ * Real.exp (b * t ^ 2) := by
    have hdiv : t ^ 2 ≤ Real.exp (b * t ^ 2) / b :=
      (le_div_iff₀ hb).2 (by nlinarith [hbt])
    simpa [div_eq_mul_inv, mul_comm] using hdiv
  have hpoly : 1 + t ^ 2 ≤
      (1 + b⁻¹) * Real.exp (b * t ^ 2) := by
    nlinarith [hExpOne, ht2]
  calc
    (1 + t ^ 2) * Real.exp (-(2 * b) * t ^ 2) ≤
        ((1 + b⁻¹) * Real.exp (b * t ^ 2)) *
          Real.exp (-(2 * b) * t ^ 2) :=
      mul_le_mul_of_nonneg_right hpoly (Real.exp_pos _).le
    _ = (1 + b⁻¹) * Real.exp (-b * t ^ 2) := by
      rw [mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf

/-- The exact Gaussian integral converts the pointwise quadratic estimate
into an explicit integrated moment bound. -/
theorem integral_one_add_sq_mul_gaussian_le {b : ℝ} (hb : 0 < b) :
    (∫ t : ℝ, (1 + t ^ 2) * Real.exp (-(2 * b) * t ^ 2)) ≤
      (1 + b⁻¹) * Real.sqrt (Real.pi / b) := by
  calc
    (∫ t : ℝ, (1 + t ^ 2) * Real.exp (-(2 * b) * t ^ 2)) ≤
        ∫ t : ℝ, (1 + b⁻¹) * Real.exp (-b * t ^ 2) := by
      apply integral_mono_of_nonneg
        (Filter.Eventually.of_forall fun t =>
          mul_nonneg (by positivity) (Real.exp_pos _).le)
        ((integrable_exp_neg_mul_sq hb).const_mul (1 + b⁻¹))
      exact Filter.Eventually.of_forall (one_add_sq_mul_gaussian_le hb)
    _ = (1 + b⁻¹) * Real.sqrt (Real.pi / b) := by
      rw [integral_const_mul, integral_gaussian]

/-- A pointwise quadratic vertical-growth input for the undamped factor. -/
def Lemma57LeftQuadraticGrowth {D : ℕ}
    (χ : RealPrimitiveCharacter D) (C : ℝ) : Prop :=
  ∀ t : ℝ,
    ‖lemma57UndampedMellinFactor χ
      (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      C * (1 + t ^ 2)

/-- A quadratic pointwise bound gives a completely explicit Gaussian
envelope. Its coefficient `C` remains an open analytic input. -/
theorem lemma57LeftGaussianEnvelope_le_of_quadratic
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {C : ℝ} (hC : 0 ≤ C) (hgrowth : Lemma57LeftQuadraticGrowth χ C) :
    lemma57LeftGaussianEnvelope χ ≤
      C * (1 + 8 * Real.log (D : ℝ) ^ 30) *
        Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30) := by
  let L : ℝ := Real.log (D : ℝ)
  let b : ℝ := 1 / (8 * L ^ 30)
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast hD)
  have hb : 0 < b := by dsimp [b]; positivity
  have hLpow : L ^ 30 ≠ 0 := by positivity
  have hmain : lemma57LeftGaussianEnvelope χ ≤
      ∫ t : ℝ, (C * (1 + b⁻¹)) * Real.exp (-b * t ^ 2) := by
    unfold lemma57LeftGaussianEnvelope
    apply integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun t =>
        mul_nonneg (norm_nonneg _) (Real.exp_pos _).le)
      ((integrable_exp_neg_mul_sq hb).const_mul (C * (1 + b⁻¹)))
    apply Filter.Eventually.of_forall
    intro t
    have hpoint := hgrowth t
    have hexp : -(t ^ 2) / (4 * Real.log (D : ℝ) ^ 30) =
        -(2 * b) * t ^ 2 := by
      dsimp [b, L]
      field_simp
      ring_nf
    change
      ‖lemma57UndampedMellinFactor χ
        (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
          Real.exp (-(t ^ 2) / (4 * Real.log (D : ℝ) ^ 30)) ≤
        (C * (1 + b⁻¹)) * Real.exp (-b * t ^ 2)
    rw [hexp]
    calc
      ‖lemma57UndampedMellinFactor χ
        (((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
          Real.exp (-(2 * b) * t ^ 2) ≤
        (C * (1 + t ^ 2)) * Real.exp (-(2 * b) * t ^ 2) :=
        mul_le_mul_of_nonneg_right hpoint (Real.exp_pos _).le
      _ = C * ((1 + t ^ 2) * Real.exp (-(2 * b) * t ^ 2)) := by ring
      _ ≤ C * ((1 + b⁻¹) * Real.exp (-b * t ^ 2)) :=
        mul_le_mul_of_nonneg_left (one_add_sq_mul_gaussian_le hb t) hC
      _ = (C * (1 + b⁻¹)) * Real.exp (-b * t ^ 2) := by ring
  calc
    lemma57LeftGaussianEnvelope χ ≤
        ∫ t : ℝ, (C * (1 + b⁻¹)) * Real.exp (-b * t ^ 2) := hmain
    _ = (C * (1 + b⁻¹)) * Real.sqrt (Real.pi / b) := by
      rw [integral_const_mul, integral_gaussian]
    _ = C * (1 + 8 * Real.log (D : ℝ) ^ 30) *
          Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30) := by
      have hinv : b⁻¹ = 8 * L ^ 30 := by
        dsimp [b]
        field_simp
      have hdiv : Real.pi / b = 8 * Real.pi * L ^ 30 := by
        dsimp [b]
        field_simp
      rw [hinv, hdiv]

/-- The corresponding explicit norm bound for the actual shifted integral. -/
theorem lemma57LeftVerticalIntegral_norm_le_of_quadratic
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {C : ℝ} (hC : 0 ≤ C) (hgrowth : Lemma57LeftQuadraticGrowth χ C) :
    ‖lemma57VerticalIntegral χ (-(1 : ℝ) / 2)‖ ≤
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
        (Real.exp (-2 * Real.log (D : ℝ) +
          1 / (16 * Real.log (D : ℝ) ^ 30)) *
          (C * (1 + 8 * Real.log (D : ℝ) ^ 30) *
            Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30))) := by
  exact (lemma57LeftVerticalIntegral_norm_le_envelope χ hD).trans
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left
        (lemma57LeftGaussianEnvelope_le_of_quadratic χ hD hC hgrowth)
        (Real.exp_pos _).le)
      (norm_nonneg _))

/-- The paper's analytic-error target follows from a quadratic bound whose
explicit coefficient fits the remaining `1/32` budget. No such coefficient
bound is assumed to hold for zeta/L in this module. -/
theorem lemma57GaussianAnalyticErrorBound_of_quadratic
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hlog : 2 ≤ Real.log (D : ℝ))
    (hA : NormalizedAssumptionA χ)
    {C : ℝ} (hC : 0 ≤ C) (hgrowth : Lemma57LeftQuadraticGrowth χ C)
    (hCbudget :
      ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
          (Real.exp (-2 * Real.log (D : ℝ) +
            1 / (16 * Real.log (D : ℝ) ^ 30)) *
            (C * (1 + 8 * Real.log (D : ℝ) ^ 30) *
              Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30))) ≤
        (1 : ℝ) / 32 * lemma57Scale D) :
    Lemma57GaussianAnalyticErrorBound χ := by
  apply lemma57GaussianAnalyticErrorBound_of_shifted_norm χ hD hlog hA
  exact (lemma57LeftVerticalIntegral_norm_le_of_quadratic χ hD hC hgrowth).trans
    hCbudget

end ZhangLS.Spec
