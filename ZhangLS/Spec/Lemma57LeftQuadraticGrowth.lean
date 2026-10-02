import ZhangLS.Spec.Lemma57CriticalStripGrowth
import ZhangLS.Spec.Lemma57QuadraticConductorThreshold

/-!
# Unconditional polynomial growth and the Lemma 5.7 Gaussian error

The zeta and character Abel--Mellin bounds give a quadratic pointwise bound
on the shifted line.  The existing Gaussian-moment and logarithmic threshold
lemmas then make the analytic error small for all sufficiently large moduli.
-/

namespace ZhangLS.Spec

open Complex Filter
open scoped Real Topology

/-- On the actual shifted line, the undamped factor has a quadratic bound
whose coefficient is an explicit constant times the conductor. -/
theorem lemma57LeftQuadraticGrowth_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57LeftQuadraticGrowth χ (288 * (D : ℝ)) := by
  intro t
  have hline : (1 : ℝ) / 2 ≤
      ‖((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ := by
    calc
      (1 : ℝ) / 2 =
          |((( -(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I).re| := by norm_num
      _ ≤ ‖((-(1 : ℝ) / 2 : ℝ) : ℂ) + (t : ℂ) * I‖ := Complex.abs_re_le_norm _
  simpa using lemma57UndampedMellinFactor_norm_le_quadratic χ hD
    (σ := -(1 : ℝ) / 2) (t := t) (by norm_num) (by norm_num) hline

/-- The proved quadratic estimate and Gaussian moment yield the paper's
analytic-error budget at the closed, computable modulus threshold. -/
theorem lemma57_gaussian_error_at_explicit_threshold
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D)
    (hA : NormalizedAssumptionA χ) :
    Lemma57GaussianAnalyticErrorBound χ := by
  have hD : 1 < D := lemma57_one_lt_of_explicit_threshold hDN
  have hlogD : 2 ≤ Real.log (D : ℝ) := by
    have hlog := lemma57_log_ge_ten_million hDN
    linarith
  have hmajorD :
      288 * lemma57QuadraticConductorMajorant D ≤ (1 : ℝ) / 32 :=
    lemma57_scaled_majorant_le_one_thirtysecond_of_explicit_threshold hDN
  clear hDN
  have hleft := lemma57LeftVerticalIntegral_norm_le_of_quadratic
    χ hD (by positivity) (lemma57LeftQuadraticGrowth_proved χ hD)
  have hExpr := lemma57QuadraticConductorExpression_le_majorant hD hlogD
  have hleftScaled :
      ‖lemma57VerticalIntegral χ (-(1 : ℝ) / 2)‖ ≤
        288 * lemma57QuadraticConductorMajorant D := by
    calc
      ‖lemma57VerticalIntegral χ (-(1 : ℝ) / 2)‖ ≤
          ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
            (Real.exp (-2 * Real.log (D : ℝ) +
              1 / (16 * Real.log (D : ℝ) ^ 30)) *
              (288 * (D : ℝ) * (1 + 8 * Real.log (D : ℝ) ^ 30) *
                Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30))) := hleft
      _ = 288 * (‖(2 * (Real.pi : ℂ) * I)⁻¹‖ *
            (Real.exp (-2 * Real.log (D : ℝ) +
              1 / (16 * Real.log (D : ℝ) ^ 30)) *
              ((D : ℝ) * (1 + 8 * Real.log (D : ℝ) ^ 30) *
                Real.sqrt (8 * Real.pi * Real.log (D : ℝ) ^ 30)))) := by ring
      _ ≤ 288 * lemma57QuadraticConductorMajorant D :=
        mul_le_mul_of_nonneg_left hExpr (by norm_num)
  have hscale := lemma57Scale_ge_one hD
  have hbudget :
      288 * lemma57QuadraticConductorMajorant D ≤
        (1 : ℝ) / 32 * lemma57Scale D := by nlinarith
  apply lemma57GaussianAnalyticErrorBound_of_shifted_norm χ hD hlogD hA
  exact hleftScaled.trans hbudget

/-- Existential compatibility wrapper; the witness is the explicit threshold
`lemma57ExplicitModulusThreshold`, not a choice extracted from convergence. -/
theorem exists_modulus_threshold_for_proved_gaussian_error :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      Lemma57GaussianAnalyticErrorBound χ := by
  refine ⟨lemma57ExplicitModulusThreshold, ?_⟩
  intro D χ hDN _hD hA
  exact lemma57_gaussian_error_at_explicit_threshold χ hDN hA

/-- Lemma 5.7's derivative lower bound with its concrete natural-number
threshold visible in the theorem statement. -/
theorem lemma57_one_sixteenth_at_explicit_threshold
    {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D)
    (hA : NormalizedAssumptionA χ) :
    (1 : ℝ) / 16 * lemma57Scale D ≤ realLDerivAtOne χ := by
  have hD : 1 < D := lemma57_one_lt_of_explicit_threshold hDN
  exact lemma57_gaussian_mellin_contour_transfer χ hD
    (lemma57MellinIdentity_proved χ hD)
    (lemma57ContourShiftIdentity_proved χ hD)
    (lemma57_gaussian_error_at_explicit_threshold χ hDN hA)

/-- Consequently Lemma 5.7's derivative lower bound holds under (A) for
all sufficiently large conductors, with the explicit constant `1/16`. -/
theorem lemma57_one_sixteenth_for_large_modulus :
    ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
      (1 : ℝ) / 16 * lemma57Scale D ≤ realLDerivAtOne χ := by
  refine ⟨lemma57ExplicitModulusThreshold, ?_⟩
  intro D χ hDN _hD hA
  exact lemma57_one_sixteenth_at_explicit_threshold χ hDN hA

/-- Zhang's paper-level Lemma 5.7, with its standing large-modulus convention
made explicit in `Lemma57AtConstant`. -/
theorem lemma57_target_proved : Lemma57Target := by
  refine ⟨(1 : ℝ) / 16, ?_⟩
  constructor
  · norm_num
  · refine ⟨lemma57ExplicitModulusThreshold, ?_⟩
    intro D χ hD₀ _hD hA
    exact lemma57_one_sixteenth_at_explicit_threshold χ hD₀ hA

end ZhangLS.Spec
