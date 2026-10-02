import ZhangLS.Spec.Lemma57MellinIdentity
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# Passing finite contour shifts to the two infinite vertical lines

This module isolates the limit argument in the contour shift from
`re s = 1` to `re s = -1/2`.  The finite rectangle residue calculation and
the decay of its horizontal edges are deliberately explicit hypotheses:
neither analytic input is hidden by the convention that a non-integrable
Bochner integral has value zero.

Once the left vertical line is integrable, the finite rectangle identities
and horizontal decay imply the exact infinite contour-shift identity.  The
right vertical integrability needed for this passage is supplied
unconditionally by the full Mellin identity.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Filter
open scoped Real Topology

/-- The normalized vertical integral on `re s = σ`, truncated at heights
`-T` and `T`. -/
noncomputable def lemma57TruncatedVerticalIntegral {D : ℕ}
    (χ : RealPrimitiveCharacter D) (σ T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∫ t : ℝ in -T..T,
      lemma57MellinIntegrand χ ((σ : ℂ) + (t : ℂ) * I) * I

/-- The normalized top-minus-bottom horizontal contribution for the rectangle
with vertical sides `re s = -1/2` and `re s = 1`.  With positive boundary
orientation, the finite residue identity can be rearranged as
`right = residue + left + horizontalError`. -/
noncomputable def lemma57HorizontalIntegralError {D : ℕ}
    (χ : RealPrimitiveCharacter D) (T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ((∫ x : ℝ in (-(1 : ℝ) / 2)..1,
        lemma57MellinIntegrand χ ((x : ℂ) + (T : ℂ) * I)) -
      ∫ x : ℝ in (-(1 : ℝ) / 2)..1,
        lemma57MellinIntegrand χ ((x : ℂ) - (T : ℂ) * I))

/-- The exact normalized residue formula on every finite rectangle of positive
height.  This is the finite complex-analysis obligation in the contour shift. -/
def Lemma57FiniteRectangleShift {D : ℕ}
    (χ : RealPrimitiveCharacter D) : Prop :=
  ∀ T : ℝ, 0 < T →
    lemma57TruncatedVerticalIntegral χ 1 T =
      lemma57ResidueValue χ +
        lemma57TruncatedVerticalIntegral χ (-(1 : ℝ) / 2) T +
          lemma57HorizontalIntegralError χ T

/-- The top-minus-bottom horizontal contribution vanishes as the rectangle
height tends to infinity.  This is the decay obligation in the contour shift. -/
def Lemma57HorizontalDecay {D : ℕ}
    (χ : RealPrimitiveCharacter D) : Prop :=
  Tendsto (lemma57HorizontalIntegralError χ) atTop (nhds 0)

/-- Honest integrability on a vertical line makes its symmetric truncations
converge to the declared normalized improper integral. -/
theorem lemma57TruncatedVerticalIntegral_tendsto
    {D : ℕ} (χ : RealPrimitiveCharacter D) {σ : ℝ}
    (hint : Lemma57VerticalIntegrable χ σ) :
    Tendsto (lemma57TruncatedVerticalIntegral χ σ) atTop
      (nhds (lemma57VerticalIntegral χ σ)) := by
  unfold lemma57TruncatedVerticalIntegral lemma57VerticalIntegral
  apply Tendsto.const_mul
  exact intervalIntegral_tendsto_integral hint
    tendsto_neg_atTop_atBot tendsto_id

/-- The complete limit step for Zhang's contour shift.  It converts the two
finite analytic obligations and left-line integrability into the exact
infinite vertical-line identity. -/
theorem lemma57ContourShiftIdentity_of_finite_rectangles
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hleft : Lemma57VerticalIntegrable χ (-(1 : ℝ) / 2))
    (hfinite : Lemma57FiniteRectangleShift χ)
    (hhorizontal : Lemma57HorizontalDecay χ) :
    Lemma57ContourShiftIdentity χ := by
  refine ⟨hleft, ?_⟩
  have hright := (lemma57MellinIdentity_proved χ hD).1
  have hrightLimit := lemma57TruncatedVerticalIntegral_tendsto χ hright
  have hleftLimit := lemma57TruncatedVerticalIntegral_tendsto χ hleft
  have hsumLimit : Tendsto
      (fun T => lemma57ResidueValue χ +
        lemma57TruncatedVerticalIntegral χ (-(1 : ℝ) / 2) T +
          lemma57HorizontalIntegralError χ T)
      atTop
      (nhds (lemma57ResidueValue χ +
        lemma57VerticalIntegral χ (-(1 : ℝ) / 2) + 0)) :=
    (tendsto_const_nhds.add hleftLimit).add hhorizontal
  have heq : ∀ᶠ T : ℝ in atTop,
      lemma57TruncatedVerticalIntegral χ 1 T =
        lemma57ResidueValue χ +
          lemma57TruncatedVerticalIntegral χ (-(1 : ℝ) / 2) T +
            lemma57HorizontalIntegralError χ T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact hfinite T hT
  have hrightLimit' : Tendsto (lemma57TruncatedVerticalIntegral χ 1) atTop
      (nhds (lemma57ResidueValue χ +
        lemma57VerticalIntegral χ (-(1 : ℝ) / 2) + 0)) :=
    hsumLimit.congr' (Filter.EventuallyEq.symm heq)
  have hunique := tendsto_nhds_unique hrightLimit hrightLimit'
  simpa using hunique

end ZhangLS.Spec
