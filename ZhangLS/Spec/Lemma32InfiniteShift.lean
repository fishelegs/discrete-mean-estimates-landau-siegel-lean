import ZhangLS.Spec.Lemma32HorizontalDecay
import ZhangLS.Spec.Lemma32OriginalMellinDifference
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Metric Set Filter
open scoped Classical Topology
set_option maxHeartbeats 2000000

noncomputable def lemma32LeftVerticalIntegral {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  ((1/(2*Real.pi) : ℝ) : ℂ)*∫ t : ℝ,
    lemma32CircleIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)

lemma lemma32_actual_infinite_contour_shift {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*
      ((∫ t : ℝ, lemma32CircleIntegrand χ (1+(t : ℂ)*I))-
        ∫ t : ℝ, lemma32CircleIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I)) =
      lemma32ActualResidue χ := by
  have hr := intervalIntegral_tendsto_integral (lemma32_actual_original_right_Gamma_integrable χ)
    tendsto_neg_atTop_atBot tendsto_id
  have hl := intervalIntegral_tendsto_integral
    (lemma32_actual_left_vertical_integrable χ hD (-1/4) (by norm_num) (by norm_num) (by norm_num))
    tendsto_neg_atTop_atBot tendsto_id
  have hh := ((lemma32_actual_lower_horizontal_decay χ hD).sub
    (lemma32_actual_upper_horizontal_decay χ hD)).const_mul (2*Real.pi*I : ℂ)⁻¹
  have hs := ((hr.sub hl).const_mul ((1/(2*Real.pi) : ℝ) : ℂ)).add hh
  have heq : ∀ᶠ T : ℝ in atTop,
      ((1/(2*Real.pi) : ℝ) : ℂ)*
        ((∫ t : ℝ in -T..T, lemma32CircleIntegrand χ (1+(t : ℂ)*I))-
          ∫ t : ℝ in -T..T, lemma32CircleIntegrand χ (((-1/4 : ℝ) : ℂ)+(t : ℂ)*I))+
      (2*Real.pi*I : ℂ)⁻¹*
        ((∫ x : ℝ in (-1/4)..1, lemma32CircleIntegrand χ ((x : ℂ)-(T : ℂ)*I))-
          ∫ x : ℝ in (-1/4)..1, lemma32CircleIntegrand χ ((x : ℂ)+(T : ℂ)*I)) =
        lemma32ActualResidue χ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact lemma32_actual_normalized_finite_shift χ hD (-1/4) T (by norm_num) (by norm_num) hT
  have hc := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
  have hu := tendsto_nhds_unique hs hc
  simpa only [sub_self,mul_zero,add_zero] using hu

lemma lemma32_actual_smoothed_difference_eq_residue_add_left {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    lemma32SmoothedWeightedDifference χ = lemma32ActualResidue χ+lemma32LeftVerticalIntegral χ := by
  have hs := lemma32_actual_infinite_contour_shift χ hD
  have hm := lemma32_actual_original_Gamma_mellin_difference χ
  change ((1/(2*Real.pi) : ℝ) : ℂ)*(∫ t : ℝ, lemma32CircleIntegrand χ (1+(t : ℂ)*I)) =
    lemma32SmoothedWeightedDifference χ at hm
  rw [← hm]
  unfold lemma32LeftVerticalIntegral
  linear_combination hs

end ZhangLS.Spec
