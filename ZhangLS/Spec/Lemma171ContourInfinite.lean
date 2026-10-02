import ZhangLS.Spec.Lemma171ContourHorizontal
import ZhangLS.Spec.Lemma171LeftIntegral

/-! # Lemma 17.1: passing the actual finite contour shift to infinite vertical lines -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Classical Topology

lemma lemma171_vertical_integral_real_normalization {D : ℕ}
    (χ : RealPrimitiveCharacter D) (σ : ℝ) :
    lemma171VerticalIntegral χ σ = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫t:ℝ,lemma171MellinIntegrand χ ((σ:ℂ)+(t:ℂ)*I) := by
  unfold lemma171VerticalIntegral
  rw [integral_mul_const]
  calc
    _ = ((2*(Real.pi:ℂ)*I)⁻¹*I)*
        ∫t:ℝ,lemma171MellinIntegrand χ ((σ:ℂ)+(t:ℂ)*I) := by ring
    _ = _ := by rw [lemma32_mellin_normalizing_factor]

lemma lemma171_right_vertical_integrable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Integrable (fun t:ℝ => lemma171MellinIntegrand χ ((1:ℂ)+(t:ℂ)*I)) := by
  have hh := ((lemma171_gaussian_mellin_identity χ hD).1).mul_const (-I)
  simpa only [mul_assoc,mul_neg,I_mul_I,neg_neg,mul_one] using hh

lemma lemma171_infinite_shift_of_left_integrable {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hleft : Integrable (fun t:ℝ =>
      lemma171MellinIntegrand χ (((-1/4:ℝ):ℂ)+(t:ℂ)*I))) :
    lemma171VerticalIntegral χ 1 =
      lemma171ActualResidue χ+lemma171VerticalIntegral χ (-1/4) := by
  have hr := intervalIntegral_tendsto_integral (lemma171_right_vertical_integrable χ hD)
    tendsto_neg_atTop_atBot tendsto_id
  have hl := intervalIntegral_tendsto_integral hleft
    tendsto_neg_atTop_atBot tendsto_id
  have hh := ((lemma171_lower_horizontal_decay χ hD).sub
    (lemma171_upper_horizontal_decay χ hD)).const_mul (2*Real.pi*I:ℂ)⁻¹
  have hs := ((hr.sub hl).const_mul ((1/(2*Real.pi):ℝ):ℂ)).add hh
  have heq : ∀ᶠ T:ℝ in atTop,
      ((1/(2*Real.pi):ℝ):ℂ)*
        ((∫t:ℝ in -T..T,lemma171MellinIntegrand χ (1+(t:ℂ)*I))-
          ∫t:ℝ in -T..T,lemma171MellinIntegrand χ (((-1/4:ℝ):ℂ)+(t:ℂ)*I))+
      (2*Real.pi*I:ℂ)⁻¹*
        ((∫x:ℝ in (-1/4)..1,lemma171MellinIntegrand χ ((x:ℂ)-(T:ℂ)*I))-
          ∫x:ℝ in (-1/4)..1,lemma171MellinIntegrand χ ((x:ℂ)+(T:ℂ)*I)) =
        lemma171ActualResidue χ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact lemma171_actual_normalized_finite_shift χ hD (-1/4) T
      (by norm_num) (by norm_num) hT
  have hc := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
  have hu := tendsto_nhds_unique hs hc
  simp only [sub_self,mul_zero,add_zero] at hu
  rw [lemma171_vertical_integral_real_normalization,
    lemma171_vertical_integral_real_normalization]
  simp only [Complex.ofReal_one]
  linear_combination hu

/-- The actual infinite contour shift with the left-line integrability
proved from the Gaussian envelope, rather than assumed. -/
lemma lemma171_actual_infinite_contour_shift {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    lemma171VerticalIntegral χ 1 =
      lemma171ActualResidue χ+lemma171VerticalIntegral χ (-1/4) :=
  lemma171_infinite_shift_of_left_integrable χ hD
    (lemma171_left_vertical_integrable χ hD)

/-- The genuine smoothed harmonic sum is the actual residue plus the
honestly convergent left Gaussian integral. -/
lemma lemma171_smoothed_sum_eq_residue_add_left {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (lemma171SmoothedSum χ:ℂ) =
      lemma171ActualResidue χ+lemma171VerticalIntegral χ (-1/4) := by
  rw [← (lemma171_gaussian_mellin_identity χ hD).2]
  exact lemma171_actual_infinite_contour_shift χ hD

end ZhangLS.Spec
