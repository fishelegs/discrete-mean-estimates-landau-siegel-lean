import ZhangLS.Spec.FourthContourFinite
import ZhangLS.Spec.LogContourBounds

/-! Actual infinite fourth-pole contour shift. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Classical Topology

lemma lemma171_log_horizontal_integral_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (t : ℝ) (ht : 1 ≤ |t|) :
    ‖∫x:ℝ in (-1/4)..1,lemma171LogMellinIntegrand χ ((x:ℂ)+(t:ℂ)*I)‖ ≤
      (5/4)*lemma171HorizontalConstant D*Real.exp (-t^2/(8*lemma23PaperL D^30)) := by
  have hbound : ∀ x ∈ Set.uIoc (-1/4:ℝ) 1,
      ‖lemma171LogMellinIntegrand χ ((x:ℂ)+(t:ℂ)*I)‖ ≤
      lemma171HorizontalConstant D*Real.exp (-t^2/(8*lemma23PaperL D^30)) := by
    intro x hx
    rw [Set.uIoc_of_le (by norm_num : (-1/4:ℝ)≤1)] at hx
    exact lemma171_log_mellin_horizontal_bound χ hD x t hx.1.le hx.2 ht
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  calc
    _ ≤ (lemma171HorizontalConstant D*Real.exp (-t^2/(8*lemma23PaperL D^30)))*
        |1-(-1/4:ℝ)| := hi
    _ = _ := by norm_num;ring

lemma lemma171_log_upper_horizontal_decay {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Tendsto (fun T:ℝ => ∫x:ℝ in (-1/4)..1,
      lemma171LogMellinIntegrand χ ((x:ℂ)+(T:ℂ)*I)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    exact lemma171_log_horizontal_integral_bound χ hD T
      (by rw [abs_of_nonneg (by linarith : 0≤T)];exact hT)
  · simpa only [mul_zero] using
      (lemma171_gaussian_height_tendsto_zero hD).const_mul ((5/4)*lemma171HorizontalConstant D)

lemma lemma171_log_lower_horizontal_decay {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) :
    Tendsto (fun T:ℝ => ∫x:ℝ in (-1/4)..1,
      lemma171LogMellinIntegrand χ ((x:ℂ)-(T:ℂ)*I)) atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall (fun T => norm_nonneg _))
  · filter_upwards [eventually_ge_atTop (1:ℝ)] with T hT
    have hh := lemma171_log_horizontal_integral_bound χ hD (-T)
      (by rw [abs_neg,abs_of_nonneg (by linarith : 0≤T)];exact hT)
    simpa only [Complex.ofReal_neg,neg_mul,← sub_eq_add_neg,neg_sq] using hh
  · simpa only [mul_zero] using
      (lemma171_gaussian_height_tendsto_zero hD).const_mul ((5/4)*lemma171HorizontalConstant D)

lemma lemma171_log_vertical_integral_real_normalization {D : ℕ}
    (χ : RealPrimitiveCharacter D) (σ : ℝ) :
    lemma171LogVerticalIntegral χ σ = ((1/(2*Real.pi):ℝ):ℂ)*
      ∫t:ℝ,lemma171LogMellinIntegrand χ ((σ:ℂ)+(t:ℂ)*I) := by
  unfold lemma171LogVerticalIntegral
  rw [integral_mul_const]
  calc
    _ = ((2*(Real.pi:ℂ)*I)⁻¹*I)*
        ∫t:ℝ,lemma171LogMellinIntegrand χ ((σ:ℂ)+(t:ℂ)*I) := by ring
    _ = _ := by rw [lemma32_mellin_normalizing_factor]

lemma lemma171_log_infinite_shift_of_left_integrable {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hleft : Integrable (fun t:ℝ =>
      lemma171LogMellinIntegrand χ (((-1/4:ℝ):ℂ)+(t:ℂ)*I))) :
    lemma171LogVerticalIntegral χ 1 =
      lemma171ActualLogResidue χ+lemma171LogVerticalIntegral χ (-1/4) := by
  have hr := intervalIntegral_tendsto_integral (lemma171_log_right_vertical_integrable χ hD)
    tendsto_neg_atTop_atBot tendsto_id
  have hl := intervalIntegral_tendsto_integral hleft
    tendsto_neg_atTop_atBot tendsto_id
  have hh := ((lemma171_log_lower_horizontal_decay χ hD).sub
    (lemma171_log_upper_horizontal_decay χ hD)).const_mul (2*Real.pi*I:ℂ)⁻¹
  have hs := ((hr.sub hl).const_mul ((1/(2*Real.pi):ℝ):ℂ)).add hh
  have heq : ∀ᶠ T:ℝ in atTop,
      ((1/(2*Real.pi):ℝ):ℂ)*
        ((∫t:ℝ in -T..T,lemma171LogMellinIntegrand χ (1+(t:ℂ)*I))-
          ∫t:ℝ in -T..T,lemma171LogMellinIntegrand χ (((-1/4:ℝ):ℂ)+(t:ℂ)*I))+
      (2*Real.pi*I:ℂ)⁻¹*
        ((∫x:ℝ in (-1/4)..1,lemma171LogMellinIntegrand χ ((x:ℂ)-(T:ℂ)*I))-
          ∫x:ℝ in (-1/4)..1,lemma171LogMellinIntegrand χ ((x:ℂ)+(T:ℂ)*I)) =
        lemma171ActualLogResidue χ := by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    exact lemma171_log_actual_normalized_finite_shift χ hD (-1/4) T
      (by norm_num) (by norm_num) hT
  have hc := tendsto_const_nhds.congr' (Filter.EventuallyEq.symm heq)
  have hu := tendsto_nhds_unique hs hc
  simp only [sub_self,mul_zero,add_zero] at hu
  rw [lemma171_log_vertical_integral_real_normalization,
    lemma171_log_vertical_integral_real_normalization]
  simp only [Complex.ofReal_one]
  linear_combination hu

/-- The actual infinite contour shift with the left-line integrability
proved from the Gaussian envelope, rather than assumed. -/
lemma lemma171_log_actual_infinite_contour_shift {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    lemma171LogVerticalIntegral χ 1 =
      lemma171ActualLogResidue χ+lemma171LogVerticalIntegral χ (-1/4) :=
  lemma171_log_infinite_shift_of_left_integrable χ hD
    (lemma171_log_left_vertical_integrable χ hD)

end ZhangLS.Spec
