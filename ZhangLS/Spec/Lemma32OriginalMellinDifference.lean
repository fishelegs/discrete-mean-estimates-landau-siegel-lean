import ZhangLS.Spec.Lemma32ActualGammaMellin
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32SmoothedWeightedDifference {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  lemma32SmoothedWeightedSeries χ ((D : ℝ)^8)-lemma32SmoothedWeightedSeries χ ((D : ℝ)^4)

lemma lemma32_actual_original_right_Gamma_difference {D : ℕ} (χ : RealPrimitiveCharacter D) (t : ℝ) :
    lemma32RightGammaIntegrand χ ((D : ℝ)^8) t-lemma32RightGammaIntegrand χ ((D : ℝ)^4) t =
      lemma32CircleIntegrand χ (1+(t : ℂ)*I) := by
  have h8 : Complex.exp ((1+(t : ℂ)*I)*(Real.log ((D : ℝ)^8) : ℂ)) =
      Complex.exp (8*(lemma23PaperL D : ℂ)*(1+(t : ℂ)*I)) := by
    rw [Real.log_pow]
    congr 1
    dsimp [lemma23PaperL]
    push_cast
    ring
  have h4 : Complex.exp ((1+(t : ℂ)*I)*(Real.log ((D : ℝ)^4) : ℂ)) =
      Complex.exp (4*(lemma23PaperL D : ℂ)*(1+(t : ℂ)*I)) := by
    rw [Real.log_pow]
    congr 1
    dsimp [lemma23PaperL]
    push_cast
    ring
  unfold lemma32RightGammaIntegrand lemma32CircleIntegrand lemma32SmoothingDifference
  rw [h8,h4,show (1 : ℂ)+(1+(t : ℂ)*I) = 2+(t : ℂ)*I by ring]
  ring

lemma lemma32_actual_original_right_Gamma_integrable {D : ℕ} (χ : RealPrimitiveCharacter D) :
    Integrable (fun t : ℝ => lemma32CircleIntegrand χ (1+(t : ℂ)*I)) := by
  have hp : 0 < (D : ℝ) := by exact_mod_cast χ.modulus_pos
  have he : (fun t : ℝ => lemma32RightGammaIntegrand χ ((D : ℝ)^8) t-
      lemma32RightGammaIntegrand χ ((D : ℝ)^4) t) =
      (fun t : ℝ => lemma32CircleIntegrand χ (1+(t : ℂ)*I)) :=
    funext (lemma32_actual_original_right_Gamma_difference χ)
  rw [← he]
  exact (lemma32_actual_right_Gamma_integrand_integrable χ _ (pow_pos hp 8)).sub
    (lemma32_actual_right_Gamma_integrand_integrable χ _ (pow_pos hp 4))

lemma lemma32_actual_original_Gamma_mellin_difference {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ((1/(2*Real.pi) : ℝ) : ℂ)*
      (∫ t : ℝ, lemma32CircleIntegrand χ (1+(t : ℂ)*I)) =
      lemma32SmoothedWeightedDifference χ := by
  have hp : 0 < (D : ℝ) := by exact_mod_cast χ.modulus_pos
  have he : (fun t : ℝ => lemma32RightGammaIntegrand χ ((D : ℝ)^8) t-
      lemma32RightGammaIntegrand χ ((D : ℝ)^4) t) =
      (fun t : ℝ => lemma32CircleIntegrand χ (1+(t : ℂ)*I)) :=
    funext (lemma32_actual_original_right_Gamma_difference χ)
  rw [← he,integral_sub (lemma32_actual_right_Gamma_integrand_integrable χ _ (pow_pos hp 8))
    (lemma32_actual_right_Gamma_integrand_integrable χ _ (pow_pos hp 4)),mul_sub,
    lemma32_actual_full_Gamma_mellin χ _ (pow_pos hp 8),
    lemma32_actual_full_Gamma_mellin χ _ (pow_pos hp 4)]
  rfl

lemma lemma32_actual_smoothed_difference_series {D : ℕ} (χ : RealPrimitiveCharacter D) :
    lemma32SmoothedWeightedDifference χ =
      ∑' n : ℕ, LSeries.term (fun n => (lemma32ActualCoefficient χ n : ℂ)) 1 n*
        ((Real.exp (-(n : ℝ)/(D : ℝ)^8) : ℂ)-(Real.exp (-(n : ℝ)/(D : ℝ)^4) : ℂ)) := by
  have hp : 0 < (D : ℝ) := by exact_mod_cast χ.modulus_pos
  unfold lemma32SmoothedWeightedDifference lemma32SmoothedWeightedSeries
  rw [← Summable.tsum_sub (lemma32_actual_smoothed_weighted_summable χ _ (pow_pos hp 8))
    (lemma32_actual_smoothed_weighted_summable χ _ (pow_pos hp 4))]
  apply tsum_congr
  intro n
  ring

end ZhangLS.Spec
