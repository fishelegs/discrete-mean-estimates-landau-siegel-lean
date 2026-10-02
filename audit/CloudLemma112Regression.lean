import ZhangLS.Spec.Lemma112
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology ComplexConjugate

-- Fully expanded original target: no (A), Ψ₁, final-estimate input, or extra floor.
example : Lemma112Target ↔
    (∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
      ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
        D₀ ≤ D →
        (p.Prime ∧ ψ.IsPrimitive ∧ Real.exp ((Real.log (D : ℝ)) ^ 9) < (p : ℝ) ∧
          (p : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ 9) * (1 + (Real.log (D : ℝ)) ^ (-68 : ℤ))) →
        ∀ {s : ℂ},
          (s.re = 1 / 2 ∧ |s.im - 2 * Real.pi * (Real.log (D : ℝ)) ^ 519| < (Real.log (D : ℝ)) ^ 405) →
          letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
          ‖(∑' n : ℕ, (if n = 0 then 0 else
              (χ.chi (n : ZMod D) * ψ (n : ZMod p)) / (n : ℂ) ^ s) *
              ((-500 * (∫ z in (1 / 2 : ℝ)..(251 / 500 : ℝ),
                  zhangGaussianWeight D (Real.exp ((Real.log (D : ℝ)) ^ 9) ^ z / n)) +
                500 * (∫ z in (251 / 500 : ℝ)..(63 / 125 : ℝ),
                  zhangGaussianWeight D (Real.exp ((Real.log (D : ℝ)) ^ 9) ^ z / n)) : ℝ) : ℂ)) -
            lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
              (∑' n : ℕ, (if n = 0 then 0 else
                (χ.chi (n : ZMod D) * ψ⁻¹ (n : ZMod p)) / (n : ℂ) ^ (1 - s)) *
                ((-500 * (∫ z in (62 / 125 : ℝ)..(249 / 500 : ℝ),
                    zhangGaussianWeight D
                      (Real.exp ((Real.log (D : ℝ)) ^ 9) ^ z * (D : ℝ) * (Real.log (D : ℝ)) ^ 519 / n)) +
                  500 * (∫ z in (249 / 500 : ℝ)..(1 / 2 : ℝ),
                    zhangGaussianWeight D
                      (Real.exp ((Real.log (D : ℝ)) ^ 9) ^ z * (D : ℝ) * (Real.log (D : ℝ)) ^ 519 / n)) : ℝ) : ℂ))‖ ≤
            C * ((Real.log (D : ℝ)) ^ (-68 : ℤ) *
              (∫ v in (-((Real.log (D : ℝ)) ^ 20))..((Real.log (D : ℝ)) ^ 20),
                ‖∑ n ∈ (Finset.Icc 1 ⌈Real.exp ((Real.log (D : ℝ)) ^ 9) ^ (63 / 125 : ℝ)⌉₊).filter
                    (fun n : ℕ => (n : ℝ) < Real.exp ((Real.log (D : ℝ)) ^ 9) ^ (63 / 125 : ℝ)),
                  (χ.chi (n : ZMod D) * ψ (n : ZMod p)) *
                    exp (-(s + I * (v : ℂ)) * (Real.log (n : ℝ) : ℂ))‖ *
                  Real.exp (-(v ^ 2) / (4 * (Real.log (D : ℝ)) ^ 30))))) := by
  rfl

example : Lemma112Target := lemma112_proved

-- Both height endpoints are excluded.
example (D : ℕ) :
    ¬ Lemma112InRegion D ⟨1 / 2, (lemma23PaperCenter D).im + lemma23PaperL D ^ 405⟩ := by
  have hpow : 0 ≤ lemma23PaperL D ^ 405 := pow_nonneg (Real.log_natCast_nonneg D) _
  simp [Lemma112InRegion, abs_of_nonneg hpow]

example (D : ℕ) :
    ¬ Lemma112InRegion D ⟨1 / 2, (lemma23PaperCenter D).im - lemma23PaperL D ^ 405⟩ := by
  have hpow : 0 ≤ lemma23PaperL D ^ 405 := pow_nonneg (Real.log_natCast_nonneg D) _
  simp [Lemma112InRegion, abs_of_nonneg hpow]

-- n=P₁ is excluded from the short polynomial.
example (D n : ℕ) (h : (n : ℝ) = lemma112PaperP1 D) :
    n ∉ (Finset.Icc 1 ⌈lemma112PaperP1 D⌉₊).filter
      (fun k : ℕ => (k : ℝ) < lemma112PaperP1 D) := by
  simp [Finset.mem_filter, h]

-- The actual inverse character is conjugation, including at nonunits.
example {D p : ℕ} (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (n : ℕ) :
    lemma112Coefficient χ ψ⁻¹ n = conj (lemma112Coefficient χ ψ n) := by
  unfold lemma112Coefficient RealPrimitiveCharacter.evalNat
  rw [map_mul, χ.conj_eval, ← MulChar.star_apply' ψ (n : ZMod p)]
  rfl

example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ) :
    (lemma44CharacterTwist χ ψ).conductor = D * p :=
  (lemma112_twist_family_data χ ψ hL hψ).2.1

example {D p : ℕ} (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {s : ℂ} (hs : s.re = 1 / 2) (v : ℝ) :
    ‖lemma112ShortPolynomial χ ψ⁻¹ (1 - s - I * (v : ℂ))‖ =
      ‖lemma112ShortPolynomial χ ψ (s + I * (v : ℂ))‖ :=
  lemma112_short_polynomial_critical_reflection χ ψ hs v

-- The displayed weight ω₁(iv) is exactly the positive real Gaussian in E₂.
example (D : ℕ) (v : ℝ) : lemma57OmegaOne D (I * (v : ℂ)) =
    (Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) : ℂ) :=
  lemma61_omega_one_imaginary_axis D v

-- Both z endpoints required by the paper are present in the local AFE.
example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    (hthreshold : lemma23SectionFourModulusThreshold ≤ D) {s : ℂ} (hs : Lemma112InRegion D s) :
    ‖lemma112GaussianDefect χ ψ s (1 / 2)‖ ≤ lemma112ApproximationConstant * lemma112ActualE2 χ ψ s :=
  lemma112_actual_approximation_bound χ ψ hψ hD hL hthreshold hs (by norm_num)

example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : Lemma23InPsi (D := D) ψ) (hD : 1 < D) (hL : 64 ≤ lemma23PaperL D)
    (hthreshold : lemma23SectionFourModulusThreshold ≤ D) {s : ℂ} (hs : Lemma112InRegion D s) :
    ‖lemma112GaussianDefect χ ψ s (63 / 125)‖ ≤ lemma112ApproximationConstant * lemma112ActualE2 χ ψ s :=
  lemma112_actual_approximation_bound χ ψ hψ hD hL hthreshold hs (by norm_num)

-- Actual E₂ has a proved polynomial floor, without modifying its definition.
example {D p : ℕ} (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 64 ≤ lemma23PaperL D) {s : ℂ} (hs : 0 ≤ s.re) :
    lemma23PaperL D ^ (-53 : ℤ) ≤ lemma112ActualE2 χ ψ s :=
  lemma112_E2_polynomial_floor χ ψ hL hs

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma112GaussianDefect
#print axioms ZhangLS.Spec.lemma112_dual_series_interval_integrable
#print axioms ZhangLS.Spec.lemma112_defect_integral_identity
#print axioms ZhangLS.Spec.lemma112_integrated_defect_eq
#print axioms ZhangLS.Spec.lemma112_approximation_constant_pos
#print axioms ZhangLS.Spec.lemma112_integrated_approximation_bound
#print axioms ZhangLS.Spec.lemma112_proved
#print axioms ZhangLS.Spec.lemma112ActualLeftMellinIntegral
#print axioms ZhangLS.Spec.lemma112LeftApproximationConstant
#print axioms ZhangLS.Spec.lemma112ApproximationConstant
#print axioms ZhangLS.Spec.lemma112_actual_original_left_dual_bound
#print axioms ZhangLS.Spec.lemma112_actual_approximation_bound
#print axioms ZhangLS.Spec.lemma112_exp_small_at_paper_scale
#print axioms ZhangLS.Spec.lemma112_frequency_recovery_budget
#print axioms ZhangLS.Spec.lemma112_gaussian_tail_recovery_budget
#print axioms ZhangLS.Spec.lemma112_P1_one_lt
#print axioms ZhangLS.Spec.lemma112_short_cutoff_card
#print axioms ZhangLS.Spec.lemma112_actual_error_integral_lower
#print axioms ZhangLS.Spec.lemma112_E2_polynomial_floor
#print axioms ZhangLS.Spec.lemma112ConductorScale
#print axioms ZhangLS.Spec.lemma112ErrorDifferenceNumerator
#print axioms ZhangLS.Spec.lemma112ActualZErrorIntegrand
#print axioms ZhangLS.Spec.lemma112ErrorRegularIntegrand
#print axioms ZhangLS.Spec.lemma112_conductor_scale_pos
#print axioms ZhangLS.Spec.lemma112_error_difference_at_zero
#print axioms ZhangLS.Spec.lemma112_error_regular_eq_actual
#print axioms ZhangLS.Spec.lemma112_error_difference_rectangle_differentiable
#print axioms ZhangLS.Spec.lemma112_error_regular_rectangle_differentiable
#print axioms ZhangLS.Spec.lemma112_actual_error_vertical_point_bound
#print axioms ZhangLS.Spec.lemma112_actual_error_vertical_integral_bound
#print axioms ZhangLS.Spec.lemma112_error_vertical_ae_eq
#print axioms ZhangLS.Spec.lemma112_error_vertical_interval_integrable
#print axioms ZhangLS.Spec.lemma112_error_vertical_integral_eq
#print axioms ZhangLS.Spec.lemma112_error_regular_path_rectangle_cauchy
#print axioms ZhangLS.Spec.lemma112_actual_error_line_shift
#print axioms ZhangLS.Spec.lemma112FourierGaussian
#print axioms ZhangLS.Spec.lemma112_fourier_gaussian_identity
#print axioms ZhangLS.Spec.lemma112_fourier_gaussian_integrable
#print axioms ZhangLS.Spec.lemma112_fourier_gaussian_integral
#print axioms ZhangLS.Spec.lemma112_fourier_gaussian_norm
#print axioms ZhangLS.Spec.lemma112_finite_polynomial_gaussian_integral
#print axioms ZhangLS.Spec.lemma112_dirichlet_term_norm_le_one
#print axioms ZhangLS.Spec.lemma112_finite_polynomial_norm_bound
#print axioms ZhangLS.Spec.lemma112_finite_gaussian_recovery_bound
#print axioms ZhangLS.Spec.lemma112_finite_polynomial_gaussian_integrable
#print axioms ZhangLS.Spec.lemma112_truncated_gaussian_norm_lower
#print axioms ZhangLS.Spec.lemma112_scale_log_bounds
#print axioms ZhangLS.Spec.lemma112_dual_scale_log_bounds
#print axioms ZhangLS.Spec.lemma112_scale_exponential_rectangle_bound
#print axioms ZhangLS.Spec.lemma112_dual_scale_left_bound
#print axioms ZhangLS.Spec.lemma112_twist_modulus_bound
#print axioms ZhangLS.Spec.lemma112_actual_L_scale_rectangle_bound
#print axioms ZhangLS.Spec.lemma112_actual_horizontal_L_integral_bound
#print axioms ZhangLS.Spec.lemma112_short_polynomial_norm_bound
#print axioms ZhangLS.Spec.lemma112_model_scale_identity
#print axioms ZhangLS.Spec.lemma112_error_horizontal_factor_bound
#print axioms ZhangLS.Spec.lemma112_actual_original_left_integrand_split
#print axioms ZhangLS.Spec.lemma112_reciprocal_model_interval_integrable
#print axioms ZhangLS.Spec.lemma112_actual_left_tail_interval_integrable
#print axioms ZhangLS.Spec.lemma112_actual_original_left_integral_split
#print axioms ZhangLS.Spec.lemma112GaussianSeries
#print axioms ZhangLS.Spec.lemma112_actual_gaussian_mellin
#print axioms ZhangLS.Spec.lemma112_actual_gaussian_summable
#print axioms ZhangLS.Spec.lemma112_actual_mellin_numerator_entire
#print axioms ZhangLS.Spec.lemma112_actual_wide_rectangle_residue
#print axioms ZhangLS.Spec.lemma112_scale_log_bound
#print axioms ZhangLS.Spec.lemma112_actual_right_mellin_truncation
#print axioms ZhangLS.Spec.lemma112_error_horizontal_point_bound
#print axioms ZhangLS.Spec.lemma112_error_horizontal_integral_bound
#print axioms ZhangLS.Spec.lemma112_actual_original_left_Z_error_bound
#print axioms ZhangLS.Spec.lemma112PaperP1
#print axioms ZhangLS.Spec.lemma112Coefficient
#print axioms ZhangLS.Spec.lemma112JtildeOne
#print axioms ZhangLS.Spec.lemma112JtildeTwo
#print axioms ZhangLS.Spec.lemma112ShortPolynomial
#print axioms ZhangLS.Spec.lemma112ActualE2
#print axioms ZhangLS.Spec.Lemma112InRegion
#print axioms ZhangLS.Spec.Lemma112Target
#print axioms ZhangLS.Spec.lemma112_coefficient_eq_twist
#print axioms ZhangLS.Spec.lemma112_coefficient_norm_le_one
#print axioms ZhangLS.Spec.lemma112_coefficient_one
#print axioms ZhangLS.Spec.lemma112_short_polynomial_differentiable
#print axioms ZhangLS.Spec.lemma112_error_integrand_continuous
#print axioms ZhangLS.Spec.lemma112_error_integrand_interval_integrable
#print axioms ZhangLS.Spec.lemma112_E2_nonneg
#print axioms ZhangLS.Spec.lemma112_short_polynomial_conjugation
#print axioms ZhangLS.Spec.lemma112_short_polynomial_critical_reflection
#print axioms ZhangLS.Spec.lemma112_region_subset_lemma51
#print axioms ZhangLS.Spec.lemma112_region_subset_lemma61
#print axioms ZhangLS.Spec.lemma112_twist_family_data
#print axioms ZhangLS.Spec.lemma112_actual_twist_functional_equation
#print axioms ZhangLS.Spec.lemma112_normalized_integral_norm_le
#print axioms ZhangLS.Spec.lemma112_reciprocal_far_left_integral_bound
#print axioms ZhangLS.Spec.lemma112_reciprocal_horizontal_integral_bound
#print axioms ZhangLS.Spec.lemma112_reciprocal_tail_truncation_bound
#print axioms ZhangLS.Spec.lemma112_reciprocal_tail_rectangle_differentiable
#print axioms ZhangLS.Spec.lemma112_reciprocal_tail_rectangle_cauchy
#print axioms ZhangLS.Spec.lemma112_reciprocal_tail_point_bound
#print axioms ZhangLS.Spec.lemma112_reciprocal_far_left_point_bound
#print axioms ZhangLS.Spec.lemma112ReciprocalModelIntegrand
#print axioms ZhangLS.Spec.lemma112_reciprocal_model_reflection
#print axioms ZhangLS.Spec.lemma112_reciprocal_model_vertical_identity
#print axioms ZhangLS.Spec.lemma112_actual_finite_reciprocal_model_bound
#print axioms ZhangLS.Spec.lemma112ReciprocalTailTerm
#print axioms ZhangLS.Spec.lemma112_reciprocal_tail_summable
#print axioms ZhangLS.Spec.lemma112_actual_reciprocal_series_split
#print axioms ZhangLS.Spec.lemma112_P1_log
#print axioms ZhangLS.Spec.lemma112_reciprocal_horizontal_term_bound
#print axioms ZhangLS.Spec.lemma112_reciprocal_horizontal_sum_bound
#print axioms ZhangLS.Spec.lemma112_reciprocal_far_left_term_bound
#print axioms ZhangLS.Spec.lemma112_reciprocal_far_left_sum_bound
#print axioms ZhangLS.Spec.lemma112ActualReciprocalTailIntegrand
#print axioms ZhangLS.Spec.lemma112FiniteGaussianSum
#print axioms ZhangLS.Spec.lemma112_dual_scale_twice_below_cutoff
#print axioms ZhangLS.Spec.lemma112_finite_gaussian_cutoff_bound
#print axioms ZhangLS.Spec.lemma112_exp_remainder_le_polynomial
#print axioms ZhangLS.Spec.lemma112_exp_remainder_le_E2
#print axioms ZhangLS.Spec.lemma112ShortRightMellinIntegrand
#print axioms ZhangLS.Spec.lemma112_short_mellin_eq_finite_sum
#print axioms ZhangLS.Spec.lemma112_short_mellin_integrable
#print axioms ZhangLS.Spec.lemma112_actual_short_gaussian_mellin
#print axioms ZhangLS.Spec.lemma112_short_right_gaussian_bound
#print axioms ZhangLS.Spec.lemma112_actual_short_right_truncation
#print axioms ZhangLS.Spec.lemma112_actual_finite_short_mellin_dual_bound
#print axioms ZhangLS.Spec.lemma112_profile_monotone
#print axioms ZhangLS.Spec.lemma112_scaled_weight_coordinate
#print axioms ZhangLS.Spec.lemma112ScaledGaussianTerm
#print axioms ZhangLS.Spec.lemma112_scaled_gaussian_term_continuous
#print axioms ZhangLS.Spec.lemma112_scaled_gaussian_term_norm_le
#print axioms ZhangLS.Spec.lemma112_scaled_gaussian_interval_hasSum
#print axioms ZhangLS.Spec.lemma112_scaled_gaussian_interval_series
#print axioms ZhangLS.Spec.lemma112_gaussian_series_continuousOn
#print axioms ZhangLS.Spec.lemma112_gaussian_series_interval_integrable
#print axioms ZhangLS.Spec.lemma112_JtildeOne_integral
#print axioms ZhangLS.Spec.lemma112_JtildeTwo_integral
#print axioms ZhangLS.Spec.lemma112_twist_Z_logDeriv_normalized_wide
#print axioms ZhangLS.Spec.lemma112_twist_Z_log_modulus_wide
#print axioms ZhangLS.Spec.lemma112_twist_Z_norm_model_wide
#print axioms ZhangLS.Spec.lemma112DualScale
#print axioms ZhangLS.Spec.lemma112_dual_scale_pos
#print axioms ZhangLS.Spec.lemma112_dual_scale_log
#print axioms ZhangLS.Spec.lemma112_twist_Z_scale_cancellation
#print axioms ZhangLS.Spec.lemma112_Dt0_log_budget
#print axioms ZhangLS.Spec.lemma112_dual_scale_cutoff_gap
