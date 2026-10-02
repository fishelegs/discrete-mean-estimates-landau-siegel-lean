import ZhangLS.Spec.Lemma36GoodFamily
open ZhangLS.Spec MeasureTheory
open scoped Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096


example : Lemma36Target := lemma36_proved

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
    (((lemma33ActualFamily D).filter (fun ψ =>
      ¬(‖lemma23ActualX4 χ ψ.2 ((D : ℝ)^8)‖ +
        ∫ t : ℝ in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8),
          ‖lemma23ActualX4 χ ψ.2 t‖/t) < lemma23PaperL D^(-633 : ℤ))).card : ℝ) ≤
      C*lemma33ActualPrimeMass D*lemma23PaperL D^(-739 : ℤ) := by
  simpa only [Lemma36Target,lemma36ActualBadFamily,lemma36ActualB,not_lt] using lemma36_proved

example {D : ℕ} (χ : RealPrimitiveCharacter D) (p : lemma33PrimeIndex D)
    (ψ : DirichletCharacter ℂ p.val) :
    (⟨p,ψ⟩ : lemma33CharacterIndex D) ∈ lemma36ActualBadFamily χ ↔
      Lemma23InPsi (D := D) ψ ∧
      ¬(‖lemma23ActualX4 χ ψ ((D : ℝ)^8)‖ +
        ∫ t : ℝ in Set.Ioc ((D : ℝ)^4) ((D : ℝ)^8),
          ‖lemma23ActualX4 χ ψ t‖/t) < lemma23PaperL D^(-633 : ℤ) :=
  lemma36_mem_bad_family χ p ψ
#print axioms ZhangLS.Spec.lemma36_mem_bad_family
#print axioms ZhangLS.Spec.lemma36_bad_count_times_threshold
#print axioms ZhangLS.Spec.lemma36_threshold_square
#print axioms ZhangLS.Spec.lemma36_B_mean_scale_identity
#print axioms ZhangLS.Spec.lemma36_uniform_actual_B_mean_square
#print axioms ZhangLS.Spec.lemma36_proved
#print axioms ZhangLS.Spec.lemma36_norm_arithmetic_apply
#print axioms ZhangLS.Spec.lemma36_norm_arithmetic_multiplicative
#print axioms ZhangLS.Spec.lemma36_upsilon_multiplicative
#print axioms ZhangLS.Spec.lemma36_upsilon_prime_power_sum
#print axioms ZhangLS.Spec.lemma36_upsilon_prime
#print axioms ZhangLS.Spec.lemma36_upsilon_prime_square
#print axioms ZhangLS.Spec.lemma36_upsilon_prime_power_ge_three
#print axioms ZhangLS.Spec.lemma36_absolute_convolution_multiplicative
#print axioms ZhangLS.Spec.lemma36_absolute_convolution_nonneg
#print axioms ZhangLS.Spec.lemma36_absolute_convolution_prime_power_sum
#print axioms ZhangLS.Spec.lemma36_absolute_convolution_prime
#print axioms ZhangLS.Spec.lemma36_absolute_convolution_prime_power_tail
#print axioms ZhangLS.Spec.lemma36_nu_prime_power_two_step
#print axioms ZhangLS.Spec.lemma36_absolute_convolution_prime_power_le
#print axioms ZhangLS.Spec.lemma36_absolute_convolution_le
#print axioms ZhangLS.Spec.lemma36_varsigma_norm_le
#print axioms ZhangLS.Spec.lemma36_varsigma_norm_square_le
#print axioms ZhangLS.Spec.lemma36_good_partial_sums_iff_bounds
#print axioms ZhangLS.Spec.lemma36_not_good_family_eq_union
#print axioms ZhangLS.Spec.lemma36_not_good_count_le_sum
#print axioms ZhangLS.Spec.lemma36_actual_not_good_count
#print axioms ZhangLS.Spec.lemma36_actual_X4_eq_partial_sum
#print axioms ZhangLS.Spec.lemma36_actual_X4_measurable
#print axioms ZhangLS.Spec.lemma36_actual_X4_partial_norm_bound
#print axioms ZhangLS.Spec.lemma36_actual_X4_integrable
#print axioms ZhangLS.Spec.lemma36_actual_X4_power_weighted_integrable
#print axioms ZhangLS.Spec.lemma36_interval_parameters
#print axioms ZhangLS.Spec.lemma36_inverse_integral
#print axioms ZhangLS.Spec.lemma36_inverse_integrable
#print axioms ZhangLS.Spec.lemma36_actual_weighted_integral_cauchy
#print axioms ZhangLS.Spec.lemma36_actual_weighted_square_integral_mean_le
#print axioms ZhangLS.Spec.lemma36_actual_integral_mean_square_le
#print axioms ZhangLS.Spec.lemma36_actual_B_nonneg
#print axioms ZhangLS.Spec.lemma36_actual_B_mean_square_le
#print axioms ZhangLS.Spec.lemma36_actual_X4_eq_centered_sum
#print axioms ZhangLS.Spec.lemma36_actual_X4_mean_eq
#print axioms ZhangLS.Spec.lemma36_centered_coefficient_energy_le
#print axioms ZhangLS.Spec.lemma36_actual_X4_mean_energy_le
#print axioms ZhangLS.Spec.lemma36_uniform_actual_X4_mean
