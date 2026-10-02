import ZhangLS.Spec.Lemma34
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open MeasureTheory Set
open scoped Classical

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ,
    ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      ((lemma34ActualBadFamily χ).card : ℝ) ≤
        C*lemma33ActualPrimeMass D*lemma23PaperL D^(-740 : ℤ) := lemma34_proved

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : ⌈Real.exp 3⌉₊ ≤ D) :
    (((lemma33ActualFamily D).filter (fun ψ => ¬((‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) ((D : ℝ)^80)‖ +
      ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) ((D : ℝ)^80)‖ +
      (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
        (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) t‖ +
          ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) t‖)/t)) < lemma23PaperL D^1171))).card : ℝ) ≤
      (51208*81^1600)*lemma33ActualPrimeMass D*lemma23PaperL D^(-740 : ℤ) := by
  simpa only [lemma34ActualBadFamily,lemma34ActualB,not_lt] using
    lemma34_actual_bad_count χ (lemma33_parameters_at_threshold hD)

example {D : ℕ} (χ : RealPrimitiveCharacter D) (p : lemma33PrimeIndex D)
    (ψ : DirichletCharacter ℂ p.val) :
    (⟨p,ψ⟩ : lemma33CharacterIndex D) ∈ lemma34ActualBadFamily χ ↔
      (p.val.Prime ∧ ψ.IsPrimitive ∧ lemma23PaperP D < (p.val : ℝ) ∧
        (p.val : ℝ) < lemma23PaperP D*(1+lemma23PaperL D^(-68 : ℤ))) ∧
      ¬((‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) ((D : ℝ)^80)‖ +
      ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) ((D : ℝ)^80)‖ +
      (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
        (‖lemma23ActualX1 χ ψ (lemma23PaperCenter D) t‖ +
          ‖lemma23ActualX2 χ ψ (lemma23PaperCenter D) t‖)/t)) < lemma23PaperL D^1171) := by
  simpa only [Lemma23InPsi,lemma34ActualB] using lemma34_mem_bad_family χ p ψ

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hL : 3 ≤ lemma23PaperL D) :
    (∑ ψ ∈ lemma33ActualFamily D, (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) ((D : ℝ)^80)‖ +
      ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) ((D : ℝ)^80)‖ +
      (∫ t in Set.Ioc (1 : ℝ) ((D : ℝ)^80),
        (‖lemma23ActualX1 χ ψ.2 (lemma23PaperCenter D) t‖ +
          ‖lemma23ActualX2 χ ψ.2 (lemma23PaperCenter D) t‖)/t))^2) ≤
      (51208*81^1600)*lemma33ActualPrimeMass D*lemma23PaperL D^1602 := by
  exact lemma34_actual_B_mean_square χ hL

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma34_multichoose_recurrence
#print axioms ZhangLS.Spec.lemma34_multichoose_40_square_le_1600
#print axioms ZhangLS.Spec.lemma34_tau_multiplicative
#print axioms ZhangLS.Spec.lemma34_tau_prime_power
#print axioms ZhangLS.Spec.lemma34_tau40_square_le_tau1600
#print axioms ZhangLS.Spec.lemma34_weighted_convolution_le
#print axioms ZhangLS.Spec.lemma34_tau_weighted_sum_le_harmonic_pow
#print axioms ZhangLS.Spec.lemma34_tuple_sum_succ
#print axioms ZhangLS.Spec.lemma34_tuple_sum_recurrence
#print axioms ZhangLS.Spec.lemma34_tuple_sum_zero
#print axioms ZhangLS.Spec.lemma34_tuple_sum_le_arithmetic_pow
#print axioms ZhangLS.Spec.lemma34_tau2_eq_divisor_card
#print axioms ZhangLS.Spec.lemma34_actual_tau40_le_standard
#print axioms ZhangLS.Spec.lemma34_actual_tau40_square_le_tau1600
#print axioms ZhangLS.Spec.lemma34_actual_tau40_weighted_sum_le
#print axioms ZhangLS.Spec.lemma34_majorized_coefficient_weighted_sum
#print axioms ZhangLS.Spec.lemma34_centered_weight_square
#print axioms ZhangLS.Spec.lemma34_centered_coefficient_energy
#print axioms ZhangLS.Spec.lemma34_actual_short_mean_bound
#print axioms ZhangLS.Spec.lemma34_centered_partial_sum_mean_square
#print axioms ZhangLS.Spec.lemma34_cutoff_le_P
#print axioms ZhangLS.Spec.lemma34_cutoff_nat_le_floor_P
#print axioms ZhangLS.Spec.lemma34_coefficient_log_bound
#print axioms ZhangLS.Spec.lemma34_uniform_centered_mean_square
#print axioms ZhangLS.Spec.lemma34_actual_x1_mean_square
#print axioms ZhangLS.Spec.lemma34_actual_x2_mean_square
#print axioms ZhangLS.Spec.lemma34_weighted_integral_cauchy
#print axioms ZhangLS.Spec.lemma34_partial_sum_measurable
#print axioms ZhangLS.Spec.lemma34_partial_sum_norm_bound
#print axioms ZhangLS.Spec.lemma34_two_partial_sums_weighted_integrable
#print axioms ZhangLS.Spec.lemma34_actual_partial_sums_weighted_integrable
#print axioms ZhangLS.Spec.lemma34_D_positive
#print axioms ZhangLS.Spec.lemma34_inverse_integral
#print axioms ZhangLS.Spec.lemma34_actual_sum_norms_square_mean
#print axioms ZhangLS.Spec.lemma34_actual_weighted_integral_cauchy
#print axioms ZhangLS.Spec.lemma34_actual_weighted_square_integral_mean
#print axioms ZhangLS.Spec.lemma34_actual_integral_mean_square
#print axioms ZhangLS.Spec.lemma34_actual_B_nonneg
#print axioms ZhangLS.Spec.lemma34_B_algebra_bound
#print axioms ZhangLS.Spec.lemma34_actual_B_mean_square
#print axioms ZhangLS.Spec.lemma34_mem_bad_family
#print axioms ZhangLS.Spec.lemma34_bad_count_times_threshold
#print axioms ZhangLS.Spec.lemma34_actual_bad_count
#print axioms ZhangLS.Spec.lemma34_proved
