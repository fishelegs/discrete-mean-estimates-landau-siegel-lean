import ZhangLS.Spec.Lemma33

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology Classical

example (D : ℕ) (a : ℕ → ℂ) :
    (∑ ψ ∈ lemma33ActualFamily D,
      ‖∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D⌋₊,
        a n * ψ.2 (n : ZMod ψ.1.val)‖ ^ 2) ≤
      (∑ p : lemma33PrimeIndex D, (p.val : ℝ)) *
        ∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D⌋₊, ‖a n‖ ^ 2 :=
  lemma33_actual_first_mean_bound D a

example {D p : ℕ} (ψ : DirichletCharacter ℂ p)
    (hψ : p.Prime ∧ ψ.IsPrimitive ∧ lemma23PaperP D < (p : ℝ) ∧
      (p : ℝ) < lemma23PaperP D * (1 + lemma23PaperL D ^ (-68 : ℤ))) :
    p ∈ lemma33PrimeWindow D := lemma33_original_family_prime_mem ψ hψ

example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    ∀ (c : ℕ → ℂ) (s : ℂ),
      (∑ χ ∈ lemma33ActualFamily D, ‖∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D⌋₊,
        c n * χ.2 (n : ZMod χ.1.val) / (n : ℂ) ^ s‖ ^ 2) ≤
          C * (∑ p : lemma33PrimeIndex D, (p.val : ℝ)) *
            (∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D⌋₊, ‖c n‖ ^ 2 / (n : ℝ) ^ (2*s.re)) ∧
      (∑ χ ∈ lemma33ActualFamily D, ‖∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D ^ 2⌋₊,
        c n * χ.2 (n : ZMod χ.1.val) / (n : ℂ) ^ s‖ ^ 2) ≤
          C * lemma23PaperP D ^ 2 *
            (∑ n ∈ Finset.Icc 1 ⌊lemma23PaperP D ^ 2⌋₊, ‖c n‖ ^ 2 / (n : ℝ) ^ (2*s.re)) := by
  obtain ⟨C,hC,D₀,h⟩ := lemma33_proved
  refine ⟨C,hC,D₀,?_⟩
  intro D hD c s
  simpa only [lemma33ActualMean,lemma33ActualPrimeMass,
    lemma33_original_Dirichlet_sum_eq_actual] using h D hD c s

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma33_mem_prime_window
#print axioms ZhangLS.Spec.lemma33_prime_index_short_bound
#print axioms ZhangLS.Spec.lemma33_actual_first_mean_bound
#print axioms ZhangLS.Spec.lemma33_original_family_prime_mem
#print axioms ZhangLS.Spec.lemma33_actual_family_mem
#print axioms ZhangLS.Spec.lemma33_LSeries_term_norm_square
#print axioms ZhangLS.Spec.lemma33_actual_first_Dirichlet_mean_bound
#print axioms ZhangLS.Spec.lemma33_local_scalar_sampling
#print axioms ZhangLS.Spec.lemma33_norm_square_derivative
#print axioms ZhangLS.Spec.lemma33_norm_square_derivative_bound
#print axioms ZhangLS.Spec.lemma33_local_norm_square_sampling
#print axioms ZhangLS.Spec.lemma33_sampling_interval_sum_le
#print axioms ZhangLS.Spec.lemma33_separated_norm_square_sampling
#print axioms ZhangLS.Spec.lemma33_prime_fraction_cross_ne
#print axioms ZhangLS.Spec.lemma33_prime_fraction_separation
#print axioms ZhangLS.Spec.lemma33_fourier_interval_orthogonality
#print axioms ZhangLS.Spec.lemma33_trig_sum_continuous
#print axioms ZhangLS.Spec.lemma33_trig_sum_parseval
#print axioms ZhangLS.Spec.lemma33_trig_sum_hasDerivAt
#print axioms ZhangLS.Spec.lemma33_trig_sum_periodic
#print axioms ZhangLS.Spec.lemma33_trig_derivative_energy
#print axioms ZhangLS.Spec.lemma33_trig_derivative_energy_bound
#print axioms ZhangLS.Spec.lemma33_trig_square_integral_two_periods
#print axioms ZhangLS.Spec.lemma33_trig_square_energy_two_periods
#print axioms ZhangLS.Spec.lemma33_trig_derivative_two_period_bound
#print axioms ZhangLS.Spec.lemma33_primitive_nonprincipal
#print axioms ZhangLS.Spec.lemma33_prime_gauss_norm_square
#print axioms ZhangLS.Spec.lemma33_unit_character_mean_square_exact
#print axioms ZhangLS.Spec.lemma33_gauss_finite_transform
#print axioms ZhangLS.Spec.lemma33_gauss_finite_transform_norm_square
#print axioms ZhangLS.Spec.lemma33_unit_character_transform_parseval
#print axioms ZhangLS.Spec.lemma33_prime_primitive_mean_le_additive
#print axioms ZhangLS.Spec.lemma33_additive_large_sieve
#print axioms ZhangLS.Spec.lemma33_prime_window_modulus_bound
#print axioms ZhangLS.Spec.lemma33_sample_point_bounds
#print axioms ZhangLS.Spec.lemma33_actual_samples_separated
#print axioms ZhangLS.Spec.lemma33_additive_polynomial_eq_trig
#print axioms ZhangLS.Spec.lemma33_actual_mean_eq_prime_sum
#print axioms ZhangLS.Spec.lemma33_actual_mean_le_samples
#print axioms ZhangLS.Spec.lemma33_actual_second_mean_bound
#print axioms ZhangLS.Spec.lemma33_actual_second_Dirichlet_mean_bound
#print axioms ZhangLS.Spec.lemma33_parameters_at_threshold
#print axioms ZhangLS.Spec.lemma33_proved
#print axioms ZhangLS.Spec.lemma33_original_Dirichlet_sum_eq_actual
