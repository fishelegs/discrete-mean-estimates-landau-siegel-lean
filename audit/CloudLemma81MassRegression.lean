import ZhangLS.Spec.Lemma81PrimeMassAbsorption


namespace ZhangLS.Spec
example : ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    1 < D ∧ 2000 ≤ Real.log (D : ℝ) ∧
    ∀ ρ : ℂ, ρ ≠ 1 → 1 - 1 / (10000000 * Real.log (D : ℝ)) < ρ.re →
      |ρ.im| ≤ D → riemannZeta ρ ≠ 0 :=
  lemma81_uniform_zeta_thin_strip

example : ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    1 < D ∧ 2000 ≤ Real.log (D : ℝ) ∧
    ∀ ρ : ℂ, 1 - 1 / (10000000 * Real.log (D : ℝ)) < ρ.re →
      |ρ.im| ≤ D → zetaPoleRemoved ρ ≠ 0 :=
  lemma81_uniform_zeta_pole_removed_thin_strip

example : ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
    (1 / 4 : ℝ) * lemma23PaperP D ^ 2 / lemma23PaperL D ^ 77 ≤ lemma33ActualPrimeMass D :=
  lemma81_uniform_actual_prime_mass_lower_original

example (C : ℝ) (hC : 0 ≤ C) (ε : ℝ) (hε : 0 < ε) :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D →
      C * lemma23PaperP D ^ 2 * lemma23PaperL D ^ (-78 : ℤ) ≤
        ε * lemma33ActualPrimeMass D :=
  lemma81_uniform_prime_mass_error_absorption C hC ε hε
end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma81_three_four_one_phase_nonneg
#print axioms ZhangLS.Spec.lemma81_three_four_one_mangoldt_term_nonneg
#print axioms ZhangLS.Spec.lemma81_zeta_three_four_one_logDeriv_nonpos
#print axioms ZhangLS.Spec.lemma81_zeta_local_zero_term_re_nonneg
#print axioms ZhangLS.Spec.lemma81_zeta_logDeriv_re_lower_sum
#print axioms ZhangLS.Spec.lemma81_zeta_logDeriv_re_lower
#print axioms ZhangLS.Spec.lemma81_zeta_logDeriv_re_lower_retaining_zero
#print axioms ZhangLS.Spec.lemma81_zeta_pole_re_le_one
#print axioms ZhangLS.Spec.lemma81_zeta_three_four_one_zero_inequality
#print axioms ZhangLS.Spec.lemma81_zeta_high_thin_strip
#print axioms ZhangLS.Spec.lemma81_zeta_removed_ne_zero_of_one_le_re
#print axioms ZhangLS.Spec.lemma81_zeta_low_height_collar
#print axioms ZhangLS.Spec.lemma81_uniform_zeta_pole_removed_thin_strip
#print axioms ZhangLS.Spec.lemma81_uniform_zeta_thin_strip
#print axioms ZhangLS.Spec.lemma81_zeta_contour_delta
#print axioms ZhangLS.Spec.lemma81_zeta_removed_paper_rectangle_bound
#print axioms ZhangLS.Spec.lemma81_zeta_logDeriv_norm_from_removed
#print axioms ZhangLS.Spec.lemma81_zeta_paper_left_bound
#print axioms ZhangLS.Spec.lemma81_zeta_paper_horizontal_bound
#print axioms ZhangLS.Spec.lemma81_principal_perron_smoothed_main_error_of_strip
#print axioms ZhangLS.Spec.lemma81_principal_mass_moment_budget
#print axioms ZhangLS.Spec.lemma81_principal_mass_left_power
#print axioms ZhangLS.Spec.lemma81_principal_mass_left_budget
#print axioms ZhangLS.Spec.lemma81_principal_mass_horizontal_budget
#print axioms ZhangLS.Spec.lemma81_principal_mass_error_constant_pos
#print axioms ZhangLS.Spec.lemma81_principal_mass_main_error_budget
#print axioms ZhangLS.Spec.lemma81_principal_mass_polynomial_absorption
#print axioms ZhangLS.Spec.lemma81_uniform_principal_smoothed_mass_main_error
#print axioms ZhangLS.Spec.lemma81_principal_sharp_prime_error_constant_pos
#print axioms ZhangLS.Spec.lemma81_uniform_principal_sharp_prime_mass_main_error
#print axioms ZhangLS.Spec.lemma81_uniform_actual_prime_mass_threshold
#print axioms ZhangLS.Spec.lemma81_uniform_actual_prime_log_mass_lower
#print axioms ZhangLS.Spec.lemma81_uniform_actual_prime_mass_lower
#print axioms ZhangLS.Spec.lemma81_uniform_actual_prime_mass_lower_original
#print axioms ZhangLS.Spec.lemma81_prime_mass_error_absorption_of_lower
#print axioms ZhangLS.Spec.lemma81_uniform_prime_mass_error_absorption
