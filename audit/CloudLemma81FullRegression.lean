import ZhangLS.Spec.Lemma81

open Complex ComplexConjugate Set
open scoped Classical
namespace ZhangLS.Spec

-- Literal unconditional target: no (A), real prime mass, outer conjugation,
-- bounds fixed before epsilon, all coefficients and actual branches.
example : ∃ c : ℝ, 0 < c ∧ Lemma52CompatibleConstant c ∧
    ∀ B₁ B₂ : ℝ, 0 < B₁ → 0 < B₂ → ∀ ε : ℝ, 0 < ε →
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
    ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ →
    Lemma81AdmissibleSequence D B₂ a₂ →
    ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
    (∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
    ‖lemma81DiscreteMean χ c Y a₁ a₂ - lemma81ThetaOne χ c a₁ a₂ -
      conj (lemma81ThetaOne χ c (lemma81ConjugateSequence a₂) (lemma81ConjugateSequence a₁))‖ ≤
      ε * lemma33ActualPrimeMass D := lemma81_proved

-- The enumerated zeros are actual L zeros in exactly (2.14).
example {D p : ℕ} [NeZero p] (ψ : DirichletCharacter ℂ p) (hψ : ψ ≠ 1) (ρ : ℂ) :
    ρ ∈ lemma81ZeroFinset D ψ ↔ Lemma23InZeroWindow D ρ ∧ ψ.LFunction ρ = 0 :=
  lemma81_mem_original_zero_finset ψ hψ ρ

-- Original strict upper height endpoint is excluded.
example (D : ℕ) (ρ : ℂ)
    (hρ : ρ.im = (lemma23PaperCenter D).im+lemma23PaperL D^405) :
    ¬Lemma81InZeroWindow D ρ := by
  intro hz
  have hh := hz.2
  rw [hρ,add_sub_cancel_left] at hh
  exact (not_lt_of_ge (le_abs_self _)) hh

-- Support remains strict at the original cutoff.
example {D : ℕ} {B : ℝ} {a : ℕ → ℂ} (ha : Lemma81AdmissibleSequence D B a)
    {n : ℕ} (hn : lemma81Cutoff D ≤ (n : ℝ)) : a n = 0 := ha.2 n hn

-- Conjugation retains exactly the same uniform coefficient bound and support.
example {D : ℕ} {B : ℝ} {a : ℕ → ℂ} (ha : Lemma81AdmissibleSequence D B a) :
    Lemma81AdmissibleSequence D B (lemma81ConjugateSequence a) :=
  lemma81_conjugate_sequence_admissible ha

-- Branch quantification is inhabited on the genuine good family.
example {D : ℕ} (χ : RealPrimitiveCharacter D) :
    ∃ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
      ∀ ψ ∈ lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ) :=
  lemma81_actual_family_branches_exist χ

-- Theta is its concrete J(1) contour definition.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    lemma81ThetaOne χ c a₁ a₂ =
      ∑ ψ ∈ lemma81GoodFamily χ, lemma81CIntegral D c ψ.2 a₁ a₂ 1 := rfl

-- Actual residues retain the genuine coefficient, including M-prime.
example {D p : ℕ} [NeZero p] (c : ℝ) (ψ : DirichletCharacter ℂ p)
    (Y : ℂ → ℂ) (a₁ a₂ : ℕ → ℂ) (ρ : ℂ) :
    lemma81ActualResidueWeight D c ψ Y a₁ a₂ ρ =
      lemma23ActualCoefficient ψ Y D c ρ*lemma81Polynomial D a₁ ψ ρ*
        lemma81Polynomial D a₂ ψ⁻¹ (1-ρ)*lemma81Omega D ρ := rfl

-- The rectangle orientation and vertical normalization agree exactly.
example : (2*(Real.pi : ℂ)*I)⁻¹*I = ((2*Real.pi : ℝ) : ℂ)⁻¹ :=
  lemma81_rectangle_normalization_vertical

end ZhangLS.Spec

#print ZhangLS.Spec.Lemma81Target
#print axioms ZhangLS.Spec.lemma81_mem_good_family
#print axioms ZhangLS.Spec.lemma81_zero_window_subset_container
#print axioms ZhangLS.Spec.lemma81_container_divisor_eq_order
#print axioms ZhangLS.Spec.lemma81_mem_container_zero_finset
#print axioms ZhangLS.Spec.lemma81_mem_zero_finset
#print axioms ZhangLS.Spec.lemma81_conjugate_sequence_admissible
#print axioms ZhangLS.Spec.lemma81_polynomial_conjugate
#print axioms ZhangLS.Spec.lemma81_center_reflection
#print axioms ZhangLS.Spec.lemma81_omega_reflection
#print axioms ZhangLS.Spec.lemma81_polynomial_weight_reflection
#print axioms ZhangLS.Spec.lemma81_actual_zero_set_finite
#print axioms ZhangLS.Spec.lemma81_segment_point_reflection
#print axioms ZhangLS.Spec.lemma81_normalized_segment_conjugation
#print axioms ZhangLS.Spec.lemma81_inverse_Z_norm_bound
#print axioms ZhangLS.Spec.lemma81_right_segment_zero_separation
#print axioms ZhangLS.Spec.lemma81_Ctilde_eq_C_mul_relative_error
#print axioms ZhangLS.Spec.lemma81_uniform_actual_kernel_replacement
#print axioms ZhangLS.Spec.lemma81_zero_window_iff_original
#print axioms ZhangLS.Spec.lemma81_mem_original_zero_finset
#print axioms ZhangLS.Spec.lemma81_actual_family_branches_exist
#print axioms ZhangLS.Spec.lemma81_multichoose_two_square_le_four
#print axioms ZhangLS.Spec.lemma81_tau_two_square_le_tau_four
#print axioms ZhangLS.Spec.lemma81_tau_two_square_harmonic_sum
#print axioms ZhangLS.Spec.lemma81_tuple_count_le_tau
#print axioms ZhangLS.Spec.lemma81_tuple_coefficient_norm_le
#print axioms ZhangLS.Spec.lemma81_tuple_coefficient_zero_of_large
#print axioms ZhangLS.Spec.lemma81_actual_polynomial_square_expansion
#print axioms ZhangLS.Spec.lemma81_thin_strip_exponential_weight
#print axioms ZhangLS.Spec.lemma81_convolution_coefficient_energy
#print axioms ZhangLS.Spec.lemma81_fourth_moment_constant_pos
#print axioms ZhangLS.Spec.lemma81_actual_polynomial_fourth_moment
#print axioms ZhangLS.Spec.lemma81_cutoff_le_P
#print axioms ZhangLS.Spec.lemma81_finite_character_polynomial_eq_cpow_sum
#print axioms ZhangLS.Spec.lemma81_actual_polynomial_eq_prefix
#print axioms ZhangLS.Spec.lemma81_conjugate_sequence_involutive
#print axioms ZhangLS.Spec.lemma81_actual_A_fourth_moment
#print axioms ZhangLS.Spec.lemma81_product_moment_of_fourth
#print axioms ZhangLS.Spec.lemma81_actual_A_inverse_fourth_moment
#print axioms ZhangLS.Spec.lemma81_actual_A_product_second_moment
#print axioms ZhangLS.Spec.lemma81_T_log_le_square
#print axioms ZhangLS.Spec.lemma81_three_T_cube_le_P
#print axioms ZhangLS.Spec.lemma81_T_inverse_square_le_exp_neg_log
#print axioms ZhangLS.Spec.lemma81_uniform_six_one_lengths
#print axioms ZhangLS.Spec.lemma81_finite_character_polynomial_conjugate
#print axioms ZhangLS.Spec.lemma81_actual_inverse_polynomial_fourth_moment
#print axioms ZhangLS.Spec.lemma81_weighted_polynomial_eq_actual_prefix
#print axioms ZhangLS.Spec.lemma81_weighted_polynomial_fourth_moment
#print axioms ZhangLS.Spec.lemma81_inverse_weighted_polynomial_fourth_moment
#print axioms ZhangLS.Spec.lemma81_short_cutoff_coefficient_norm
#print axioms ZhangLS.Spec.lemma81_short_polynomial_eq_actual_prefix
#print axioms ZhangLS.Spec.lemma81_short_polynomial_fourth_moment
#print axioms ZhangLS.Spec.lemma81_uniform_six_one_polynomial_moments
#print axioms ZhangLS.Spec.lemma81_interval_cauchy_square
#print axioms ZhangLS.Spec.lemma81_interval_fourth_power
#print axioms ZhangLS.Spec.lemma81_finite_family_integral_fourth
#print axioms ZhangLS.Spec.lemma81_uniform_actual_E1_fourth_moment
#print axioms ZhangLS.Spec.lemma81_three_term_fourth_bound
#print axioms ZhangLS.Spec.lemma81_uniform_actual_L_fourth_moment
#print axioms ZhangLS.Spec.lemma81_uniform_actual_shifted_L_product_moment
#print axioms ZhangLS.Spec.lemma81_omega_segment_norm
#print axioms ZhangLS.Spec.lemma81_omega_norm_density
#print axioms ZhangLS.Spec.lemma81_gaussian_density_integrable
#print axioms ZhangLS.Spec.lemma81_gaussian_density_mass
#print axioms ZhangLS.Spec.lemma81_actual_finite_gaussian_mass
#print axioms ZhangLS.Spec.lemma81_analytic_critical_reflection
#print axioms ZhangLS.Spec.lemma81_actual_M_analytic
#print axioms ZhangLS.Spec.lemma81_actual_M_critical_real
#print axioms ZhangLS.Spec.lemma81_actual_M_reflection
#print axioms ZhangLS.Spec.lemma81_actual_normalized_quotient_reflection
#print axioms ZhangLS.Spec.lemma81_Ctilde_reflection_of_domain
#print axioms ZhangLS.Spec.lemma81_uniform_Ctilde_reflection
#print axioms ZhangLS.Spec.lemma81_right_segment_point_in_region
#print axioms ZhangLS.Spec.lemma81_uniform_reflected_contour_identity
#print axioms ZhangLS.Spec.lemma81_polynomial_differentiable
#print axioms ZhangLS.Spec.lemma81_omega_differentiable
#print axioms ZhangLS.Spec.lemma81_tilde_integrand_eq_numerator_div
#print axioms ZhangLS.Spec.lemma81_actual_tilde_numerator_analyticAt
#print axioms ZhangLS.Spec.lemma81_actual_tilde_integrand_analyticAt
#print axioms ZhangLS.Spec.lemma81_actual_C_analyticAt
#print axioms ZhangLS.Spec.lemma81_right_point_mem_segment
#print axioms ZhangLS.Spec.lemma81_uniform_right_contour_regular_data
#print axioms ZhangLS.Spec.lemma81_actual_C_integrand_analyticAt
#print axioms ZhangLS.Spec.lemma81_uniform_actual_contour_integrability
#print axioms ZhangLS.Spec.lemma81_integrand_difference_factor
#print axioms ZhangLS.Spec.lemma81_uniform_aggregate_replacement_pointwise
#print axioms ZhangLS.Spec.lemma81_normalization_factor_norm_le_one
#print axioms ZhangLS.Spec.lemma81_normalized_family_error_bound
#print axioms ZhangLS.Spec.lemma81_uniform_aggregate_replacement_integral
#print axioms ZhangLS.Spec.lemma81_ThetaOne_eq_sum_CIntegral
#print axioms ZhangLS.Spec.lemma81_actual_replacement_littleO
#print axioms ZhangLS.Spec.lemma81_wide_strip_parameters
#print axioms ZhangLS.Spec.lemma81_actual_L_coarse_exponential
#print axioms ZhangLS.Spec.lemma81_inverse_Z_coarse_exponential
#print axioms ZhangLS.Spec.lemma81_section_log_hundred
#print axioms ZhangLS.Spec.lemma81_wide_shift_path_near_center
#print axioms ZhangLS.Spec.lemma81_uniform_wide_actual_quotient
#print axioms ZhangLS.Spec.lemma81_actual_phase_norm_one
#print axioms ZhangLS.Spec.lemma81_uniform_wide_actual_C_growth
#print axioms ZhangLS.Spec.lemma81_boundary_growth_constant_pos
#print axioms ZhangLS.Spec.lemma81_uniform_thin_actual_Ctilde_growth
#print axioms ZhangLS.Spec.lemma81_actual_A_coarse_bound
#print axioms ZhangLS.Spec.lemma81_actual_A_product_coarse_bound
#print axioms ZhangLS.Spec.lemma81_actual_good_family_card_le_mass
#print axioms ZhangLS.Spec.lemma81_gaussian_boundary_decay
#print axioms ZhangLS.Spec.lemma81_gaussian_boundary_decay_at
#print axioms ZhangLS.Spec.lemma81_uniform_boundary_envelope_small
#print axioms ZhangLS.Spec.lemma81_boundary_integrand_envelope
#print axioms ZhangLS.Spec.lemma81_uniform_actual_boundary_integrands_small
#print axioms ZhangLS.Spec.lemma81_separated_upper_cut
#print axioms ZhangLS.Spec.lemma81_separated_lower_cut
#print axioms ZhangLS.Spec.lemma81_closed_rectangle_height
#print axioms ZhangLS.Spec.lemma81_uniform_actual_rectangle_boundaries
#print axioms ZhangLS.Spec.lemma81_analyticAt_dslope_same
#print axioms ZhangLS.Spec.lemma81_simple_pole_regular_part_analytic
#print axioms ZhangLS.Spec.lemma81_simple_zero_div_eq
#print axioms ZhangLS.Spec.lemma81_simple_zero_principal_part
#print axioms ZhangLS.Spec.lemma81_simple_zero_residue_tendsto
#print axioms ZhangLS.Spec.lemma81_actual_numerator_div_deriv
#print axioms ZhangLS.Spec.lemma81_uniform_actual_simple_zero_residues
#print axioms ZhangLS.Spec.lemma81_finite_pole_remainder_off_set
#print axioms ZhangLS.Spec.lemma81_finite_pole_remainder_at_pole
#print axioms ZhangLS.Spec.lemma81_principal_sum_analyticAt
#print axioms ZhangLS.Spec.lemma81_finite_pole_remainder_analyticOnNhd
#print axioms ZhangLS.Spec.lemma81_rectangle_cauchy
#print axioms ZhangLS.Spec.lemma81_horizontal_inverse_continuous
#print axioms ZhangLS.Spec.lemma81_vertical_inverse_continuous
#print axioms ZhangLS.Spec.lemma81_rectangle_inverse_split_real
#print axioms ZhangLS.Spec.lemma81_rectangle_inverse_split_im
#print axioms ZhangLS.Spec.lemma81_rectangle_inverse_winding_symmetric
#print axioms ZhangLS.Spec.lemma81_rectangle_inverse_winding
#print axioms ZhangLS.Spec.lemma81_rectangle_reciprocal_translate
#print axioms ZhangLS.Spec.lemma81_rectangle_simple_pole_winding
#print axioms ZhangLS.Spec.lemma81_finite_pole_edge_integral
#print axioms ZhangLS.Spec.lemma81_finite_rectangle_residue_theorem
#print axioms ZhangLS.Spec.lemma81_closed_rectangle_iff
#print axioms ZhangLS.Spec.lemma81_open_rectangle_iff
#print axioms ZhangLS.Spec.lemma81_closed_not_open_is_boundary
#print axioms ZhangLS.Spec.lemma81_actual_rectangle_residue_identity
#print axioms ZhangLS.Spec.lemma81_uniform_extended_contour_separation
#print axioms ZhangLS.Spec.lemma81_zero_separated_quarter_of_one
#print axioms ZhangLS.Spec.lemma81_normalized_segment_eq_vertical
#print axioms ZhangLS.Spec.lemma81_rectangle_vertical_difference_bound
#print axioms ZhangLS.Spec.lemma81_uniform_actual_C_shift_pointwise
#print axioms ZhangLS.Spec.lemma81_actual_C_shift_littleO
#print axioms ZhangLS.Spec.lemma81_height_band_of_near_endpoint
#print axioms ZhangLS.Spec.lemma81_height_of_mem_uIcc
#print axioms ZhangLS.Spec.lemma81_integral_height_change_bound
#print axioms ZhangLS.Spec.lemma81_uniform_extended_vertical_integrability
#print axioms ZhangLS.Spec.lemma81_rectangle_normalization_vertical
#print axioms ZhangLS.Spec.lemma81_rectangle_normalization_norm_le_one
#print axioms ZhangLS.Spec.lemma81_rectangle_truncation_bound
#print axioms ZhangLS.Spec.lemma81_uniform_actual_residue_to_segments
#print axioms ZhangLS.Spec.lemma81_actual_residue_deformation_littleO
#print axioms ZhangLS.Spec.lemma81_actual_right_contour_littleO
#print axioms ZhangLS.Spec.lemma81_proved
