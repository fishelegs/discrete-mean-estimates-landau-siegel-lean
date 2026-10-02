import ZhangLS.Spec.Lemma59

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

example (c η : ℝ) (hc : 0 < c) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p]
      (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ {s : ℂ},
    |s.re - 1 / 2| ≤ lemma44PaperAlpha D →
    |s.im - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 10 →
    (∀ ρ : ℂ, DirichletCharacter.LFunction ψ ρ = 0 → η * lemma44PaperAlpha D ≤ ‖s - ρ‖) →
    ‖DirichletCharacter.LFunction ψ (s + I * (lemma23PaperOffsetOne D c : ℂ)) /
      DirichletCharacter.LFunction ψ s‖ ≤ C * Real.log (lemma23PaperP D) := by
  obtain ⟨C,hC,D₀,h⟩ := lemma59_proved c hc η hη
  refine ⟨C,hC,D₀,?_⟩
  intro D p _ χ ψ hD hψ s hre him hsep
  exact h χ ψ hD hψ ⟨hre,him⟩ hsep

example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {C : ℝ} {D₀ : ℕ} {c η : ℝ}
    (h : ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ {s : ℂ}, Lemma59InRegion D s →
      Lemma59ZeroSeparated (D := D) ψ s η →
      ‖DirichletCharacter.LFunction ψ (s + I * (lemma23PaperOffsetOne D c : ℂ)) /
        DirichletCharacter.LFunction ψ s‖ ≤ C * Real.log (lemma23PaperP D))
    (hD : D₀ ≤ D) (hL : 100 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hre : s.re = 1 / 2 + lemma44PaperAlpha D)
    (him : s.im = (lemma23PaperCenter D).im + (lemma23PaperL D ^ 405 + 10))
    (hsep : Lemma59ZeroSeparated (D := D) ψ s η) :
    ‖DirichletCharacter.LFunction ψ (s + I * (lemma23PaperOffsetOne D c : ℂ)) /
      DirichletCharacter.LFunction ψ s‖ ≤ C * Real.log (lemma23PaperP D) := by
  apply h χ ψ hD hψ _ hsep
  have ha := (lemma59_alpha_bounds hL).1
  have hp : 0 ≤ lemma23PaperL D ^ 405 + 10 := by positivity
  constructor
  · rw [hre,add_sub_cancel_left,abs_of_nonneg ha.le]
  · rw [him,add_sub_cancel_left,abs_of_nonneg hp]

example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    {C : ℝ} {D₀ : ℕ} {c η : ℝ}
    (h : ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ {s : ℂ}, Lemma59InRegion D s →
      Lemma59ZeroSeparated (D := D) ψ s η →
      ‖DirichletCharacter.LFunction ψ (s + I * (lemma23PaperOffsetOne D c : ℂ)) /
        DirichletCharacter.LFunction ψ s‖ ≤ C * Real.log (lemma23PaperP D))
    (hD : D₀ ≤ D) (hL : 100 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hre : s.re = 1 / 2 - lemma44PaperAlpha D)
    (him : s.im = (lemma23PaperCenter D).im - (lemma23PaperL D ^ 405 + 10))
    (hsep : Lemma59ZeroSeparated (D := D) ψ s η) :
    ‖DirichletCharacter.LFunction ψ (s + I * (lemma23PaperOffsetOne D c : ℂ)) /
      DirichletCharacter.LFunction ψ s‖ ≤ C * Real.log (lemma23PaperP D) := by
  apply h χ ψ hD hψ _ hsep
  have ha := (lemma59_alpha_bounds hL).1
  have hp : 0 ≤ lemma23PaperL D ^ 405 + 10 := by positivity
  constructor
  · rw [hre,sub_sub_cancel_left,abs_neg,abs_of_nonneg ha.le]
  · rw [him,sub_sub_cancel_left,abs_neg,abs_of_nonneg hp]


#print axioms lemma59_extended_height_margin
#print axioms lemma59_ext44_gamma_region_height
#print axioms lemma59_ext44_middle_reflected_displacement
#print axioms lemma59_ext44_omega3_displacement
#print axioms lemma59_ext44_omega3_re_pos
#print axioms lemma59_ext44_omega3_subset_extended_gamma_region
#print axioms lemma59_ext44_right_mellin_gaussian_bound
#print axioms lemma59_ext44_truncated_shift_in_extended_gamma_region
#print axioms lemma59_ext44ActualZtilde_norm_on_omega3
#print axioms lemma59_ext44_equation46
#print axioms lemma59_ext44_gaussian_long_sum_on_omega3
#print axioms lemma59_ext44_initial_left_denominator_bound
#print axioms lemma59_ext44_initial_left_shift_abs_re
#print axioms lemma59_ext44_left_product_mellin_eq_reflected_series
#print axioms lemma59_ext44_long_sum_on_omega3
#print axioms lemma59_ext44_middle_Z_norm_bound
#print axioms lemma59_ext44_middle_integrable
#print axioms lemma59_ext44_product_finite_shift
#print axioms lemma59_ext44_product_horizontal_point_bound
#print axioms lemma59_ext44_reflected_horizontal_point_bound
#print axioms lemma59_ext44_reflected_long_sum_bound
#print axioms lemma59_ext44_reflected_numerator_rectangle_differentiable
#print axioms lemma59_ext44_reflected_polynomial_intervalIntegrable
#print axioms lemma59_ext44_right_vertical_truncation_bound
#print axioms lemma59_ext44_short_right_point_bound
#print axioms lemma59_ext44_initial_left_gamma_region
#print axioms lemma59_ext44_initial_left_omega_bound
#print axioms lemma59_ext44_long_horizontal_point_bound
#print axioms lemma59_ext44_middle_product_bound
#print axioms lemma59_ext44_paper_gaussian_long_sum_on_omega3
#print axioms lemma59_ext44_product_horizontal_error_bound
#print axioms lemma59_ext44_reflected_polynomial_middle_shift
#print axioms lemma59_ext44_reflected_polynomial_residue_shift
#print axioms lemma59_ext44_short_horizontal_point_bound
#print axioms lemma59_ext44_short_right_contour_bound
#print axioms lemma59_ext44_full_gaussian_series_approximation
#print axioms lemma59_ext44_initial_left_Z_scale_bound
#print axioms lemma59_ext44_long_horizontal_error_bound
#print axioms lemma59_ext44_middle_integrand_norm_bound
#print axioms lemma59_ext44_reflected_tail_contour_continuousOn
#print axioms lemma59_ext44_short_horizontal_error_bound
#print axioms lemma59_ext44_reflected_tail_contour_intervalIntegrable
#print axioms lemma59_ext44_reflected_tail_contour_pointwise_bound
#print axioms lemma59_ext44_right_mellin_approximation
#print axioms lemma59_ext44_truncated_middle_contour_bound
#print axioms lemma59_ext44_left_product_contour_decomposition
#print axioms lemma59_ext44_middle_reflected_polynomial_bound
#print axioms lemma59_ext44_reflected_tail_contour_bound
#print axioms lemma59_ext44_actual_approximate_functional_equation
#print axioms lemma59_ext44_uniform_error_constant
#print axioms lemma59_ext_good_FG_bound
#print axioms lemma59_ext_good_product_bound
#print axioms lemma59_ext_F_logDeriv_at_threshold
#print axioms lemma59_ext45_horizontal_F_quotient_bound
#print axioms lemma59_ext45_omega1_F_inv_bound
#print axioms lemma59_ext45_equation410
#print axioms lemma59_ext45_region_subsets
#print axioms lemma59_ext46_disk_subset_local_strip
#print axioms lemma59_ext46_local_strip_regions
#print axioms lemma59_ext48_omega_height_pos
#print axioms lemma59_ext48_omega_reflection
#print axioms lemma59_ext48_thin_slab_regions
#print axioms lemma59_ext45_B_bound_far
#print axioms lemma59_ext45_B_bound_near
#print axioms lemma59_ext46_actual_A_reflected_zero
#print axioms lemma59_ext46_actual_B_differentiable_ne_zero
#print axioms lemma59_ext46_equation411
#print axioms lemma59_ext46_inner_disk_regions
#print axioms lemma59_ext45_B_uniform_gap
#print axioms lemma59_ext46_actual_A_analyticOn_inner_disk
#print axioms lemma59_ext46_actual_model_approximation_closed
#print axioms lemma59_ext45_actual_A_lower_bound
#print axioms lemma59_ext46_actual_model_approximation
#print axioms lemma59_ext46_actual_rouche_count_one_closed
#print axioms lemma59_ext45_actual_A_ne_zero
#print axioms lemma59_ext46_actual_rouche_count_one
#print axioms lemma59_ext46_zero_analysis_at_contraction_closed
#print axioms lemma59_ext45_actual_product_ne_zero
#print axioms lemma59_ext46_zero_analysis_at_contraction
#print axioms lemma59_ext46_proved
#print axioms lemma59_ext48_actual_zero_in_thin_slab
#print axioms lemma59_ext48_actual_Z_inv_bound
#print axioms lemma59_ext_prop22_actual_zero_analysis
#print axioms lemma59_ext48_actual_inverse_factor_approximation
#print axioms lemma59_ext48_at_explicit_constant
#print axioms lemma59_ext48_proved
#print axioms lemma59_uniform_extended_actual_product_zeros
#print axioms lemma59_actual_L_simple_of_product_simple
#print axioms lemma59_uniform_actual_local_zero_structure
#print axioms lemma59_critical_line_norm_eq_im_distance
#print axioms lemma59_relaxed_rank_scalar
#print axioms lemma59_relaxed_ranked_zero_product_bound
#print axioms lemma59_exceptional_zero_product_bound_three
#print axioms lemma59_ordered_separated_rank
#print axioms lemma59_near_real_zero_card_le_three
#print axioms lemma59_sorted_real_zero_product_bound
#print axioms lemma59_zero_line_distance
#print axioms lemma59_zero_ordinate_injective
#print axioms lemma59_neg_zero_ordinate_injective
#print axioms lemma59_harmonic_le_log_succ
#print axioms lemma59_far_complex_zero_product_bound
#print axioms lemma59_near_complex_zero_card_le_three
#print axioms lemma59_log_succ_product_budget_mono
#print axioms lemma59_separated_complex_zero_product_bound
#print axioms lemma59_log_zero_count_budget
#print axioms lemma59_relaxed_scale_shift_budget
#print axioms lemma59_uniform_relaxed_product_budget
#print axioms lemma59_proved
end ZhangLS.Spec
