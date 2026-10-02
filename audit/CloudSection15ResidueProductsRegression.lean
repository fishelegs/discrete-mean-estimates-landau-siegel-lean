import ZhangLS.Spec.Section15LeadingResidueBudget
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Filter
open scoped Topology

-- Actual source (15.16), retaining every analytic factor.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 3 → ℂ) (B : ℝ) (s : ℂ) :
    section15ActualIntegrand χ β B s=
      riemannZeta (1+s+β 0)*riemannZeta (1+s+β 1)/
        (riemannZeta (1+s)*dirichletLFunction χ (1+s))*
        ((B:ℂ)^(s+β 2)*lemma57OmegaOne D (s+β 2))/(s+β 2) := rfl

-- The star coefficient contains actual δ(1) and actual shifted L values.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 3 → ℂ) :
    section15ActualRStar χ β=
      dirichletLFunction χ (1+β 0)*dirichletLFunction χ (1+β 1)/LDerivAtOne χ*
        lemma54PaperDeltaMellin D 1 := rfl

-- The residue is defined from the actual meromorphic function.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 3 → ℂ) (B : ℝ) (j : Fin 3) :
    section15ActualR χ β B j=
      limUnder (𝓝[≠] (-β j)) (fun s => (s+β j)*section15ActualIntegrand χ β B s) := rfl

-- The retained original shifts satisfy the exact, necessary relation.
example (D : ℕ) (c : ℝ) :
    lemma52PaperBetaOne D c+lemma52PaperBetaTwo D c=lemma52PaperBetaThree D c := by
  linear_combination -(lemma153_beta_gap_one D c)

-- The geometric main values really are the source's three values.
example : lemma153LeadingWeight 0=1 ∧ lemma153LeadingWeight 1=2 ∧ lemma153LeadingWeight 2=1 := by
  norm_num [lemma153LeadingWeight]
  decide

-- Genuine L(1) was not replaced by zero.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D) : 0<realLAtOne χ := realLAtOne_pos χ hD

example {z : ℂ} (hz : ‖z-1‖≤1/4) : ‖zetaPoleRemoved z-1‖≤5*‖z-1‖ :=
  section15_zeta_regular_error hz

-- All original plus/minus shifts, under genuine (A), have the sharper rate.
example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hs : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10) (j : Fin 3) :
    ‖section15LFactor χ (-lemma83PaperBeta D c j)-1‖≤section15LRelativeConstant*lemma23PaperL D^(-6:ℤ) :=
  (section15_actual_beta_L_relative_error χ hDN hA hc hs j).2

-- All denominator nonzero conditions are discharged, rather than postulated.
example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold≤D) (hA : NormalizedAssumptionA χ)
    {c : ℝ} (hc : 0<c) (hs : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (hb : section15FactorConstant*lemma23PaperL D^(-6:ℤ)≤1/2) (j : Fin 3) :
    LDerivAtOne χ≠0 ∧ dirichletLFunction χ (1-lemma83PaperBeta D c j)≠0 ∧
      zetaPoleRemoved (1-lemma83PaperBeta D c j)≠0 :=
  section15_actual_denominators_nonzero χ hDN hA hc hs hb j

-- Explicit absolute rate for the actual-a weighted analytic/geometric difference.
example {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      ‖(lemma171MainTerm χ:ℂ)*(section15ActualRStar χ (lemma83PaperBeta D c)*
        section15ActualR χ (lemma83PaperBeta D c) (lemma61PaperP4 D) j-
          lemma153GeometricWeight D c j)‖≤
        (lemma32RegularProductBound (3/4)*(16*Real.exp 1)^2*(510*section15FactorConstant))*
          lemma23PaperL D^(-2:ℤ) := section15_actual_weighted_r_product_bridge hc

-- Stronger local conclusion after combining the frozen original phase geometry.
example {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      ‖(lemma171MainTerm χ:ℂ)*(section15ActualRStar χ (lemma83PaperBeta D c)*
        section15ActualR χ (lemma83PaperBeta D c) (lemma61PaperP4 D) j-
          lemma153LeadingWeight j)‖≤
        (lemma32RegularProductBound (3/4)*(16*Real.exp 1)^2*section15LeadingProductConstant c)*
          lemma23PaperL D^(-2:ℤ) := section15_actual_weighted_leading_residue_budget hc

-- Genuine nonzero simple poles for every original j, with no nonvanishing oracle.
example {c : ℝ} (hc : 0<c) :
    ∃ D₀ : ℕ, 3≤D₀ ∧ ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ j : Fin 3,
      section15ActualR χ (lemma83PaperBeta D c) (lemma61PaperP4 D) j≠0 := by
  obtain ⟨D₀,hD₀,hcert⟩ := section15_actual_simple_pole_certificates hc
  exact ⟨D₀,hD₀,fun D hD χ hA j => (hcert D hD χ hA j).2.2.1⟩

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma153_exp_imaginary_difference
#print axioms ZhangLS.Spec.lemma153_P4_log_difference
#print axioms ZhangLS.Spec.lemma153_P4_log_difference_bound
#print axioms ZhangLS.Spec.lemma153_alpha_logP
#print axioms ZhangLS.Spec.lemma153PhaseErrorConstant
#print axioms ZhangLS.Spec.lemma153_offset_P4_phase_error
#print axioms ZhangLS.Spec.lemma153_beta_gap_one
#print axioms ZhangLS.Spec.lemma153_beta_gap_two
#print axioms ZhangLS.Spec.lemma153_P4_cpow_imaginary
#print axioms ZhangLS.Spec.lemma153PhaseSign
#print axioms ZhangLS.Spec.lemma153_actual_P4_phase_bound
#print axioms ZhangLS.Spec.lemma153ShiftRatio
#print axioms ZhangLS.Spec.lemma153_actual_beta_factorization
#print axioms ZhangLS.Spec.lemma153_actual_shift_ratio_formula
#print axioms ZhangLS.Spec.lemma153LeadingWeight
#print axioms ZhangLS.Spec.lemma153LeadingSignedWeight
#print axioms ZhangLS.Spec.lemma153_real_ratio_bounds
#print axioms ZhangLS.Spec.lemma153_actual_shift_ratio_bounds
#print axioms ZhangLS.Spec.lemma153GeometricWeight
#print axioms ZhangLS.Spec.lemma153GeometricErrorConstant
#print axioms ZhangLS.Spec.lemma153_geometric_error_constant_pos
#print axioms ZhangLS.Spec.lemma153_phase_sign_norm
#print axioms ZhangLS.Spec.lemma153_weight_sign_identity
#print axioms ZhangLS.Spec.lemma153_actual_geometric_weight_bound
#print axioms ZhangLS.Spec.lemma153_actual_a_geometric_weight_budget
#print axioms ZhangLS.Spec.section15_zeta_regular_error
#print axioms ZhangLS.Spec.section15_ne_zero_of_near_one
#print axioms ZhangLS.Spec.section15_inverse_error
#print axioms ZhangLS.Spec.section15_derivative_lower
#print axioms ZhangLS.Spec.section15LFactor
#print axioms ZhangLS.Spec.section15LRelativeConstant
#print axioms ZhangLS.Spec.section15_l_relative_constant_pos
#print axioms ZhangLS.Spec.section15_actual_L_relative_error
#print axioms ZhangLS.Spec.section15_actual_beta_norm_lower
#print axioms ZhangLS.Spec.section15_actual_beta_L_relative_error
#print axioms ZhangLS.Spec.section15ActualIntegrand
#print axioms ZhangLS.Spec.section15RegularFactor
#print axioms ZhangLS.Spec.section15PoleNumerator
#print axioms ZhangLS.Spec.section15ActualR
#print axioms ZhangLS.Spec.section15ActualRStar
#print axioms ZhangLS.Spec.section15_cyclic_product
#print axioms ZhangLS.Spec.section15_integrand_regularization
#print axioms ZhangLS.Spec.section15_regular_factor_analytic
#print axioms ZhangLS.Spec.section15_pole_numerator_analytic
#print axioms ZhangLS.Spec.section15_actual_local_factorization
#print axioms ZhangLS.Spec.section15_actual_residue_limit
#print axioms ZhangLS.Spec.section15_actual_residue_formula
#print axioms ZhangLS.Spec.section15_alpha_le_L6
#print axioms ZhangLS.Spec.section15_alpha_logL_le_L6
#print axioms ZhangLS.Spec.section15_actual_delta_error_threshold
#print axioms ZhangLS.Spec.section15_omega_small_error
#print axioms ZhangLS.Spec.section15_actual_omega_error
#print axioms ZhangLS.Spec.section15_actual_zeta_factor_errors
#print axioms ZhangLS.Spec.section15_mul_error
#print axioms ZhangLS.Spec.section15_eight_factor_error
#print axioms ZhangLS.Spec.section15Correction
#print axioms ZhangLS.Spec.section15Geometric
#print axioms ZhangLS.Spec.section15_exact_residue_product
#print axioms ZhangLS.Spec.section15FactorConstant
#print axioms ZhangLS.Spec.section15_factor_constant_bounds
#print axioms ZhangLS.Spec.section15_actual_correction_error
#print axioms ZhangLS.Spec.section15_actual_shift_data
#print axioms ZhangLS.Spec.section15_actual_denominators_nonzero
#print axioms ZhangLS.Spec.section15_actual_geometric_eq
#print axioms ZhangLS.Spec.section15_actual_geometric_norm
#print axioms ZhangLS.Spec.section15_actual_r_product_error
#print axioms ZhangLS.Spec.section15_actual_a_L6_budget
#print axioms ZhangLS.Spec.section15_budget_threshold
#print axioms ZhangLS.Spec.section15_actual_weighted_r_product_bridge
#print axioms ZhangLS.Spec.section15_actual_small_circle_residue
#print axioms ZhangLS.Spec.section15_actual_geometric_nonzero
#print axioms ZhangLS.Spec.section15_actual_pole_nonzero
#print axioms ZhangLS.Spec.section15_actual_simple_pole_certificates
#print axioms ZhangLS.Spec.section15LeadingProductConstant
#print axioms ZhangLS.Spec.section15_leading_product_constant_pos
#print axioms ZhangLS.Spec.section15_alpha_logT_le_L6
#print axioms ZhangLS.Spec.section15_actual_r_product_leading_error
#print axioms ZhangLS.Spec.section15_actual_weighted_leading_residue_budget
