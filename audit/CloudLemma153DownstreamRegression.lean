import ZhangLS.Spec.Lemma153DownstreamMainTerm
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

-- The kernel is the paper's actual T and Gaussian, with no replacement scale.
example (D : ℕ) (w : ℂ) :
    lemma171GaussianMellinFactor D w =
      (lemma56PaperT D:ℂ)^w * Complex.exp (w^2/(4*(Real.log (D:ℝ):ℂ)^30)) := by
  simpa only [lemma57OmegaOne] using lemma171_gaussian_factor_eq_paper D w

-- The L argument is shifted in the genuine repaired integrand.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ w : ℂ) :
    lemma153MellinIntegrand χ β γ w =
      lemma153EulerProduct χ β γ (1+w)*riemannZeta (1+w)^2*
        dirichletLFunction χ (1+w-γ)^2*
        ((lemma56PaperT D:ℂ)^w*lemma57OmegaOne D w)/w := by
  rw [lemma153MellinIntegrand,lemma171_gaussian_factor_eq_paper]

-- The exact unshifted special case retains L(1), not an assumed zero there.
example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1<D)
    (β : Fin 2 → ℂ) (hpar : Lemma153SmallParameters β 0) :
    lemma153ActualResidue χ β 0 = lemma153EulerProduct χ β 0 1*LDerivAtOne χ^2+
      LAtOne χ*(lemma153EulerProduct χ β 0 1*iteratedDeriv 2 (dirichletLFunction χ) 1+
        2*deriv (lemma153ResiduePrefactor χ β 0) 0*LDerivAtOne χ+
        iteratedDeriv 2 (lemma153ResiduePrefactor χ β 0) 0*LAtOne χ/2) := by
  simpa only [sub_zero,LAtOne,LDerivAtOne] using
    lemma153_actual_residue_decomposition χ hD β 0 hpar

-- All three original shifts, the actual M normalization and actual a survive
-- in the local residue statement; there is no finite-sum premise or conclusion.
example : ∃ C : ℝ, 0<C ∧ ∀ c : ℝ, 0<c → ∃ D₀ : ℕ, 3≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ j : Fin 3,
      ‖lemma153GeneralMEulerProduct χ (lemma152PaperBeta D c) 1 1 (1-lemma83PaperBeta D c j)*
          lemma153ActualResidue χ (lemma152PaperBeta D c) (lemma83PaperBeta D c j)-
        (lemma171MainTerm χ:ℂ)*((Nat.totient D:ℂ)/(D:ℂ))‖≤
          C*lemma23PaperL D^(-3:ℤ) := by
  exact ⟨lemma153NormalizedResidueErrorConstant,lemma153_normalized_residue_error_constant_pos,
    fun _ hc => lemma153_paper_normalized_actual_residue hc⟩

end ZhangLS.Spec

#print axioms ZhangLS.Spec.lemma153MellinIntegrand
#print axioms ZhangLS.Spec.lemma153_mellin_integrand_eq_actual_series
#print axioms ZhangLS.Spec.lemma153ResiduePrefactor
#print axioms ZhangLS.Spec.lemma153_residue_prefactor_differentiableAt
#print axioms ZhangLS.Spec.lemma153_residue_prefactor_analyticAt
#print axioms ZhangLS.Spec.lemma153_residue_prefactor_zero
#print axioms ZhangLS.Spec.lemma153RegularNumerator
#print axioms ZhangLS.Spec.lemma153_regular_numerator_differentiableAt
#print axioms ZhangLS.Spec.lemma153_regular_numerator_eq
#print axioms ZhangLS.Spec.lemma153ActualResidue
#print axioms ZhangLS.Spec.lemma153_actual_circle_integral_eq_residue
#print axioms ZhangLS.Spec.lemma153_actual_residue_decomposition
#print axioms ZhangLS.Spec.lemma153ResidueRadius
#print axioms ZhangLS.Spec.lemma153LocalUBound
#print axioms ZhangLS.Spec.lemma153LocalPrefactorBound
#print axioms ZhangLS.Spec.lemma153_residue_radius_properties
#print axioms ZhangLS.Spec.lemma153_local_U_bound_nonneg
#print axioms ZhangLS.Spec.lemma153_local_prefactor_bound_nonneg
#print axioms ZhangLS.Spec.lemma153_U_bound_le_prefactor_bound
#print axioms ZhangLS.Spec.lemma153_gaussian_factor_residue_bound
#print axioms ZhangLS.Spec.lemma153_actual_U_local_bound
#print axioms ZhangLS.Spec.lemma153_actual_prefactor_local_bound
#print axioms ZhangLS.Spec.lemma153_actual_prefactor_diffContOnCl
#print axioms ZhangLS.Spec.lemma153_actual_prefactor_first_derivative_bound
#print axioms ZhangLS.Spec.lemma153_actual_prefactor_second_derivative_bound
#print axioms ZhangLS.Spec.lemma153_actual_shifted_residue_error_bound
#print axioms ZhangLS.Spec.lemma153ShiftedValueConstant
#print axioms ZhangLS.Spec.lemma153ResidueBracketConstant
#print axioms ZhangLS.Spec.lemma153ResidueRateConstant
#print axioms ZhangLS.Spec.lemma153_shifted_value_constant_pos
#print axioms ZhangLS.Spec.lemma153_residue_bracket_constant_pos
#print axioms ZhangLS.Spec.lemma153_residue_rate_constant_pos
#print axioms ZhangLS.Spec.lemma153_shifted_value_scale
#print axioms ZhangLS.Spec.lemma153_residue_bracket_scale
#print axioms ZhangLS.Spec.lemma153_actual_shifted_residue_rate
#print axioms ZhangLS.Spec.lemma153_log_power_eventual_absorption
#print axioms ZhangLS.Spec.lemma153_paper_log_absorption_threshold
#print axioms ZhangLS.Spec.lemma153PaperResidueErrorConstant
#print axioms ZhangLS.Spec.lemma153_paper_residue_error_constant_pos
#print axioms ZhangLS.Spec.lemma153_paper_actual_residue_estimate
#print axioms ZhangLS.Spec.lemma153_M_uniform_bound
#print axioms ZhangLS.Spec.lemma153_general_M_normalization_uniform_bound
#print axioms ZhangLS.Spec.lemma153_actual_U_center_uniform_bound
#print axioms ZhangLS.Spec.lemma153_main_U_uniform_bound
#print axioms ZhangLS.Spec.lemma153_ramified_totient_hasProd
#print axioms ZhangLS.Spec.lemma153_zero_MU_prime_cancellation
#print axioms ZhangLS.Spec.lemma153_zero_MU_exact_cancellation
#print axioms ZhangLS.Spec.lemma153_zero_MU_LDeriv_main_term
#print axioms ZhangLS.Spec.lemma153NormalizedCenterErrorConstant
#print axioms ZhangLS.Spec.lemma153NormalizedResidueErrorConstant
#print axioms ZhangLS.Spec.lemma153_normalized_center_error_constant_pos
#print axioms ZhangLS.Spec.lemma153_normalized_residue_error_constant_pos
#print axioms ZhangLS.Spec.lemma153_paper_normalized_actual_residue
