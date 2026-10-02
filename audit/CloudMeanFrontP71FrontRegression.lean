import ZhangLS.Spec.Proposition71ReciprocalGamma
import ZhangLS.Spec.Proposition71GammaLineBound
import ZhangLS.Spec.Proposition71GammaOmegaTail
import ZhangLS.Spec.Proposition71MellinInversion
import ZhangLS.Spec.Proposition71MellinFiniteSum
import ZhangLS.Spec.Proposition71MellinDoubleSum
import ZhangLS.Spec.Proposition71DeltaOneSeries
import ZhangLS.Spec.Proposition71FrontCoefficientBounds
import ZhangLS.Spec.Proposition71DeltaOneDoubleSeries
import ZhangLS.Spec.Proposition71ReciprocalGammaNorm
import ZhangLS.Spec.Proposition71FrontIntegrands
import ZhangLS.Spec.Proposition71FrontSegment
import ZhangLS.Spec.Proposition71OriginalFrontTransform
import ZhangLS.Spec.Proposition71FrontUniformRate
import ZhangLS.Spec.Proposition71FrontContourObjects
import ZhangLS.Spec.Proposition71FrontFamilyRate

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory
open scoped Classical
set_option maxRecDepth 4096

-- The n=0 term is actually excluded, regardless of the long coefficient at zero.
example (D : ℕ) (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) (q : ℝ) :
    proposition71DeltaOneDoubleTerm D c S a q 0=0 := by
  simp [proposition71DeltaOneDoubleTerm]

-- The precise q*n scale and 1/n weight survive at every positive long index.
example (D : ℕ) (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) (q : ℝ)
    (m : ℕ) (hm : 0<m) :
    proposition71DeltaOneDoubleTerm D c S a q m=
      c m*∑n∈S, (a n/(n : ℂ))*lemma53PaperDeltaOne D ((m : ℝ)/(q*(n : ℝ))) := by
  simp [proposition71DeltaOneDoubleTerm,Nat.ne_of_gt hm]

-- Empty short support has exactly zero transformed series, including m=0.
example (D : ℕ) (c : ℕ → ℂ) (a : ℕ → ℂ) (q : ℝ) (m : ℕ) :
    proposition71DeltaOneDoubleTerm D c ∅ a q m=0 := by
  simp [proposition71DeltaOneDoubleTerm]

-- No character twist is silently inserted into either arbitrary coefficient.
example {N : ℕ} [NeZero N] (D : ℕ) (θ : DirichletCharacter ℂ N)
    (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) (t : ℝ) :
    proposition71FrontActualIntegrand D θ c S a t=
      (lemma23DirichletZ θ ((3/2 : ℂ)+(t : ℂ)*I))⁻¹*
        LSeries c ((3/2 : ℂ)+(t : ℂ)*I)*
        (∑n∈S, a n*(n : ℂ)^(((3/2 : ℂ)+(t : ℂ)*I)-1))*
        lemma53PaperOmega D ((3/2 : ℂ)+(t : ℂ)*I) := rfl

-- The original upward J(1) normalization is exact, not asymptotic.
example {N : ℕ} [NeZero N] (D : ℕ) (θ : DirichletCharacter ℂ N)
    (c : ℕ → ℂ) (S : Finset ℕ) (a : ℕ → ℂ) :
    lemma81NormalizedSegmentIntegral D 1 (proposition71FrontActualKernel D θ c S a)=
      proposition71FrontSegmentIntegral D θ c S a :=
  proposition71_front_original_contour_exact D θ c S a

-- All negative heights are retained in the full-line majorant.
example (t : ℝ) : ‖lemma53PaperThetaStar ((3/2 : ℂ)+((-t : ℝ) : ℂ)*I)‖≤4*(1+|t|) := by
  simpa only [abs_neg] using proposition71_theta_star_three_halves_bound (-t)

-- The threshold and conductor range are explicit; no A, zeta-free region,
-- mean estimate, prime-mass lower bound or target theorem appears.
#check proposition71_front_transform_uniform_rate
#check proposition71_front_actual_family_rate
end ZhangLS.Spec

#print axioms ZhangLS.Spec.proposition71_front_gammaR_ne_zero
#print axioms ZhangLS.Spec.proposition71_front_gammaR_even_quotient
#print axioms ZhangLS.Spec.proposition71_front_gammaR_odd_quotient
#print axioms ZhangLS.Spec.proposition71_front_theta_even_exact
#print axioms ZhangLS.Spec.proposition71_front_theta_odd_exact
#print axioms ZhangLS.Spec.proposition71_front_reciprocal_Z_archimedean
#print axioms ZhangLS.Spec.proposition71_front_even_inv
#print axioms ZhangLS.Spec.proposition71_front_odd_inv
#print axioms ZhangLS.Spec.proposition71_reciprocal_Z_exact
#print axioms ZhangLS.Spec.proposition71_gamma_half_norm_square
#print axioms ZhangLS.Spec.proposition71_gamma_three_halves_norm_square
#print axioms ZhangLS.Spec.proposition71_exp_div_cosh_le_two
#print axioms ZhangLS.Spec.proposition71_theta_star_three_halves_bound
#print axioms ZhangLS.Spec.proposition71GammaOmegaKernel
#print axioms ZhangLS.Spec.proposition71_gamma_omega_integrable
#print axioms ZhangLS.Spec.proposition71_omega_gamma_line_density
#print axioms ZhangLS.Spec.proposition71_gamma_omega_density_bound
#print axioms ZhangLS.Spec.proposition71_gamma_omega_mass_bound
#print axioms ZhangLS.Spec.proposition71_gamma_omega_exterior_bound
#print axioms ZhangLS.Spec.proposition71_actual_delta_vertical_integrable
#print axioms ZhangLS.Spec.proposition71_actual_delta_mellin_inversion
#print axioms ZhangLS.Spec.proposition71_actual_scaled_delta_mellin
#print axioms ZhangLS.Spec.proposition71_inverse_mellin_integrand_integrable
#print axioms ZhangLS.Spec.proposition71_scaled_mellin_power
#print axioms ZhangLS.Spec.proposition71_extracted_scale_norm
#print axioms ZhangLS.Spec.proposition71_actual_finite_mellin_sum
#print axioms ZhangLS.Spec.proposition71_positive_ratio_cpow
#print axioms ZhangLS.Spec.proposition71_finite_mellin_integrand_integrable
#print axioms ZhangLS.Spec.proposition71DoubleMellinIntegrand
#print axioms ZhangLS.Spec.proposition71_double_mellin_integrand_expansion
#print axioms ZhangLS.Spec.proposition71_double_mellin_integrand_integrable
#print axioms ZhangLS.Spec.proposition71_actual_double_mellin_sum
#print axioms ZhangLS.Spec.proposition71DeltaOneSeriesTerm
#print axioms ZhangLS.Spec.proposition71_delta_one_series_term_norm
#print axioms ZhangLS.Spec.proposition71_delta_one_series_term_kernel
#print axioms ZhangLS.Spec.proposition71_delta_one_series_term_integrable
#print axioms ZhangLS.Spec.proposition71_delta_one_series_integral_norm_summable
#print axioms ZhangLS.Spec.proposition71_delta_one_series_tsum_integrable
#print axioms ZhangLS.Spec.proposition71_delta_one_integral
#print axioms ZhangLS.Spec.proposition71_delta_one_series_term_integral
#print axioms ZhangLS.Spec.proposition71_actual_delta_one_series
#print axioms ZhangLS.Spec.proposition71_front_coefficient_summable
#print axioms ZhangLS.Spec.proposition71TauFiveThreeHalvesMass
#print axioms ZhangLS.Spec.proposition71_tau_three_halves_norm_summable
#print axioms ZhangLS.Spec.proposition71_tau_three_halves_mass_pos
#print axioms ZhangLS.Spec.proposition71_front_lseries_norm_bound
#print axioms ZhangLS.Spec.proposition71_front_lseries_analytic
#print axioms ZhangLS.Spec.proposition71ShortCoefficientMass
#print axioms ZhangLS.Spec.proposition71_short_coefficient_mass_nonneg
#print axioms ZhangLS.Spec.proposition71_short_polynomial_norm
#print axioms ZhangLS.Spec.proposition71_short_coefficient_mass_bound
#print axioms ZhangLS.Spec.proposition71FrontDominantIntegrand
#print axioms ZhangLS.Spec.proposition71DeltaOneDoubleTerm
#print axioms ZhangLS.Spec.proposition71_positive_shifted_power_product
#print axioms ZhangLS.Spec.proposition71_front_dominant_finite_expansion
#print axioms ZhangLS.Spec.proposition71_actual_delta_one_double_series
#print axioms ZhangLS.Spec.proposition71DominantReciprocalZ
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_norm
#print axioms ZhangLS.Spec.proposition71_character_neg_one_norm
#print axioms ZhangLS.Spec.proposition71_dominant_reciprocal_Z_norm
#print axioms ZhangLS.Spec.proposition71_reciprocal_Z_error_exact
#print axioms ZhangLS.Spec.proposition71_reciprocal_Z_error_norm
#print axioms ZhangLS.Spec.proposition71_dominant_reciprocal_Z_line_bound
#print axioms ZhangLS.Spec.proposition71FrontActualIntegrand
#print axioms ZhangLS.Spec.proposition71FrontGaussIntegrand
#print axioms ZhangLS.Spec.proposition71_front_actual_factorization
#print axioms ZhangLS.Spec.proposition71_front_error_exact
#print axioms ZhangLS.Spec.proposition71_front_error_norm
#print axioms ZhangLS.Spec.proposition71_front_gauss_integrable
#print axioms ZhangLS.Spec.proposition71_front_gauss_norm_bound
#print axioms ZhangLS.Spec.proposition71_front_actual_interval_integrable
#print axioms ZhangLS.Spec.proposition71_integral_segment_complement
#print axioms ZhangLS.Spec.proposition71_front_parity_segment_bound
#print axioms ZhangLS.Spec.proposition71_front_exterior_bound
#print axioms ZhangLS.Spec.proposition71_front_gauss_full_integral
#print axioms ZhangLS.Spec.proposition71FrontSegmentIntegral
#print axioms ZhangLS.Spec.proposition71_original_front_lower_height
#print axioms ZhangLS.Spec.proposition71_original_front_parity_decay
#print axioms ZhangLS.Spec.proposition71_original_front_exterior_gap
#print axioms ZhangLS.Spec.proposition71_original_front_transform
#print axioms ZhangLS.Spec.proposition71_front_kernel_polynomial
#print axioms ZhangLS.Spec.proposition71_front_scalar_budget
#print axioms ZhangLS.Spec.proposition71FrontErrorConstant
#print axioms ZhangLS.Spec.proposition71_front_error_constant_pos
#print axioms ZhangLS.Spec.proposition71_front_transform_uniform_rate
#print axioms ZhangLS.Spec.proposition71FrontActualKernel
#print axioms ZhangLS.Spec.proposition71_front_omega_exact
#print axioms ZhangLS.Spec.proposition71_front_segment_point_exact
#print axioms ZhangLS.Spec.proposition71_front_original_contour_exact
#print axioms ZhangLS.Spec.proposition71_actual_family_card_le_mass
#print axioms ZhangLS.Spec.proposition71_front_actual_family_rate
#print ZhangLS.Spec.proposition71FrontActualIntegrand
#print ZhangLS.Spec.proposition71FrontActualKernel
#print ZhangLS.Spec.proposition71FrontDominantIntegrand
#print ZhangLS.Spec.proposition71DeltaOneDoubleTerm
#print ZhangLS.Spec.proposition71FrontSegmentIntegral
#print ZhangLS.Spec.proposition71FrontErrorConstant
#print ZhangLS.Spec.proposition71TauFiveThreeHalvesMass
#print ZhangLS.Spec.proposition71_reciprocal_Z_exact
#print ZhangLS.Spec.proposition71_original_front_transform
#print ZhangLS.Spec.proposition71_front_transform_uniform_rate
#print ZhangLS.Spec.proposition71_front_actual_family_rate
#print ZhangLS.Spec.lemma81NormalizedSegmentIntegral
#print ZhangLS.Spec.lemma81SegmentPoint
#print ZhangLS.Spec.lemma81Omega
#print ZhangLS.Spec.lemma53PaperOmega
#print ZhangLS.Spec.lemma53PaperDeltaOne
#print ZhangLS.Spec.lemma33ActualFamily
#print ZhangLS.Spec.Lemma23InPsi
#print ZhangLS.Spec.lemma33ActualPrimeMass
