import ZhangLS.Spec.Lemma162Definitions
import ZhangLS.Spec.Lemma162ActualMLocal
import ZhangLS.Spec.Lemma162GeneralMNorm
import ZhangLS.Spec.Lemma162GeneralMSeries
import ZhangLS.Spec.Lemma162GeneralMEuler
import ZhangLS.Spec.Lemma162GeneralMContinuation
import ZhangLS.Spec.Lemma162OddM
import ZhangLS.Spec.Lemma162NuChi
import ZhangLS.Spec.Lemma162OddVarpi
import ZhangLS.Spec.Lemma162OddLocalRatio
import ZhangLS.Spec.Lemma162NuChiNorm
import ZhangLS.Spec.Lemma162OddCoefficientNorm
import ZhangLS.Spec.Lemma162PrimeSupportedConvolution
import ZhangLS.Spec.Lemma162CoefficientReassembly
import ZhangLS.Spec.Lemma162CubicNormSeries
import ZhangLS.Spec.Lemma162ActualCoefficientNorm
import ZhangLS.Spec.Lemma162PrimeSupportedSeries
import ZhangLS.Spec.Lemma162ActualDirichletSeries
import ZhangLS.Spec.Lemma162HadamardH2H3
import ZhangLS.Spec.Lemma162LocalExtraction
import ZhangLS.Spec.Lemma162NuChiLocalH3
import ZhangLS.Spec.Lemma162OriginalValueWitness
import ZhangLS.Spec.Lemma162PaperArithmeticBridge
import ZhangLS.Spec.Lemma162LocalKernel
import ZhangLS.Spec.Lemma162RawLocalSeries
import ZhangLS.Spec.Lemma162ActualLocalBridge
import ZhangLS.Spec.Lemma162ActualRawExtraction
import ZhangLS.Spec.Lemma162ActualShiftedIdentity
import ZhangLS.Spec.Lemma162RawPolynomialTail
import ZhangLS.Spec.Lemma162LocalDataRational
import ZhangLS.Spec.Lemma162FirstRemainderNorm
import ZhangLS.Spec.Lemma162ActualUnramifiedBound
import ZhangLS.Spec.Lemma162RawMajorant
import ZhangLS.Spec.Lemma162CorrectedAnalytic
import ZhangLS.Spec.Lemma162ActualOldValueWitness

open ZhangLS.Spec
#print axioms ZhangLS.Spec.lemma162Varpi
#print axioms ZhangLS.Spec.lemma162NuChi
#print axioms ZhangLS.Spec.lemma162Coefficient
#print axioms ZhangLS.Spec.lemma162DirichletSeries
#print axioms ZhangLS.Spec.Lemma162OriginalContinuation
#print axioms ZhangLS.Spec.Lemma162ShiftedContinuation
#print axioms ZhangLS.Spec.lemma162_lambda_one
#print axioms ZhangLS.Spec.lemma162_lambda_prime
#print axioms ZhangLS.Spec.lemma162_varpi_one
#print axioms ZhangLS.Spec.lemma162_varpi_prime
#print axioms ZhangLS.Spec.lemma162_coefficient_d
#print axioms ZhangLS.Spec.lemma162_coefficient_unexcluded
#print axioms ZhangLS.Spec.lemma162_coefficient_l_unexcluded
#print axioms ZhangLS.Spec.lemma162_coefficient_l
#print axioms ZhangLS.Spec.lemma162_coefficient_d_hasSum
#print axioms ZhangLS.Spec.lemma162_coefficient_l_hasSum
#print axioms ZhangLS.Spec.lemma162GeneralMPrimeFactor
#print axioms ZhangLS.Spec.lemma162_general_m_local_agreement
#print axioms ZhangLS.Spec.lemma162_general_m_prime_norm_le
#print axioms ZhangLS.Spec.lemma162_general_m_local_norm_series
#print axioms ZhangLS.Spec.lemma162_general_m_term_mul
#print axioms ZhangLS.Spec.lemma162_general_m_prime_power_term
#print axioms ZhangLS.Spec.lemma162_general_m_lseries_summable
#print axioms ZhangLS.Spec.lemma162_general_m_dirichlet_series_hasProd
#print axioms ZhangLS.Spec.lemma162GeneralMEulerProduct
#print axioms ZhangLS.Spec.lemma162GeneralMExceptionBound
#print axioms ZhangLS.Spec.lemma162_general_m_exception_bound_pos
#print axioms ZhangLS.Spec.lemma162_general_m_prime_error_bound
#print axioms ZhangLS.Spec.lemma162_prime_divisor_indicator_summable
#print axioms ZhangLS.Spec.lemma162GeneralMMajorant
#print axioms ZhangLS.Spec.lemma162_general_m_majorant_summable
#print axioms ZhangLS.Spec.lemma162_general_m_prime_differentiableOn
#print axioms ZhangLS.Spec.lemma162_general_m_products_locally_uniform
#print axioms ZhangLS.Spec.lemma162_general_m_euler_multipliable
#print axioms ZhangLS.Spec.lemma162_general_m_analyticOnNhd
#print axioms ZhangLS.Spec.lemma162_general_m_local_product_agreement
#print axioms ZhangLS.Spec.lemma162_general_m_actual_continuation
#print axioms ZhangLS.Spec.lemma162_general_m_baseline_prime
#print axioms ZhangLS.Spec.lemma162_general_m_baseline
#print axioms ZhangLS.Spec.lemma162PrimeTwo
#print axioms ZhangLS.Spec.lemma162OddMPrimeFactor
#print axioms ZhangLS.Spec.lemma162OddMEulerProduct
#print axioms ZhangLS.Spec.lemma162_odd_m_multipliable
#print axioms ZhangLS.Spec.lemma162_general_m_two_odd_decomposition
#print axioms ZhangLS.Spec.lemma162_odd_m_baseline
#print axioms ZhangLS.Spec.lemma162TwoNormalizer
#print axioms ZhangLS.Spec.lemma162_star_odd_decomposition
#print axioms ZhangLS.Spec.lemma162_odd_baseline_nonzero
#print axioms ZhangLS.Spec.lemma162_general_m_prime_pair_mul
#print axioms ZhangLS.Spec.lemma162_odd_m_prime_pair_mul
#print axioms ZhangLS.Spec.lemma162_odd_m_pair_mul
#print axioms ZhangLS.Spec.lemma162_odd_m_normalized_pair_mul
#print axioms ZhangLS.Spec.lemma162_character_one
#print axioms ZhangLS.Spec.lemma162_nu_chi_one
#print axioms ZhangLS.Spec.lemma162_nu_chi_prime
#print axioms ZhangLS.Spec.lemma162_actual_hadamard_prime
#print axioms ZhangLS.Spec.lemma162_lambda_mul
#print axioms ZhangLS.Spec.lemma162OddVarpiKernel
#print axioms ZhangLS.Spec.lemma162_odd_varpi_kernel_one
#print axioms ZhangLS.Spec.lemma162_odd_varpi_kernel_mul
#print axioms ZhangLS.Spec.lemma162OddVarpiArithmetic
#print axioms ZhangLS.Spec.lemma162_odd_varpi_multiplicative
#print axioms ZhangLS.Spec.lemma162OddRestriction
#print axioms ZhangLS.Spec.lemma162_odd_restriction_multiplicative
#print axioms ZhangLS.Spec.lemma162_nu_chi_multiplicative
#print axioms ZhangLS.Spec.lemma162OddCoefficientArithmetic
#print axioms ZhangLS.Spec.lemma162_odd_coefficient_multiplicative
#print axioms ZhangLS.Spec.lemma162_odd_base_prime_nonzero
#print axioms ZhangLS.Spec.lemma162_odd_m_prime_power_ratio
#print axioms ZhangLS.Spec.lemma162_odd_inverse_family_bounded
#print axioms ZhangLS.Spec.lemma162GeneralMNormBound
#print axioms ZhangLS.Spec.lemma162_general_m_norm_bound_pos
#print axioms ZhangLS.Spec.lemma162_general_m_local_norm
#print axioms ZhangLS.Spec.lemma162_character_arithmetic_norm_le_one
#print axioms ZhangLS.Spec.lemma162_actual_nu_prime_power_norm
#print axioms ZhangLS.Spec.lemma162_actual_nu_chi_prime_power_norm
#print axioms ZhangLS.Spec.lemma162_divisor_kernel_prime_power_norm
#print axioms ZhangLS.Spec.lemma162_odd_coefficient_prime_power_norm_of_kernel
#print axioms ZhangLS.Spec.lemma162_divisor_kernel_coprime_split
#print axioms ZhangLS.Spec.lemma162PrimePowerPart
#print axioms ZhangLS.Spec.lemma162CoprimePart
#print axioms ZhangLS.Spec.lemma162_prime_power_part_apply
#print axioms ZhangLS.Spec.lemma162_coprime_part_apply
#print axioms ZhangLS.Spec.lemma162_prime_power_coprime_unique
#print axioms ZhangLS.Spec.lemma162_prime_supported_convolution_apply
#print axioms ZhangLS.Spec.lemma162_divisor_kernel_prime_convolution
#print axioms ZhangLS.Spec.lemma162_coprime_part_multiplicative
#print axioms ZhangLS.Spec.lemma162_pmul_convolution_of_coprime_support
#print axioms ZhangLS.Spec.lemma162_prime_supported_pmul_convolution
#print axioms ZhangLS.Spec.lemma162_weighted_divisor_kernel_prime_convolution
#print axioms ZhangLS.Spec.lemma162_weighted_divisor_kernel_lseries
#print axioms ZhangLS.Spec.lemma162_odd_m_remove_two_powers
#print axioms ZhangLS.Spec.lemma162_m_two_remove_odd
#print axioms ZhangLS.Spec.lemma162ActualVarpiKernel
#print axioms ZhangLS.Spec.lemma162TwoVarpiKernel
#print axioms ZhangLS.Spec.lemma162_actual_kernel_two_odd_split
#print axioms ZhangLS.Spec.lemma162ActualCoefficientArithmetic
#print axioms ZhangLS.Spec.lemma162_actual_coefficient_arithmetic_eq
#print axioms ZhangLS.Spec.lemma162TwoCoefficientArithmetic
#print axioms ZhangLS.Spec.lemma162_actual_coefficient_reassembly
#print axioms ZhangLS.Spec.lemma162_cubic_half_majorant_summable
#print axioms ZhangLS.Spec.lemma162CubicNormConstant
#print axioms ZhangLS.Spec.lemma162_cubic_norm_constant_nonneg
#print axioms ZhangLS.Spec.lemma162_cubic_local_norm_series
#print axioms ZhangLS.Spec.lemma162_cubic_local_norm_series_general
#print axioms ZhangLS.Spec.lemma162_lambda_prime_power_norm
#print axioms ZhangLS.Spec.lemma162_prime_power_varpi_weight_norm
#print axioms ZhangLS.Spec.lemma162_actual_odd_kernel_prime_power_norm
#print axioms ZhangLS.Spec.lemma162_actual_odd_coefficient_cubic_bound
#print axioms ZhangLS.Spec.lemma162TwoNormConstant
#print axioms ZhangLS.Spec.lemma162_two_norm_constant_nonneg
#print axioms ZhangLS.Spec.lemma162_actual_two_kernel_prime_power_norm
#print axioms ZhangLS.Spec.lemma162_actual_two_coefficient_prime_power_norm
#print axioms ZhangLS.Spec.lemma162_actual_two_local_norm_series
#print axioms ZhangLS.Spec.lemma162_actual_odd_local_norm_series
#print axioms ZhangLS.Spec.lemma162_arithmetic_prime_power_term
#print axioms ZhangLS.Spec.lemma162_prime_supported_term_zero
#print axioms ZhangLS.Spec.lemma162_prime_supported_lseries_hasSum
#print axioms ZhangLS.Spec.lemma162_prime_supported_lseries_summable
#print axioms ZhangLS.Spec.lemma162_prime_supported_lseries_eq
#print axioms ZhangLS.Spec.lemma162_prime_power_part_pmul
#print axioms ZhangLS.Spec.lemma162_arithmetic_term_mul
#print axioms ZhangLS.Spec.lemma162_actual_odd_lseries_summable
#print axioms ZhangLS.Spec.lemma162_actual_odd_dirichlet_hasProd
#print axioms ZhangLS.Spec.lemma162_actual_two_lseries_summable
#print axioms ZhangLS.Spec.lemma162_actual_two_lseries_eq
#print axioms ZhangLS.Spec.lemma162_actual_lseries_summable
#print axioms ZhangLS.Spec.lemma162_actual_dirichlet_two_odd_product
#print axioms ZhangLS.Spec.lemma162_odd_coefficient_two_succ
#print axioms ZhangLS.Spec.lemma162_odd_two_local_series
#print axioms ZhangLS.Spec.lemma162ActualLocalSeries
#print axioms ZhangLS.Spec.lemma162_actual_dirichlet_series_hasProd
#print axioms ZhangLS.Spec.lemma162_weighted_convolution_hasSum
#print axioms ZhangLS.Spec.lemma162_weighted_h3_hasSum
#print axioms ZhangLS.Spec.lemma162_h2_diagonal
#print axioms ZhangLS.Spec.lemma162_hadamard_fraction_identity
#print axioms ZhangLS.Spec.lemma162_h2_h3_hadamard_hasSum
#print axioms ZhangLS.Spec.lemma162LocalLambda
#print axioms ZhangLS.Spec.lemma162M01
#print axioms ZhangLS.Spec.lemma162M00
#print axioms ZhangLS.Spec.lemma162M10
#print axioms ZhangLS.Spec.lemma162M11
#print axioms ZhangLS.Spec.lemma162_m00_source_identity
#print axioms ZhangLS.Spec.lemma162_ramified_factors
#print axioms ZhangLS.Spec.lemma162FirstNumerator
#print axioms ZhangLS.Spec.lemma162FirstRemainder
#print axioms ZhangLS.Spec.lemma162_exact_first_remainder
#print axioms ZhangLS.Spec.lemma162_shifted_first_coefficient
#print axioms ZhangLS.Spec.lemma162_unshifted_first_coefficient
#print axioms ZhangLS.Spec.lemma162ShiftedRemoval
#print axioms ZhangLS.Spec.lemma162_shifted_removal_linear
#print axioms ZhangLS.Spec.lemma162_special_two_center
#print axioms ZhangLS.Spec.lemma162_zero_shift_centers
#print axioms ZhangLS.Spec.lemma162_extraction_exponents_unique
#print axioms ZhangLS.Spec.lemma162_arithmetic_mul_prime_power
#print axioms ZhangLS.Spec.lemma162_character_prime_power
#print axioms ZhangLS.Spec.lemma162_nu_prime_power_h2
#print axioms ZhangLS.Spec.lemma162_nu_chi_prime_power_h3
#print axioms ZhangLS.Spec.lemma162RegularOldExtension
#print axioms ZhangLS.Spec.lemma162_regular_old_extension_at_one
#print axioms ZhangLS.Spec.lemma162_regular_old_extension_continuous
#print axioms ZhangLS.Spec.lemma162_regular_old_extension_eq_quotient
#print axioms ZhangLS.Spec.lemma162Approach
#print axioms ZhangLS.Spec.lemma162_approach_re
#print axioms ZhangLS.Spec.lemma162_approach_tendsto
#print axioms ZhangLS.Spec.lemma162_original_value_forced_zero
#print axioms ZhangLS.Spec.lemma162PaperShift
#print axioms ZhangLS.Spec.lemma162_paper_shift_zero
#print axioms ZhangLS.Spec.lemma162_paper_shift_one
#print axioms ZhangLS.Spec.lemma162_paper_shift_re
#print axioms ZhangLS.Spec.lemma162_paper_shift_nonzero
#print axioms ZhangLS.Spec.Lemma162PaperArithmeticBridgeAt
#print axioms ZhangLS.Spec.lemma162_paper_actual_arithmetic_bridge
#print axioms ZhangLS.Spec.lemma162_arithmetic_bridge_with_shared_shift_constant
#print axioms ZhangLS.Spec.lemma162RawKernel
#print axioms ZhangLS.Spec.lemma162RawCoefficient
#print axioms ZhangLS.Spec.lemma162_raw_kernel_boundary_decomposition
#print axioms ZhangLS.Spec.lemma162_antidiagonal_snd_boundary
#print axioms ZhangLS.Spec.lemma162_antidiagonal_fst_boundary
#print axioms ZhangLS.Spec.lemma162_antidiagonal_corner
#print axioms ZhangLS.Spec.lemma162_raw_kernel_sum
#print axioms ZhangLS.Spec.lemma162_raw_coefficient_zero
#print axioms ZhangLS.Spec.lemma162_divisor_kernel_prime_power
#print axioms ZhangLS.Spec.lemma162_lambda_prime_power
#print axioms ZhangLS.Spec.lemma162_nat_power_cpow
#print axioms ZhangLS.Spec.lemma162_general_m_prime_power_flags
#print axioms ZhangLS.Spec.lemma162RawP
#print axioms ZhangLS.Spec.lemma162RawQ
#print axioms ZhangLS.Spec.lemma162RawS
#print axioms ZhangLS.Spec.lemma162RawPolynomial
#print axioms ZhangLS.Spec.lemma162_common_denominator
#print axioms ZhangLS.Spec.lemma162_raw_local_hasSum
#print axioms ZhangLS.Spec.lemma162Local00
#print axioms ZhangLS.Spec.lemma162Local01
#print axioms ZhangLS.Spec.lemma162Local10
#print axioms ZhangLS.Spec.lemma162Local11
#print axioms ZhangLS.Spec.lemma162LocalNormalizer
#print axioms ZhangLS.Spec.lemma162RawPrimeCoefficient
#print axioms ZhangLS.Spec.lemma162_local_kernel_prime_power
#print axioms ZhangLS.Spec.lemma162_odd_kernel_raw_eq
#print axioms ZhangLS.Spec.lemma162_two_kernel_raw_eq
#print axioms ZhangLS.Spec.lemma162_odd_prime_coprime_two
#print axioms ZhangLS.Spec.lemma162_odd_prime_power_raw_eq
#print axioms ZhangLS.Spec.lemma162_two_prime_power_raw_eq
#print axioms ZhangLS.Spec.lemma162_actual_local_series_eq_raw
#print axioms ZhangLS.Spec.lemma162RawPrimeCorrection
#print axioms ZhangLS.Spec.lemma162_normalizers_hasProd
#print axioms ZhangLS.Spec.lemma162_local_normalizer_nonzero
#print axioms ZhangLS.Spec.lemma162_ramified_actual_data
#print axioms ZhangLS.Spec.lemma162_h3_ramified
#print axioms ZhangLS.Spec.lemma162_ramified_raw_coefficient
#print axioms ZhangLS.Spec.lemma162_ramified_normalizer
#print axioms ZhangLS.Spec.lemma162_actual_raw_local_extraction
#print axioms ZhangLS.Spec.lemma162ShiftedMainFactor
#print axioms ZhangLS.Spec.lemma162RawEulerProduct
#print axioms ZhangLS.Spec.lemma162CorrectedEulerProduct
#print axioms ZhangLS.Spec.lemma162_shifted_prime_monomial
#print axioms ZhangLS.Spec.lemma162_shifted_main_factor_nonzero
#print axioms ZhangLS.Spec.lemma162_shifted_main_factor_hasProd
#print axioms ZhangLS.Spec.lemma162_shifted_removal_hasProd
#print axioms ZhangLS.Spec.lemma162_raw_euler_hasProd_on_convergence
#print axioms ZhangLS.Spec.lemma162_actual_shifted_euler_identity
#print axioms ZhangLS.Spec.lemma162RawP1
#print axioms ZhangLS.Spec.lemma162RawQ1
#print axioms ZhangLS.Spec.lemma162RawPTail
#print axioms ZhangLS.Spec.lemma162RawQTail
#print axioms ZhangLS.Spec.lemma162RawSTail
#print axioms ZhangLS.Spec.lemma162RawPQTail
#print axioms ZhangLS.Spec.lemma162RawLinear
#print axioms ZhangLS.Spec.lemma162RawTail
#print axioms ZhangLS.Spec.lemma162_raw_polynomial_expansion
#print axioms ZhangLS.Spec.lemma162_norm_sum_four
#print axioms ZhangLS.Spec.lemma162_raw_small_polynomial_bounds
#print axioms ZhangLS.Spec.lemma162_raw_pq_tail_bound
#print axioms ZhangLS.Spec.lemma162_raw_tail_bound
#print axioms ZhangLS.Spec.lemma162_center_prime_monomial
#print axioms ZhangLS.Spec.lemma162_actual_local_data_rational
#print axioms ZhangLS.Spec.lemma162_half_denominator_bound
#print axioms ZhangLS.Spec.lemma162_four_denominator_bounds
#print axioms ZhangLS.Spec.lemma162_first_remainder_bound
#print axioms ZhangLS.Spec.lemma162_norm_one_add_twice
#print axioms ZhangLS.Spec.lemma162_actual_raw_linear_bound
#print axioms ZhangLS.Spec.lemma162_actual_raw_unramified_error
#print axioms ZhangLS.Spec.lemma162UnramifiedMajorant
#print axioms ZhangLS.Spec.lemma162_unramified_majorant_nonneg
#print axioms ZhangLS.Spec.lemma162_unramified_majorant_summable
#print axioms ZhangLS.Spec.lemma162_unramified_raw_error_majorized
#print axioms ZhangLS.Spec.lemma162_ramified_raw_error
#print axioms ZhangLS.Spec.lemma162RawMajorant
#print axioms ZhangLS.Spec.lemma162_raw_majorant_nonneg
#print axioms ZhangLS.Spec.lemma162_raw_majorant_summable
#print axioms ZhangLS.Spec.lemma162_actual_raw_error_majorized
#print axioms ZhangLS.Spec.lemma162_raw_prime_differentiable
#print axioms ZhangLS.Spec.lemma162_raw_euler_multipliable
#print axioms ZhangLS.Spec.lemma162_raw_products_locally_uniform
#print axioms ZhangLS.Spec.lemma162_raw_euler_analytic
#print axioms ZhangLS.Spec.lemma162_corrected_euler_analytic
#print axioms ZhangLS.Spec.lemma162RawDBound
#print axioms ZhangLS.Spec.lemma162_raw_d_bound_pos
#print axioms ZhangLS.Spec.lemma162_raw_finite_product_bound
#print axioms ZhangLS.Spec.lemma162_raw_euler_bound
#print axioms ZhangLS.Spec.lemma162_corrected_euler_bound
#print axioms ZhangLS.Spec.lemma162_actual_shifted_continuation
#print axioms ZhangLS.Spec.lemma162OldActualExtension
#print axioms ZhangLS.Spec.lemma162_old_actual_continuous_extension
#print axioms ZhangLS.Spec.lemma162_actual_original_value_forced_zero
#print axioms ZhangLS.Spec.lemma162_paper_corrected_analytic_bridge
#print axioms ZhangLS.Spec.lemma162_paper_old_center_forced_zero
