import ZhangLS.Spec.Proposition141WeightedBilinear
import ZhangLS.Spec.Proposition141ConductorBudget
import ZhangLS.Spec.DivisorPowerBudget
import ZhangLS.Spec.Proposition141DoubleMellin
import ZhangLS.Spec.CoprimeGaussPrimeAverage
import ZhangLS.Spec.InducedGaussMainCharacters
import ZhangLS.Spec.AdditiveReciprocity
import ZhangLS.Spec.Proposition141MainSeriesConvergence
import ZhangLS.Spec.Proposition141TailRates
import ZhangLS.Spec.DivisorSmallPowerBudget
import ZhangLS.Spec.Proposition141Objects
import ZhangLS.Spec.Proposition141Conductor
import ZhangLS.Spec.Proposition141SmallConductor
import ZhangLS.Spec.Proposition141Support
import ZhangLS.Spec.Proposition141OffDiagonal
import ZhangLS.Spec.Proposition141SupportedPrimeBound
import ZhangLS.Spec.Proposition141ComplexShift
import ZhangLS.Spec.Proposition141ShiftedEstimate
import ZhangLS.Spec.Proposition141CharacterExpansion
import ZhangLS.Spec.Proposition141DivisorBounds
import ZhangLS.Spec.Proposition141EighthPrimeIntegral
import ZhangLS.Spec.Proposition141SmallKernel
import ZhangLS.Spec.Proposition141OffDiagonalKernel
import ZhangLS.Spec.Proposition141SmallCoefficientSum
set_option autoImplicit false
open ZhangLS.Spec Complex
open scoped ComplexConjugate

example : Proposition141Target ↔
    ∀ Bκ Ba : ℝ, 0 < Bκ → 0 < Ba → ∀ ε : ℝ, 0 < ε →
      ∃ D₀ : ℕ, 2 ≤ D₀ ∧ ∀ D : ℕ, D₀ ≤ D →
        ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
          ∀ κ a : ℕ → ℂ, Proposition141KappaBound Bκ κ →
            Proposition141AdmissibleSequence D Ba a →
            ∀ β : ℂ, ‖β‖ < 5 * lemma44PaperAlpha D →
              ‖proposition141ThetaTwo χ β κ a - proposition141MainTerm χ β κ a‖ ≤
                ε * lemma33ActualPrimeMass D := Iff.rfl

example (B : ℝ) (κ : ℕ → ℂ) : Proposition141KappaBound B κ ↔
    ∀ n : ℕ, 0<n → ‖κ n‖ ≤ B * lemma34Tau 5 n := Iff.rfl

example (D : ℕ) (B : ℝ) (a : ℕ → ℂ) : Proposition141AdmissibleSequence D B a ↔
    (∀ n : ℕ, 0<n → ‖a n‖ ≤ B) ∧
      ∀ n : ℕ, 2 * (lemma23PaperP D * lemma56PaperT D ^ (-2 : ℤ) * lemma51PaperT0 D) <
        (n : ℝ) → a n=0 := Iff.rfl

example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ → ℂ) :
    proposition141ThetaTwo χ β κ a =
      ∑ ψ ∈ proposition21ActualPsi1Family χ,
        ((ψ.1.val : ℂ) * (lemma51PaperT0 D : ℂ))^β *
          proposition141Integral χ κ a ψ.2 := rfl

example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (κ a : ℕ → ℂ) (ψ : DirichletCharacter ℂ p) :
    proposition141Integral χ κ a ψ =
      letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
      proposition141SegmentIntegral D (fun s =>
        (lemma23DirichletZ (lemma44CharacterTwist χ ψ) s)⁻¹ *
          proposition141KappaSeries κ ψ s * proposition141Polynomial D a ψ⁻¹ (1-s) *
            lemma53PaperOmega D s) := rfl

example {D : ℕ} (χ : RealPrimitiveCharacter D) (β : ℂ) (κ a : ℕ → ℂ) :
    proposition141MainTerm χ β κ a =
      (Nat.totient D : ℂ)⁻¹ * ∑ p ∈ lemma33PrimeWindow D,
        proposition141ShiftWeight D p β *
          ∑ d ∈ proposition141Indices D, (d : ℂ)⁻¹ *
            ∑ k ∈ proposition141Indices D,
              (ArithmeticFunction.moebius k : ℂ) * χ.chi (k : ZMod D) * a (d*k) /
                ((k : ℂ) * (Nat.totient k : ℂ)) *
                (∑' l : ℕ+, if (l : ℕ).Coprime k then
                  χ.chi ((l : ℕ) : ZMod D) * κ (d*l) *
                    lemma53PaperDelta D ((l : ℝ) / ((D : ℝ)*p*k)) else 0) := rfl

example {D N : ℕ} (χ : RealPrimitiveCharacter D) (hD : D ∣ N)
    (θ : DirichletCharacter ℂ N) :
    proposition141PrimeCharacter χ hD θ = χ.chi.changeLevel hD * θ⁻¹ := rfl

example {D N : ℕ} (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N) (τ : ℝ) :
    proposition141ProductPrimeSum χ θ τ =
      ∑ p ∈ lemma56PaperPrimes D, χ.chi (p : ZMod D) * conj (θ (p : ZMod N)) *
        (p : ℂ) ^ (1 + I * (τ : ℂ)) := rfl

example {D N : ℕ} (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (β : ℂ) (τ : ℝ) :
    proposition141ShiftedProductPrimeSum χ θ β τ =
      ∑ p ∈ lemma56PaperPrimes D, χ.chi (p : ZMod D) * conj (θ (p : ZMod N)) *
        (p : ℂ) ^ (1 + I * (τ : ℂ) + β) := rfl

example {D : ℕ} (hD : 2≤D) {β : ℂ} (hβ : ‖β‖≤1) {τ : ℝ}
    (hτ : |τ|≤(D:ℝ)/2) : |τ+β.im|≤D :=
  proposition141_shifted_height_margin hD hβ hτ


example {D N : ℕ} (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (β : ℂ) (h r l : ℝ) :
    proposition141ActualShiftedPrimeKernel χ θ β h r l =
      ∑ p ∈ lemma56PaperPrimes D, χ.chi (p:ZMod D)*conj (θ (p:ZMod N))*(p:ℂ)^β*
        lemma53PaperDelta D (l/((p:ℝ)*h*r)) := rfl

example {D N : ℕ} (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ N)
    (β : ℂ) (κ : ℕ → ℂ) (D₁ d : ℕ) (h r : ℝ) (S : Finset ℕ) :
    proposition141FiniteSmallCharacterSum χ θ β κ D₁ d h r S =
      ∑ l ∈ S, κ (D₁*d*l)*θ (l:ZMod N)*
        proposition141ActualShiftedPrimeKernel χ θ β h r l := rfl


example {D h r : ℕ} (hD : 0<D) : D∣h*r ↔ D/(D.gcd r)∣h :=
  ZhangLS.Spec.proposition141_conductor_congruence hD
example (D : ℕ) :
    (∑d∈D.divisors,(ZhangLS.Spec.lemma34Tau 5 d:ℝ))≤(2:ℝ)^630*Real.sqrt (D:ℝ) :=
  ZhangLS.Spec.divisorPower_divisor_tau_five_sqrt D
example {D : ℕ} (hL : 2000≤ZhangLS.Spec.lemma23PaperL D) {β : ℂ}
    (hβ : ‖β‖<5*ZhangLS.Spec.lemma44PaperAlpha D) :
    ‖(ZhangLS.Spec.lemma51PaperT0 D:ℂ)^β‖≤Real.exp 20 :=
  ZhangLS.Spec.proposition141_t0_shift_norm hL hβ
example (D : ℕ) : ZhangLS.Spec.lemma33ActualPrimeMass D=ZhangLS.Spec.lemma56PrimeMass D :=
  ZhangLS.Spec.proposition141_actual_prime_masses_equal D
example {D : ℕ} (hD : 0<D) (hL : 2000≤ZhangLS.Spec.lemma23PaperL D) (m : ℕ) (hm : m≤500) :
    Real.exp (-ZhangLS.Spec.lemma23PaperL D^10/2)*ZhangLS.Spec.lemma23PaperP D^m≤1/(D:ℝ)^100 :=
  ZhangLS.Spec.proposition141_actual_tail_polynomial_rate hD hL m hm
example : ZhangLS.Spec.proposition141TauFiveSquareMass=(Real.pi^2/6)^5 :=
  ZhangLS.Spec.proposition141_tau_five_square_mass_eq
example (D : ℕ) :
    (∑d∈D.divisors,(ZhangLS.Spec.lemma34Tau 5 d:ℝ))≤
      ZhangLS.Spec.divisorPowerQuarterConstant 6*(D:ℝ)^(1/4:ℝ) :=
  ZhangLS.Spec.divisorPower_divisor_tau_five_quarter D
-- GENERATED AXIOM CHECKS
#print axioms ZhangLS.Spec.proposition141PrimeCharacter
#print axioms ZhangLS.Spec.proposition141_equal_nat_evaluations_induce
#print axioms ZhangLS.Spec.proposition141_prime_character_nonprincipal
#print axioms ZhangLS.Spec.proposition141_prime_character_not_chi_induced
#print axioms ZhangLS.Spec.proposition141_actual_product_inducer_admissible
#print axioms ZhangLS.Spec.proposition141_product_conductor_le
#print axioms ZhangLS.Spec.proposition141_product_inducer_eval
#print axioms ZhangLS.Spec.proposition141_small_product_conductor_lt_fourth
#print axioms ZhangLS.Spec.proposition141_uniform_fourth_lt_T
#print axioms ZhangLS.Spec.proposition141_small_product_inducer_prime_bound
#print axioms ZhangLS.Spec.proposition141ProductPrimeSum
#print axioms ZhangLS.Spec.proposition141_actual_prime_sum_eq_inducer
#print axioms ZhangLS.Spec.proposition141_small_actual_product_prime_bound
#print axioms ZhangLS.Spec.proposition141ShiftedPrimeSum
#print axioms ZhangLS.Spec.proposition141_shifted_prime_weight_identity
#print axioms ZhangLS.Spec.proposition141_real_shift_weight_mono
#print axioms ZhangLS.Spec.proposition141_shifted_finite_prime_budget
#print axioms ZhangLS.Spec.proposition141_complex_shift_parameters
#print axioms ZhangLS.Spec.proposition141_complex_shift_weight_bound
#print axioms ZhangLS.Spec.proposition141_prime_window_sum_eq
#print axioms ZhangLS.Spec.proposition141_actual_shifted_prime_weight_budget
#print axioms ZhangLS.Spec.proposition141_shifted_height_margin
#print axioms ZhangLS.Spec.proposition141_uniform_shifted_primitive_prime_absolute_bound
#print axioms ZhangLS.Spec.proposition141_uniform_shifted_primitive_prime_normalized_bound
#print axioms ZhangLS.Spec.proposition141ShiftedProductPrimeSum
#print axioms ZhangLS.Spec.proposition141_shifted_product_prime_sum_eq_inducer
#print axioms ZhangLS.Spec.proposition141_uniform_small_shifted_product_prime_bound
#print axioms ZhangLS.Spec.lemma54EighthConstant
#print axioms ZhangLS.Spec.lemma54EighthMajorant
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_constant_pos
#print axioms ZhangLS.Spec.lemma54_eighth_contour_factor_pow_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_majorant_factorization
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_majorant_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_kernel_norm_real
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_kernel_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_majorant_integral_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_ray_norm_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_kernel_norm_left
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_left_tail_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_vertical_point_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_vertical_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_left_vertical_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_ray_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_right_ray_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_majorant_tendsto_zero
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_right_vertical_tendsto_zero
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_infinite_contour_shift
#print axioms ZhangLS.Spec.lemma54EighthDerivativeTail
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_large_range_estimate
#print axioms ZhangLS.Spec.lemma54EighthIntegral
#print axioms ZhangLS.Spec.lemma54_eighth_integral_zero
#print axioms ZhangLS.Spec.lemma54_eighth_integral_zero_actual
#print axioms ZhangLS.Spec.lemma54_eighth_kernel_hasDerivAt
#print axioms ZhangLS.Spec.lemma54_eighth_integral_hasDerivAt
#print axioms ZhangLS.Spec.lemma54_eighth_integral_continuous
#print axioms ZhangLS.Spec.lemma54_eighth_integral_norm_bound
#print axioms ZhangLS.Spec.lemma54_eighth_integral_large_range
#print axioms ZhangLS.Spec.lemma54_eighth_integral_isBigO_atTop
#print axioms ZhangLS.Spec.lemma54_eighth_integral_isBigO_at_zero
#print axioms ZhangLS.Spec.lemma54_eighth_integral_mellin_convergent
#print axioms ZhangLS.Spec.lemma54_eighth_integral_boundary_products
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_step
#print axioms ZhangLS.Spec.lemma54_eighth_zero_mellin_actual
#print axioms ZhangLS.Spec.lemma54EighthMoment
#print axioms ZhangLS.Spec.lemma54EighthGlobalConstant
#print axioms ZhangLS.Spec.lemma54EighthLogConstant
#print axioms ZhangLS.Spec.lemma54EighthExpConstant
#print axioms ZhangLS.Spec.lemma54EighthMomentConstant
#print axioms ZhangLS.Spec.lemma54_eighth_constants_pos
#print axioms ZhangLS.Spec.lemma54_eighth_moment_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_global_norm_bound
#print axioms ZhangLS.Spec.lemma54_eighth_small_moment_bound
#print axioms ZhangLS.Spec.lemma54EighthMomentEnvelope
#print axioms ZhangLS.Spec.lemma54_eighth_envelope_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_envelope_nonneg
#print axioms ZhangLS.Spec.lemma54_eighth_envelope_bound
#print axioms ZhangLS.Spec.lemma54_eighth_envelope_integral_bound
#print axioms ZhangLS.Spec.lemma54_eighth_moment_uniform_bound
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_iteration
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_integral_identity
#print axioms ZhangLS.Spec.lemma54_eighth_norm_shift_le
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_bound_by_moment
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_line_bound
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_frequency_bound
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_explicit_threshold
#print axioms ZhangLS.Spec.lemma54_eighth_arctan_le_self
#print axioms ZhangLS.Spec.lemma54_eighth_positive_cauchy_tail
#print axioms ZhangLS.Spec.lemma54_eighth_negative_cauchy_tail
#print axioms ZhangLS.Spec.lemma54_eighth_weight_le_cauchy
#print axioms ZhangLS.Spec.lemma54_eighth_weight_tail_point
#print axioms ZhangLS.Spec.lemma54_eighth_bounded_weight_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_window_and_tail
#print axioms ZhangLS.Spec.lemma54_eighth_actual_line_continuous
#print axioms ZhangLS.Spec.lemma54_eighth_actual_product_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_actual_window_and_tail
#print axioms ZhangLS.Spec.proposition141_small_shift_power_norm
#print axioms ZhangLS.Spec.proposition141_shifted_product_prime_continuous
#print axioms ZhangLS.Spec.proposition141_shifted_product_prime_global_bound
#print axioms ZhangLS.Spec.proposition141ActualPrimeMellinIntegral
#print axioms ZhangLS.Spec.proposition141_uniform_small_product_mellin_integral_bound
#print axioms ZhangLS.Spec.Proposition141KappaBound
#print axioms ZhangLS.Spec.Proposition141AdmissibleSequence
#print axioms ZhangLS.Spec.proposition141Indices
#print axioms ZhangLS.Spec.proposition141KappaSeries
#print axioms ZhangLS.Spec.proposition141Polynomial
#print axioms ZhangLS.Spec.proposition141SegmentIntegral
#print axioms ZhangLS.Spec.proposition141Integral
#print axioms ZhangLS.Spec.proposition141ShiftWeight
#print axioms ZhangLS.Spec.proposition141ThetaTwo
#print axioms ZhangLS.Spec.proposition141AmbientMean
#print axioms ZhangLS.Spec.proposition141InnerMain
#print axioms ZhangLS.Spec.proposition141MainTerm
#print axioms ZhangLS.Spec.Proposition141Target
#print axioms ZhangLS.Spec.proposition141_mem_indices
#print axioms ZhangLS.Spec.proposition141_segment_real_part
#print axioms ZhangLS.Spec.proposition141_zero_shift
#print axioms ZhangLS.Spec.proposition141_kappa_series_summable
#print axioms ZhangLS.Spec.proposition141_nonzero_support
#print axioms ZhangLS.Spec.proposition141_nonzero_product_indices
#print axioms ZhangLS.Spec.proposition141_omitted_coefficient_zero
#print axioms ZhangLS.Spec.proposition141_uniform_t0_le_D
#print axioms ZhangLS.Spec.proposition141_uniform_support_modulus_bound
#print axioms ZhangLS.Spec.proposition141_supported_modulus_coprime_prime
#print axioms ZhangLS.Spec.proposition141_t0_log_bounds
#print axioms ZhangLS.Spec.proposition141_t0_shift_norm
#print axioms ZhangLS.Spec.proposition141_prime_t0_shift_factor
#print axioms ZhangLS.Spec.proposition141_prime_t0_shift_norm
#print axioms ZhangLS.Spec.proposition141_prime_t0_shift_sum
#print axioms ZhangLS.Spec.proposition141_prime_windows_equal
#print axioms ZhangLS.Spec.proposition141_actual_prime_masses_equal
#print axioms ZhangLS.Spec.proposition141_multichoose_five_square_le
#print axioms ZhangLS.Spec.proposition141_tau_five_square_le
#print axioms ZhangLS.Spec.proposition141_tau_five_square_harmonic_bound
#print axioms ZhangLS.Spec.proposition141_bounded_coefficient_harmonic_energy
#print axioms ZhangLS.Spec.proposition141_bounded_coefficient_interval_energy
#print axioms ZhangLS.Spec.proposition71_actual_delta_vertical_integrable
#print axioms ZhangLS.Spec.proposition71_actual_delta_mellin_inversion
#print axioms ZhangLS.Spec.proposition71_actual_scaled_delta_mellin
#print axioms ZhangLS.Spec.proposition71_inverse_mellin_integrand_integrable
#print axioms ZhangLS.Spec.proposition71_scaled_mellin_power
#print axioms ZhangLS.Spec.proposition71_extracted_scale_norm
#print axioms ZhangLS.Spec.proposition71_actual_finite_mellin_sum
#print axioms ZhangLS.Spec.proposition141ActualShiftedPrimeKernel
#print axioms ZhangLS.Spec.proposition141_actual_shifted_prime_mellin_identity
#print axioms ZhangLS.Spec.proposition141_actual_shifted_prime_kernel_integral_bound
#print axioms ZhangLS.Spec.proposition141_uniform_small_shifted_prime_kernel_bound
#print axioms ZhangLS.Spec.proposition71SplitPairs
#print axioms ZhangLS.Spec.proposition71_split_mem
#print axioms ZhangLS.Spec.proposition71_split_gcd
#print axioms ZhangLS.Spec.proposition71_split_injective
#print axioms ZhangLS.Spec.proposition71_split_surjective
#print axioms ZhangLS.Spec.proposition71_divisor_pair_split
#print axioms ZhangLS.Spec.proposition71_kappa_convolution_split
#print axioms ZhangLS.Spec.proposition71_nat_divisor_pair_split
#print axioms ZhangLS.Spec.proposition71_convolution_submultiplicative
#print axioms ZhangLS.Spec.proposition71_tau_submultiplicative
#print axioms ZhangLS.Spec.proposition71_reciprocal_totient_le_tau
#print axioms ZhangLS.Spec.proposition71_reciprocal_product_totient
#print axioms ZhangLS.Spec.proposition141_kappa_three_factor_bound
#print axioms ZhangLS.Spec.proposition141_kappa_finite_harmonic_bound
#print axioms ZhangLS.Spec.proposition141FiniteSmallCharacterSum
#print axioms ZhangLS.Spec.proposition141_uniform_finite_small_character_sum_bound
#print axioms ZhangLS.Spec.proposition141_actual_kappa_interval_energy
#print axioms ZhangLS.Spec.proposition141_actual_weighted_kappa_mean
#print axioms ZhangLS.Spec.proposition141_actual_shifted_prime_energy
#print axioms ZhangLS.Spec.proposition141_actual_weighted_prime_mean
#print axioms ZhangLS.Spec.proposition71_weighted_cauchy
#print axioms ZhangLS.Spec.proposition71_weighted_primitive_cauchy
#print axioms ZhangLS.Spec.proposition71_weighted_primitive_cauchy_bound
#print axioms ZhangLS.Spec.proposition141_actual_weighted_bilinear_mean
#print axioms ZhangLS.Spec.proposition71_tau_harmonic_bound
#print axioms ZhangLS.Spec.proposition71_small_conductor_weight_sum
#print axioms ZhangLS.Spec.proposition71_quarter_split_small_budget
#print axioms ZhangLS.Spec.proposition71_quarter_split_large_budget
#print axioms ZhangLS.Spec.proposition71_primitive_character_count
#print axioms ZhangLS.Spec.proposition71_three_halves_eq_mul_sqrt
#print axioms ZhangLS.Spec.proposition71_counted_totient_weight
#print axioms ZhangLS.Spec.proposition71_sqrt_conductor_sum
#print axioms ZhangLS.Spec.proposition71_counted_conductor_weight_sum
#print axioms ZhangLS.Spec.proposition141_multichoose_six_le_pow
#print axioms ZhangLS.Spec.proposition141_multichoose_six_prime_bound
#print axioms ZhangLS.Spec.proposition141_tau_six_linear_bound
#print axioms ZhangLS.Spec.proposition141_divisor_tau_five_sum
#print axioms ZhangLS.Spec.proposition141_divisor_tau_five_budget
#print axioms ZhangLS.Spec.proposition141_conductor_congruence
#print axioms ZhangLS.Spec.proposition141SmallConductorModuli
#print axioms ZhangLS.Spec.proposition141_small_counted_weight_sum
#print axioms ZhangLS.Spec.proposition141_eighth_counted_tail_identity
#print axioms ZhangLS.Spec.proposition141_eighth_gauss_tail_identity
#print axioms ZhangLS.Spec.proposition141_eighth_divisor_tail_budget
#print axioms ZhangLS.Spec.divisorPower_multichoose_le_pow
#print axioms ZhangLS.Spec.divisorPower_multichoose_prime_bound
#print axioms ZhangLS.Spec.divisorPower_tau_linear_bound
#print axioms ZhangLS.Spec.divisorPower_multichoose_six_square
#print axioms ZhangLS.Spec.divisorPower_tau_six_square
#print axioms ZhangLS.Spec.divisorPower_tau_six_sqrt
#print axioms ZhangLS.Spec.divisorPower_divisor_tau_five_sqrt
#print axioms ZhangLS.Spec.proposition71_positive_ratio_cpow
#print axioms ZhangLS.Spec.proposition71_finite_mellin_integrand_integrable
#print axioms ZhangLS.Spec.proposition71DoubleMellinIntegrand
#print axioms ZhangLS.Spec.proposition71_double_mellin_integrand_expansion
#print axioms ZhangLS.Spec.proposition71_double_mellin_integrand_integrable
#print axioms ZhangLS.Spec.proposition71_actual_double_mellin_sum
#print axioms ZhangLS.Spec.proposition141DoubleMellinIntegrand
#print axioms ZhangLS.Spec.proposition141_double_mellin_integrand_eq
#print axioms ZhangLS.Spec.proposition141_double_mellin_integrable
#print axioms ZhangLS.Spec.proposition141_actual_double_mellin_identity
#print axioms ZhangLS.Spec.inducedGauss_sum_zmod_eq_range
#print axioms ZhangLS.Spec.inducedGauss_sum_range_multiples
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_nat
#print axioms ZhangLS.Spec.inducedGauss_mobius_indicator
#print axioms ZhangLS.Spec.inducedGauss_mobius_indicator_divisors
#print axioms ZhangLS.Spec.inducedGauss_scaled_additive
#print axioms ZhangLS.Spec.coprimeGaussResidueEquiv
#print axioms ZhangLS.Spec.coprimeGauss_residue_coordinates
#print axioms ZhangLS.Spec.coprimeGauss_residue_nat
#print axioms ZhangLS.Spec.coprimeGauss_additive_factorization
#print axioms ZhangLS.Spec.coprimeGauss_real_twist_values
#print axioms ZhangLS.Spec.coprimeGauss_real_twist_formula
#print axioms ZhangLS.Spec.inducedGaussInflation
#print axioms ZhangLS.Spec.inducedGauss_inflation_zero
#print axioms ZhangLS.Spec.inducedGauss_inflation_one
#print axioms ZhangLS.Spec.inducedGauss_inflation_formula
#print axioms ZhangLS.Spec.inducedGauss_coprime_sum_mobius
#print axioms ZhangLS.Spec.inducedGauss_divisor_inner
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_formula
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_formula_dvd
#print axioms ZhangLS.Spec.inducedGauss_conductor_formula
#print axioms ZhangLS.Spec.inducedGauss_level_one_value
#print axioms ZhangLS.Spec.inducedGauss_primitive_norm
#print axioms ZhangLS.Spec.inducedGauss_mobius_norm_le_one
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_norm_le
#print axioms ZhangLS.Spec.inducedGauss_norm_le_sqrt_conductor
#print axioms ZhangLS.Spec.inducedGauss_inverse_norm_le_sqrt_conductor
#print axioms ZhangLS.Spec.inducedGauss_nonprincipal_conductor_gt_one
#print axioms ZhangLS.Spec.proposition71_prime_primitive_iff
#print axioms ZhangLS.Spec.proposition71_full_gauss_average
#print axioms ZhangLS.Spec.proposition71_principal_gauss
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_average
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_error
#print axioms ZhangLS.Spec.proposition71_gauss_average_nonunit
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_average_all
#print axioms ZhangLS.Spec.coprimeGauss_prime_average_summand
#print axioms ZhangLS.Spec.coprimeGauss_full_prime_average
#print axioms ZhangLS.Spec.coprimeGauss_primitive_prime_average
#print axioms ZhangLS.Spec.coprimeGauss_primitive_prime_average_error
#print axioms ZhangLS.Spec.coprimeGauss_primitive_average_nonunit
#print axioms ZhangLS.Spec.inducedGauss_principal_value
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_neg_nat
#print axioms ZhangLS.Spec.inducedGauss_phase_product
#print axioms ZhangLS.Spec.inducedGauss_real_changeLevel_inv
#print axioms ZhangLS.Spec.inducedGauss_real_phase_product
#print axioms ZhangLS.Spec.inducedGauss_totient_denominator
#print axioms ZhangLS.Spec.inducedGauss_coprime_filter
#print axioms ZhangLS.Spec.inducedGauss_real_square
#print axioms ZhangLS.Spec.additiveReciprocity_stdAddChar
#print axioms ZhangLS.Spec.additiveReciprocity_product_phase
#print axioms ZhangLS.Spec.additiveReciprocity_delta
#print axioms ZhangLS.Spec.proposition71_large_log_exponent
#print axioms ZhangLS.Spec.proposition71_large_power_exponent
#print axioms ZhangLS.Spec.proposition71_tail_exp_factor
#print axioms ZhangLS.Spec.proposition71LargeDeltaTailConstant
#print axioms ZhangLS.Spec.proposition71_large_delta_tail_constant_pos
#print axioms ZhangLS.Spec.proposition71_actual_large_delta_tail
#print axioms ZhangLS.Spec.proposition141_tau_five_square_summable
#print axioms ZhangLS.Spec.proposition141TauFiveSquareMass
#print axioms ZhangLS.Spec.proposition141_tau_five_square_mass_nonneg
#print axioms ZhangLS.Spec.proposition141_dilated_kappa_square_summable
#print axioms ZhangLS.Spec.proposition141_dilated_kappa_square_sum
#print axioms ZhangLS.Spec.proposition141_scaled_large_delta_tail
#print axioms ZhangLS.Spec.proposition141DilatedDeltaTailTerm
#print axioms ZhangLS.Spec.proposition141_dilated_delta_tail_majorant
#print axioms ZhangLS.Spec.proposition141_dilated_delta_tail_summable
#print axioms ZhangLS.Spec.proposition141_dilated_delta_tail_bound
#print axioms ZhangLS.Spec.tauDirichlet_lseries_value
#print axioms ZhangLS.Spec.tauDirichlet_square_mass
#print axioms ZhangLS.Spec.tauDirichlet_five_square_mass_le
#print axioms ZhangLS.Spec.proposition141_tau_five_square_mass_eq
#print axioms ZhangLS.Spec.proposition141_tau_five_square_mass_le
#print axioms ZhangLS.Spec.proposition141_dilated_delta_tail_explicit_bound
#print axioms ZhangLS.Spec.proposition141_prime_tail_shift_norm
#print axioms ZhangLS.Spec.proposition141_prime_card_le_mass
#print axioms ZhangLS.Spec.proposition141_prime_summed_infinite_tail
#print axioms ZhangLS.Spec.proposition141_prime_tail_interchange
#print axioms ZhangLS.Spec.proposition141_dilated_delta_series_summable
#print axioms ZhangLS.Spec.proposition141_coprime_delta_series_summable
#print axioms ZhangLS.Spec.proposition141_original_main_series_summable
#print axioms ZhangLS.Spec.proposition141_large_tail_prime_power_absorption
#print axioms ZhangLS.Spec.proposition141_actual_tail_prime_power_absorption
#print axioms ZhangLS.Spec.proposition141_actual_large_tail_decay
#print axioms ZhangLS.Spec.proposition141_actual_tail_polynomial_rate
#print axioms ZhangLS.Spec.divisorPower_multichoose_square
#print axioms ZhangLS.Spec.divisorPower_tau_square
#print axioms ZhangLS.Spec.divisorPower_tau_fourth
#print axioms ZhangLS.Spec.divisorPowerQuarterConstant
#print axioms ZhangLS.Spec.divisorPower_quarter_constant_pos
#print axioms ZhangLS.Spec.divisorPower_tau_quarter
#print axioms ZhangLS.Spec.divisorPower_divisor_tau_five_quarter
#print axioms ZhangLS.Spec.proposition141_off_diagonal_not_dvd
#print axioms ZhangLS.Spec.proposition141_lift_ne_chi_of_not_dvd
#print axioms ZhangLS.Spec.proposition141_off_diagonal_inducer_admissible
#print axioms ZhangLS.Spec.proposition141_off_diagonal_product_conductor_le
#print axioms ZhangLS.Spec.proposition141_off_diagonal_inducer_eval
#print axioms ZhangLS.Spec.proposition141_small_off_diagonal_inducer_prime_bound
#print axioms ZhangLS.Spec.proposition141_small_supported_product_prime_bound
#print axioms ZhangLS.Spec.proposition141_off_diagonal_actual_prime_sum_eq_inducer
#print axioms ZhangLS.Spec.proposition141_small_actual_off_diagonal_prime_bound
#print axioms ZhangLS.Spec.proposition141_general_hermitian_orthogonality
#print axioms ZhangLS.Spec.proposition141_general_gauss_average
#print axioms ZhangLS.Spec.proposition141_additive_phase_character_expansion
#print axioms ZhangLS.Spec.proposition141_nonunit_character_phase_zero
#print axioms ZhangLS.Spec.proposition141_prime_kernel_changeLevel
#print axioms ZhangLS.Spec.proposition141_uniform_off_diagonal_small_kernel_bound
#print axioms ZhangLS.Spec.proposition141_supported_off_diagonal_common_modulus
#print axioms ZhangLS.Spec.proposition141_uniform_supported_off_diagonal_small_kernel_bound

#print ZhangLS.Spec.Proposition141Target
