import ZhangLS.Spec.Proposition71ArithmeticFactors
import ZhangLS.Spec.Proposition71CharacterConductorWeights
import ZhangLS.Spec.Proposition71CoefficientEnergy
import ZhangLS.Spec.Proposition71Conductor
import ZhangLS.Spec.Proposition71ConductorAggregateAlgebra
import ZhangLS.Spec.Proposition71ConductorAggregateOrder
import ZhangLS.Spec.Proposition71ConductorModulusRestriction
import ZhangLS.Spec.Proposition71ConductorWeights
import ZhangLS.Spec.Proposition71ConvolutionSplit
import ZhangLS.Spec.Proposition71DeltaGaussianTail
import ZhangLS.Spec.Proposition71DeltaLargeTail
import ZhangLS.Spec.Proposition71DeltaLocalization
import ZhangLS.Spec.Proposition71DivisorWeights
import ZhangLS.Spec.Proposition71DyadicCoefficientEnergy
import ZhangLS.Spec.Proposition71DyadicCover
import ZhangLS.Spec.Proposition71DyadicMellinMean
import ZhangLS.Spec.Proposition71DyadicPrimeMean
import ZhangLS.Spec.Proposition71DyadicSigmaBound
import ZhangLS.Spec.Proposition71ExceptionalLittleO
import ZhangLS.Spec.Proposition71ExceptionalMoments
import ZhangLS.Spec.Proposition71FullConductorAggregate
import ZhangLS.Spec.Proposition71FullLargeConductor
import ZhangLS.Spec.Proposition71FullSigmaBlock
import ZhangLS.Spec.Proposition71FullSmallConductor
import ZhangLS.Spec.Proposition71GaussAverage
import ZhangLS.Spec.Proposition71LargeConductorAggregate
import ZhangLS.Spec.Proposition71LargeConductorSaving
import ZhangLS.Spec.Proposition71LargeConductorWeights
import ZhangLS.Spec.Proposition71LargeLArgument
import ZhangLS.Spec.Proposition71LargeLPrimeKernel
import ZhangLS.Spec.Proposition71LargeLTailAggregate
import ZhangLS.Spec.Proposition71LocalizedDyadicSaving
import ZhangLS.Spec.Proposition71LocalizedGeometry
import ZhangLS.Spec.Proposition71LocalizedSigmaSquare
import ZhangLS.Spec.Proposition71MellinDoubleSum
import ZhangLS.Spec.Proposition71MellinFiniteSum
import ZhangLS.Spec.Proposition71MellinInversion
import ZhangLS.Spec.Proposition71MellinPrimeBound
import ZhangLS.Spec.Proposition71Mobius
import ZhangLS.Spec.Proposition71Objects
import ZhangLS.Spec.Proposition71OffLocalAggregate
import ZhangLS.Spec.Proposition71OffLocalMajorant
import ZhangLS.Spec.Proposition71OffLocalTail
import ZhangLS.Spec.Proposition71OriginalConductorLittleO
import ZhangLS.Spec.Proposition71OriginalLargeConductor
import ZhangLS.Spec.Proposition71OriginalSmallConductor
import ZhangLS.Spec.Proposition71OuterTailBudget
import ZhangLS.Spec.Proposition71Phase
import ZhangLS.Spec.Proposition71PhaseSummation
import ZhangLS.Spec.Proposition71QuarterConductorSaving
import ZhangLS.Spec.Proposition71SigmaLargeLTail
import ZhangLS.Spec.Proposition71SigmaMellin
import ZhangLS.Spec.Proposition71SigmaSeries
import ZhangLS.Spec.Proposition71SigmaTruncation
import ZhangLS.Spec.Proposition71SmallConductorAggregate
import ZhangLS.Spec.Proposition71SmallConductorIntegral
import ZhangLS.Spec.Proposition71SmallConductorKernel
import ZhangLS.Spec.Proposition71SmallSigma
import ZhangLS.Spec.Proposition71Support
import ZhangLS.Spec.Proposition71TailScalarBudget
import ZhangLS.Spec.Proposition71TauDirichlet
import ZhangLS.Spec.Proposition71WeightedCauchy
import ZhangLS.Spec.Proposition71WeightedHeightTail

set_option autoImplicit false
open ZhangLS.Spec Complex
open scoped Classical

example : Proposition71Target ↔
    ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
      ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∃ C : ℝ, 0<C ∧
        ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
          ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D,
            NormalizedAssumptionA χ → ∀ a₁ a₂ : ℕ → ℂ,
              Lemma81AdmissibleSequence D B₁ a₁ → Lemma81AdmissibleSequence D B₂ a₂ →
              ‖lemma81ThetaOne χ c a₁ a₂-proposition71MainTerm D c a₁ a₂‖ ≤
                C*proposition71ErrorScale D c a₁ a₂+ε*lemma33ActualPrimeMass D := Iff.rfl

example (D : ℕ) (B : ℝ) (a : ℕ → ℂ) : Lemma81AdmissibleSequence D B a ↔
    (∀ n : ℕ, ‖a n‖ ≤ B) ∧ ∀ n : ℕ,
      lemma23PaperP D * lemma56PaperT D^(-2 : ℤ) ≤ (n : ℝ) → a n=0 := Iff.rfl

example {D : ℕ} (χ : RealPrimitiveCharacter D) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    lemma81ThetaOne χ c a₁ a₂ =
      ∑ ψ ∈ lemma81GoodFamily χ, lemma81NormalizedSegmentIntegral D 1
        (fun s => lemma81ActualC D c ψ.2 s * lemma81Polynomial D a₁ ψ.2 s *
          lemma81Polynomial D a₂ ψ.2⁻¹ (1-s) * lemma81Omega D s) := rfl

example (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    proposition71MainTerm D c a₁ a₂ =
      (lemma44PaperAlpha D : ℂ)⁻¹ *
        ((1/2 : ℂ)*proposition71ArithmeticSum D c 0 a₁ a₂+
          2*proposition71ArithmeticSum D c 1 a₁ a₂+
          (3/2 : ℂ)*proposition71ArithmeticSum D c 2 a₁ a₂)*
        (lemma33ActualPrimeMass D : ℂ) := rfl

example (D : ℕ) (c : ℝ) (a₁ a₂ : ℕ → ℂ) :
    proposition71ErrorScale D c a₁ a₂ =
      lemma33ActualPrimeMass D*lemma23PaperL D^2*
        ∑ j : Fin 3, ‖proposition71ArithmeticSum D c j a₁ a₂‖ := rfl


/-- Uniform original (7.5), with the actual bad family and actual polynomials expanded. -/
example : ∀ B₁ B₂ : ℝ, 0<B₁ → 0<B₂ → ∀ ε : ℝ, 0<ε →
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ → ∀ c : ℝ,
        ∀ a₁ a₂ : ℕ → ℂ, Lemma81AdmissibleSequence D B₁ a₁ →
          Lemma81AdmissibleSequence D B₂ a₂ → ∀ s : ℂ, s.re=1/2 →
            (∑ ψ∈proposition21ActualPsi2Family χ,
              ‖proposition71TruncatedKappaPolynomial D c a₁ ψ.2 s‖*
                ‖lemma81Polynomial D a₂ ψ.2⁻¹ (1-s)‖)≤ε*lemma33ActualPrimeMass D :=
  proposition71_original_seven_five


/-- Original closed localization endpoints and genuine coprimality. -/
example {D l h : ℕ} {R : ℝ} :
    l∈proposition71LocalizedIndices D R h ↔
      0<l ∧ proposition71LocalScale D R h/3≤(l : ℝ) ∧
        (l : ℝ)≤4*proposition71LocalScale D R h ∧ l.Coprime h :=
  proposition71_mem_localized_indices

example (D h : ℕ) (R : ℝ) : 0∉proposition71LocalizedIndices D R h := by
  rw [proposition71_mem_localized_indices]
  simp

example (R : ℝ) : (1 : ℕ)∉primitiveDyadicModuli R := by
  simp [mem_primitiveDyadicModuli]

example : (2 : ℕ)∈primitiveDyadicModuli 2 := by
  norm_num [mem_primitiveDyadicModuli]

example : (4 : ℕ)∉primitiveDyadicModuli 2 := by
  norm_num [mem_primitiveDyadicModuli]

/-- The exact two-finite-sum Mellin object handles an empty coefficient range. -/
example (D : ℕ) (σ h r : ℝ) (P : Finset ℕ) (b a : ℕ → ℂ) (t : ℝ) :
    proposition71DoubleMellinIntegrand D σ h r ∅ P b a t=0 := by
  simp [proposition71DoubleMellinIntegrand]

/-- Original β₃ with its actual finite localized l and prime sums. -/
example {r : ℕ} (D : ℕ) (c : ℝ) (a : ℕ → ℂ) (R : ℝ)
    (h d : ℕ) (θ : DirichletCharacter ℂ r) :
    proposition71OriginalSigmaStar D c a R h d θ=
      ∑ l∈proposition71LocalizedIndices D R h,
        (lemma83Kappa (lemma83PaperBeta D c)*proposition71ArithmeticSequence a) (d*l)*θ (l : ZMod r)*
          ∑ p∈lemma56PaperPrimes D, (p : ℂ)^lemma52PaperBetaThree D c*θ⁻¹ (p : ZMod r)*
            lemma53PaperDelta D ((l : ℝ)/((p : ℝ)*(h : ℝ)*(r : ℝ))) := rfl

/-- The final localized statement has no sequence-dependent or c-dependent threshold. -/
example : ∀ B : ℝ, 0<B → ∀ ε : ℝ, 0<ε → ∃ D₀ : ℕ, 2≤D₀ ∧
    ∀ D : ℕ, D₀≤D → ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
      ∀ c : ℝ, ∀ a : ℕ → ℂ, Lemma81AdmissibleSequence D B a →
        proposition71OriginalLocalizedLargeAggregate D c a≤ε*lemma56PrimeMass D :=
  proposition71_original_localized_large_little_o


/-- The full original (7.13) right-hand sum, with no truncated or residual σ. -/
example (D : ℕ) (c : ℝ) (a : ℕ → ℂ) :
    proposition71OriginalConductorAggregate D c a=
      ∑ d∈Finset.Icc 1 ⌊lemma23PaperP D⌋₊, ∑ h∈Finset.Icc 1 ⌊lemma23PaperP D⌋₊,
        ∑ r∈Finset.Icc 2 ⌊lemma23PaperP D⌋₊,
          if ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D then
            ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹*
              ∑ θ∈(Finset.univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
                ‖proposition71OriginalSigmaSeries D c a h d θ‖ else 0 := rfl

example {r : ℕ} (D : ℕ) (c b : ℝ) (a : ℕ → ℂ) (h d : ℕ)
    (θ : DirichletCharacter ℂ r) : proposition71SigmaTerm D c b a h d θ 0=0 := by
  simp [proposition71SigmaTerm]

/-- At l=P², the strict large-l tail omits the endpoint. -/
example {D r l : ℕ} (c b : ℝ) (a : ℕ → ℂ) (h d : ℕ) (θ : DirichletCharacter ℂ r)
    (hl : (l : ℝ)=lemma23PaperP D^2) :
    proposition71SigmaLargeLTerm D c b a h d θ l=0 := by
  simp [proposition71SigmaLargeLTerm,hl]

/-- The localization complement literally omits every member of the closed interval. -/
example {D r l : ℕ} (c b : ℝ) (a : ℕ → ℂ) (R : ℝ) (h d : ℕ) (θ : DirichletCharacter ℂ r)
    (hl : l∈proposition71LocalizedIndices D R h) :
    proposition71SigmaOffLocalTerm D c b a R h d θ l=0 := by
  simp only [proposition71SigmaOffLocalTerm,if_pos hl]

example : proposition71TauFiveQuadraticMass=
    ∑' n : ℕ, (lemma34Tau 5 n : ℝ)/(n : ℝ)^2 := rfl

/-- Full uniform original-phase conductor majorant, not merely its localized version. -/
example : ∀ c : ℝ, 0<c → ∀ B : ℝ, 0<B → ∀ ε : ℝ, 0<ε →
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ χ : RealPrimitiveCharacter D, NormalizedAssumptionA χ →
        ∀ a : ℕ → ℂ, Lemma81AdmissibleSequence D B a →
          proposition71OriginalConductorAggregate D c a≤ε*lemma56PrimeMass D :=
  proposition71_original_seven_thirteen_majorant_little_o

#print axioms ZhangLS.Spec.proposition71_prime_support_union
#print axioms ZhangLS.Spec.proposition71_lambda_factorization
#print axioms ZhangLS.Spec.proposition71_xi_factor_extraction
#print axioms ZhangLS.Spec.proposition71_primitive_character_count
#print axioms ZhangLS.Spec.proposition71_three_halves_eq_mul_sqrt
#print axioms ZhangLS.Spec.proposition71_counted_totient_weight
#print axioms ZhangLS.Spec.proposition71_sqrt_conductor_sum
#print axioms ZhangLS.Spec.proposition71_counted_conductor_weight_sum
#print axioms ZhangLS.Spec.proposition71_convolution_majorant
#print axioms ZhangLS.Spec.proposition71_power_coefficient_majorant
#print axioms ZhangLS.Spec.proposition71_moebius_coefficient_majorant
#print axioms ZhangLS.Spec.proposition71_actual_kappa_le_tau_four
#print axioms ZhangLS.Spec.proposition71ArithmeticSequence
#print axioms ZhangLS.Spec.proposition71_arithmetic_sequence_positive
#print axioms ZhangLS.Spec.proposition71_actual_convolution_le_tau_five
#print axioms ZhangLS.Spec.proposition71_multichoose_five_square_le_twentyfive
#print axioms ZhangLS.Spec.proposition71_tau_five_square_le_twentyfive
#print axioms ZhangLS.Spec.proposition71_tau_five_square_harmonic_sum
#print axioms ZhangLS.Spec.proposition71_actual_convolution_harmonic_energy
#print axioms ZhangLS.Spec.proposition71_nonprincipal_conductor_gt_one
#print axioms ZhangLS.Spec.proposition71_equal_nat_evaluations_changeLevel
#print axioms ZhangLS.Spec.proposition71_small_primitive_distinct
#print axioms ZhangLS.Spec.proposition71_actual_inducer_admissible
#print axioms ZhangLS.Spec.proposition71_small_conductor_lt_T
#print axioms ZhangLS.Spec.proposition71_small_actual_inducer_prime_bound
#print axioms ZhangLS.Spec.proposition71ConductorNormAggregate
#print axioms ZhangLS.Spec.proposition71_conductor_norm_aggregate_nonneg
#print axioms ZhangLS.Spec.proposition71_conductor_norm_aggregate_bound
#print axioms ZhangLS.Spec.proposition71_conductor_aggregate_mono
#print axioms ZhangLS.Spec.proposition71_conductor_aggregate_le_add
#print axioms ZhangLS.Spec.proposition71_conductor_aggregate_predicate_split
#print axioms ZhangLS.Spec.proposition71_conductor_aggregate_cover
#print axioms ZhangLS.Spec.proposition71_conductor_aggregate_upper_restrict
#print axioms ZhangLS.Spec.proposition71_tau_harmonic_bound
#print axioms ZhangLS.Spec.proposition71_small_conductor_weight_sum
#print axioms ZhangLS.Spec.proposition71_quarter_split_small_budget
#print axioms ZhangLS.Spec.proposition71_quarter_split_large_budget
#print axioms ZhangLS.Spec.proposition71SplitPairs
#print axioms ZhangLS.Spec.proposition71_split_mem
#print axioms ZhangLS.Spec.proposition71_split_gcd
#print axioms ZhangLS.Spec.proposition71_split_injective
#print axioms ZhangLS.Spec.proposition71_split_surjective
#print axioms ZhangLS.Spec.proposition71_divisor_pair_split
#print axioms ZhangLS.Spec.proposition71_kappa_convolution_split
#print axioms ZhangLS.Spec.proposition71_gaussian_clearance_budget
#print axioms ZhangLS.Spec.proposition71_actual_gaussian_offcenter
#print axioms ZhangLS.Spec.proposition71OffCenterDeltaConstant
#print axioms ZhangLS.Spec.proposition71_offcenter_delta_constant_pos
#print axioms ZhangLS.Spec.proposition71_actual_delta_offcenter
#print axioms ZhangLS.Spec.proposition71_large_log_exponent
#print axioms ZhangLS.Spec.proposition71_large_power_exponent
#print axioms ZhangLS.Spec.proposition71_tail_exp_factor
#print axioms ZhangLS.Spec.proposition71LargeDeltaTailConstant
#print axioms ZhangLS.Spec.proposition71_large_delta_tail_constant_pos
#print axioms ZhangLS.Spec.proposition71_actual_large_delta_tail
#print axioms ZhangLS.Spec.proposition71_paper_prime_le_three_halves_P
#print axioms ZhangLS.Spec.proposition71_offlocalized_clearance
#print axioms ZhangLS.Spec.proposition71_actual_offlocalized_delta
#print axioms ZhangLS.Spec.proposition71_nat_divisor_pair_split
#print axioms ZhangLS.Spec.proposition71_convolution_submultiplicative
#print axioms ZhangLS.Spec.proposition71_tau_submultiplicative
#print axioms ZhangLS.Spec.proposition71_reciprocal_totient_le_tau
#print axioms ZhangLS.Spec.proposition71_reciprocal_product_totient
#print axioms ZhangLS.Spec.proposition71_actual_dyadic_coefficient_energy
#print axioms ZhangLS.Spec.proposition71_actual_weighted_dyadic_kappa_mean
#print axioms ZhangLS.Spec.proposition71_actual_localized_kappa_mean
#print axioms ZhangLS.Spec.proposition71DyadicScale
#print axioms ZhangLS.Spec.proposition71DyadicBlockCount
#print axioms ZhangLS.Spec.proposition71_dyadic_scale_lower
#print axioms ZhangLS.Spec.proposition71_dyadic_scale_pos
#print axioms ZhangLS.Spec.proposition71_dyadic_block_count_bound
#print axioms ZhangLS.Spec.proposition71_dyadic_cover
#print axioms ZhangLS.Spec.proposition71_dyadic_cover_unique
#print axioms ZhangLS.Spec.proposition71DyadicCharacters
#print axioms ZhangLS.Spec.proposition71_mem_dyadic_characters
#print axioms ZhangLS.Spec.proposition71DyadicSigmaNormSum
#print axioms ZhangLS.Spec.proposition71DyadicPolynomialNormSum
#print axioms ZhangLS.Spec.proposition71_dyadic_sigma_norm_sum_expanded
#print axioms ZhangLS.Spec.proposition71_dyadic_mellin_product_integrable
#print axioms ZhangLS.Spec.proposition71_actual_dyadic_mellin_mean
#print axioms ZhangLS.Spec.proposition71_primitive_inverse_sum
#print axioms ZhangLS.Spec.proposition71_paper_prime_le_twice_P
#print axioms ZhangLS.Spec.proposition71_actual_prime_coefficient_energy
#print axioms ZhangLS.Spec.proposition71_actual_weighted_dyadic_prime_mean
#print axioms ZhangLS.Spec.proposition71_actual_weighted_dyadic_inverse_prime_mean
#print axioms ZhangLS.Spec.proposition71_actual_delta_norm_integral
#print axioms ZhangLS.Spec.proposition71_actual_dyadic_product_bound
#print axioms ZhangLS.Spec.proposition71_actual_weighted_dyadic_sigma_bound
#print axioms ZhangLS.Spec.proposition71ExceptionalPolynomialMean
#print axioms ZhangLS.Spec.proposition71_exceptional_mean_nonneg
#print axioms ZhangLS.Spec.proposition71_exceptional_fourth_power_budget
#print axioms ZhangLS.Spec.proposition71_original_seven_five
#print axioms ZhangLS.Spec.proposition71TruncatedKappaCoefficient
#print axioms ZhangLS.Spec.proposition71TruncatedKappaPolynomial
#print axioms ZhangLS.Spec.proposition71_strict_polynomial_eq_LSeries
#print axioms ZhangLS.Spec.proposition71_mem_long_indices
#print axioms ZhangLS.Spec.proposition71_truncated_coefficient_majorant
#print axioms ZhangLS.Spec.proposition71_truncated_coefficient_energy
#print axioms ZhangLS.Spec.proposition71_actual_kappa_second_moment
#print axioms ZhangLS.Spec.proposition71_exceptional_holder
#print axioms ZhangLS.Spec.proposition71ActualConductorAggregate
#print axioms ZhangLS.Spec.proposition71_strict_triple_indices
#print axioms ZhangLS.Spec.proposition71_actual_conductor_split
#print axioms ZhangLS.Spec.proposition71_actual_conductor_power_saving
#print axioms ZhangLS.Spec.proposition71ActualLargeConductorAggregate
#print axioms ZhangLS.Spec.proposition71_actual_large_conductor_dyadic_cover
#print axioms ZhangLS.Spec.proposition71_actual_large_conductor_power_saving
#print axioms ZhangLS.Spec.proposition71FullSigmaConductorBlock
#print axioms ZhangLS.Spec.proposition71_dhR_le_cutoff
#print axioms ZhangLS.Spec.proposition71_strict_localized_aggregate_le
#print axioms ZhangLS.Spec.proposition71_full_sigma_block_le_local_and_tail
#print axioms ZhangLS.Spec.proposition71ActualSmallConductorAggregate
#print axioms ZhangLS.Spec.proposition71_strict_truncated_aggregate_le
#print axioms ZhangLS.Spec.proposition71_D_le_P
#print axioms ZhangLS.Spec.proposition71_actual_small_conductor_power_saving
#print axioms ZhangLS.Spec.proposition71_prime_primitive_iff
#print axioms ZhangLS.Spec.proposition71_full_gauss_average
#print axioms ZhangLS.Spec.proposition71_principal_gauss
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_average
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_error
#print axioms ZhangLS.Spec.proposition71_gauss_average_nonunit
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_average_all
#print axioms ZhangLS.Spec.proposition71LocalizedDyadicAggregate
#print axioms ZhangLS.Spec.proposition71_localized_dyadic_aggregate_nonneg
#print axioms ZhangLS.Spec.proposition71_localized_dyadic_aggregate_bound
#print axioms ZhangLS.Spec.proposition71_log_power_rpow_threshold
#print axioms ZhangLS.Spec.proposition71LocalizedLargeAggregate
#print axioms ZhangLS.Spec.proposition71_localized_large_aggregate_nonneg
#print axioms ZhangLS.Spec.proposition71_localized_large_aggregate_power_saving
#print axioms ZhangLS.Spec.proposition71_large_conductor_weight
#print axioms ZhangLS.Spec.proposition71LocalizedConductorBlock
#print axioms ZhangLS.Spec.proposition71_localized_conductor_block_nonneg
#print axioms ZhangLS.Spec.proposition71_localized_conductor_block_le_mean
#print axioms ZhangLS.Spec.proposition71_localized_conductor_block_bound
#print axioms ZhangLS.Spec.proposition71_log_power_linear_quarter_threshold
#print axioms ZhangLS.Spec.proposition71_uniform_large_l_geometry
#print axioms ZhangLS.Spec.proposition71_uniform_large_l_argument
#print axioms ZhangLS.Spec.proposition71_prime_second_mass_bound
#print axioms ZhangLS.Spec.proposition71_positive_imaginary_power_norm
#print axioms ZhangLS.Spec.proposition71_ratio_inverse_square
#print axioms ZhangLS.Spec.proposition71_large_l_prime_kernel
#print axioms ZhangLS.Spec.proposition71LargeLTailAggregate
#print axioms ZhangLS.Spec.proposition71_large_l_tail_aggregate_bound
#print axioms ZhangLS.Spec.proposition71_actual_localized_dyadic_power_saving
#print axioms ZhangLS.Spec.proposition71LocalScale
#print axioms ZhangLS.Spec.proposition71LocalizedIndices
#print axioms ZhangLS.Spec.proposition71_mem_localized_indices
#print axioms ZhangLS.Spec.proposition71_uniform_localized_geometry
#print axioms ZhangLS.Spec.proposition71_localized_length_budget
#print axioms ZhangLS.Spec.proposition71SigmaStar
#print axioms ZhangLS.Spec.proposition71LocalizedDyadicMean
#print axioms ZhangLS.Spec.proposition71_localized_dyadic_mean_expanded
#print axioms ZhangLS.Spec.proposition71_localized_dyadic_mean_nonneg
#print axioms ZhangLS.Spec.proposition71LargeMeanSquareConstant
#print axioms ZhangLS.Spec.proposition71_large_mean_square_constant_pos
#print axioms ZhangLS.Spec.proposition71_actual_localized_sigma_square
#print axioms ZhangLS.Spec.proposition71_positive_ratio_cpow
#print axioms ZhangLS.Spec.proposition71_finite_mellin_integrand_integrable
#print axioms ZhangLS.Spec.proposition71DoubleMellinIntegrand
#print axioms ZhangLS.Spec.proposition71_double_mellin_integrand_expansion
#print axioms ZhangLS.Spec.proposition71_double_mellin_integrand_integrable
#print axioms ZhangLS.Spec.proposition71_actual_double_mellin_sum
#print axioms ZhangLS.Spec.proposition71_inverse_mellin_integrand_integrable
#print axioms ZhangLS.Spec.proposition71_scaled_mellin_power
#print axioms ZhangLS.Spec.proposition71_extracted_scale_norm
#print axioms ZhangLS.Spec.proposition71_actual_finite_mellin_sum
#print axioms ZhangLS.Spec.proposition71_actual_delta_vertical_integrable
#print axioms ZhangLS.Spec.proposition71_actual_delta_mellin_inversion
#print axioms ZhangLS.Spec.proposition71_actual_scaled_delta_mellin
#print axioms ZhangLS.Spec.proposition71_weighted_prime_polynomial_continuous
#print axioms ZhangLS.Spec.proposition71_weighted_prime_polynomial_norm
#print axioms ZhangLS.Spec.proposition71_weighted_prime_kernel_integrable
#print axioms ZhangLS.Spec.proposition71_actual_mellin_prime_bound
#print axioms ZhangLS.Spec.proposition71_mobius_coprime_indicator
#print axioms ZhangLS.Spec.proposition71_mobius_insert
#print axioms ZhangLS.Spec.proposition71_mobius_coprime_factor
#print axioms ZhangLS.Spec.proposition71_mobius_factor_all
#print axioms ZhangLS.Spec.proposition71ArithmeticSum
#print axioms ZhangLS.Spec.proposition71ErrorScale
#print axioms ZhangLS.Spec.proposition71MainTerm
#print axioms ZhangLS.Spec.Proposition71AtConstant
#print axioms ZhangLS.Spec.Proposition71Target
#print axioms ZhangLS.Spec.proposition71_mem_indices
#print axioms ZhangLS.Spec.proposition71_good_family_exact
#print axioms ZhangLS.Spec.proposition71OffLocalConductorAggregate
#print axioms ZhangLS.Spec.proposition71_hr_le_cutoff_of_dhr
#print axioms ZhangLS.Spec.proposition71_offlocal_conductor_aggregate_bound
#print axioms ZhangLS.Spec.proposition71OffLocalLargeAggregate
#print axioms ZhangLS.Spec.proposition71_offlocal_large_aggregate_power_saving
#print axioms ZhangLS.Spec.proposition71_offlocal_prime_kernel
#print axioms ZhangLS.Spec.proposition71_offlocal_sigma_term
#print axioms ZhangLS.Spec.proposition71_offlocal_term_majorant
#print axioms ZhangLS.Spec.proposition71OffLocalTailConstant
#print axioms ZhangLS.Spec.proposition71_offlocal_tail_constant_pos
#print axioms ZhangLS.Spec.proposition71_actual_offlocal_tail_bound
#print axioms ZhangLS.Spec.proposition71OriginalSigmaSeries
#print axioms ZhangLS.Spec.proposition71_original_sigma_series_expanded
#print axioms ZhangLS.Spec.proposition71OriginalConductorAggregate
#print axioms ZhangLS.Spec.proposition71_original_seven_thirteen_majorant_little_o
#print axioms ZhangLS.Spec.proposition71OriginalSigmaStar
#print axioms ZhangLS.Spec.proposition71_original_sigma_star_expanded
#print axioms ZhangLS.Spec.proposition71OriginalLocalizedLargeAggregate
#print axioms ZhangLS.Spec.proposition71_original_localized_large_power_saving
#print axioms ZhangLS.Spec.proposition71_original_localized_large_little_o
#print axioms ZhangLS.Spec.proposition71OriginalSigmaTruncated
#print axioms ZhangLS.Spec.proposition71_original_sigma_expanded
#print axioms ZhangLS.Spec.proposition71OriginalQuarterAggregate
#print axioms ZhangLS.Spec.proposition71_beta_three_height_margin
#print axioms ZhangLS.Spec.proposition71_original_quarter_aggregate_power_saving
#print axioms ZhangLS.Spec.proposition71_outer_tail_budget
#print axioms ZhangLS.Spec.proposition71_imaginary_phase_distance
#print axioms ZhangLS.Spec.proposition71_prime_window_log_error
#print axioms ZhangLS.Spec.proposition71_actual_prime_phase_rate
#print axioms ZhangLS.Spec.proposition71_actual_phase_rate
#print axioms ZhangLS.Spec.proposition71_uniform_phase_budget
#print axioms ZhangLS.Spec.proposition71_prime_windows_equal
#print axioms ZhangLS.Spec.proposition71_actual_prime_masses_equal
#print axioms ZhangLS.Spec.proposition71_weighted_three_norm
#print axioms ZhangLS.Spec.proposition71_summed_phase_budget
#print axioms ZhangLS.Spec.proposition71_actual_arithmetic_phase_budget
#print axioms ZhangLS.Spec.proposition71_log_power_eighth_threshold
#print axioms ZhangLS.Spec.proposition71_quarter_small_conductor_power_saving
#print axioms ZhangLS.Spec.proposition71SigmaTerm
#print axioms ZhangLS.Spec.proposition71SigmaLargeLTerm
#print axioms ZhangLS.Spec.proposition71SigmaLargeLTail
#print axioms ZhangLS.Spec.proposition71_large_l_term_majorant
#print axioms ZhangLS.Spec.proposition71_large_l_tail_bound
#print axioms ZhangLS.Spec.proposition71KappaCharacterPolynomial
#print axioms ZhangLS.Spec.proposition71PrimeCharacterPolynomial
#print axioms ZhangLS.Spec.proposition71SigmaOnSet
#print axioms ZhangLS.Spec.proposition71SigmaMellinIntegrand
#print axioms ZhangLS.Spec.proposition71_kappa_character_polynomial_factor
#print axioms ZhangLS.Spec.proposition71_prime_character_polynomial_factor
#print axioms ZhangLS.Spec.proposition71_sigma_integrand_eq_double
#print axioms ZhangLS.Spec.proposition71_actual_sigma_mellin
#print axioms ZhangLS.Spec.proposition71_sigma_mellin_integrable
#print axioms ZhangLS.Spec.proposition71_sigma_mellin_norm
#print axioms ZhangLS.Spec.proposition71SigmaSeries
#print axioms ZhangLS.Spec.proposition71SigmaOffLocalTerm
#print axioms ZhangLS.Spec.proposition71SigmaOffLocalTail
#print axioms ZhangLS.Spec.proposition71_tsum_finite_split
#print axioms ZhangLS.Spec.proposition71_sigma_series_summable
#print axioms ZhangLS.Spec.proposition71_sigma_local_finite_sum
#print axioms ZhangLS.Spec.proposition71_sigma_exact_localization
#print axioms ZhangLS.Spec.proposition71_mem_sigma_truncation
#print axioms ZhangLS.Spec.proposition71_sigma_truncated_finite_sum
#print axioms ZhangLS.Spec.proposition71_sigma_truncation_complement
#print axioms ZhangLS.Spec.proposition71_sigma_exact_truncation
#print axioms ZhangLS.Spec.proposition71SmallConductorAggregate
#print axioms ZhangLS.Spec.proposition71_small_conductor_aggregate_bound
#print axioms ZhangLS.Spec.proposition71_actual_prime_sum_continuous
#print axioms ZhangLS.Spec.proposition71_actual_prime_sum_trivial_bound
#print axioms ZhangLS.Spec.proposition71_actual_inducer_weighted_prime_integral
#print axioms ZhangLS.Spec.proposition71_decay_le_inverse_modulus
#print axioms ZhangLS.Spec.proposition71_actual_inducer_weighted_prime_integral_inverse_D
#print axioms ZhangLS.Spec.proposition71_small_primitive_weighted_integral
#print axioms ZhangLS.Spec.proposition71_prime_shift_polynomial
#print axioms ZhangLS.Spec.proposition71_small_primitive_delta_sum
#print axioms ZhangLS.Spec.proposition71SigmaTruncated
#print axioms ZhangLS.Spec.proposition71_actual_small_sigma_bound
#print axioms ZhangLS.Spec.proposition71_cutoff_le_P
#print axioms ZhangLS.Spec.proposition71_short_index_lt_prime
#print axioms ZhangLS.Spec.proposition71_short_index_unit
#print axioms ZhangLS.Spec.proposition71_supported_second_index_unit
#print axioms ZhangLS.Spec.proposition71_divisible_long_index_zero
#print axioms ZhangLS.Spec.proposition71_factors_le_product
#print axioms ZhangLS.Spec.proposition71_omitted_positive_coefficient_zero
#print axioms ZhangLS.Spec.proposition71_tail_scalar_budget
#print axioms ZhangLS.Spec.proposition71_tau_five_quadratic_summable
#print axioms ZhangLS.Spec.proposition71TauFiveQuadraticMass
#print axioms ZhangLS.Spec.proposition71_tau_five_quadratic_mass_pos
#print axioms ZhangLS.Spec.proposition71_actual_dilated_kappa_majorant
#print axioms ZhangLS.Spec.proposition71_tau_dominated_series_summable
#print axioms ZhangLS.Spec.proposition71_tau_dominated_tsum_bound
#print axioms ZhangLS.Spec.proposition71_weighted_cauchy
#print axioms ZhangLS.Spec.proposition71_weighted_primitive_cauchy
#print axioms ZhangLS.Spec.proposition71_weighted_primitive_cauchy_bound
#print axioms ZhangLS.Spec.proposition71_arctan_le_self
#print axioms ZhangLS.Spec.proposition71_positive_cauchy_tail
#print axioms ZhangLS.Spec.proposition71_negative_cauchy_tail
#print axioms ZhangLS.Spec.proposition71_bounded_cauchy_integrable
#print axioms ZhangLS.Spec.proposition71_cauchy_window_and_tail

#print ZhangLS.Spec.Proposition71Target
#print ZhangLS.Spec.Proposition71AtConstant
#print ZhangLS.Spec.proposition71ArithmeticSum
#print ZhangLS.Spec.proposition71ErrorScale
#print ZhangLS.Spec.proposition71MainTerm
#print ZhangLS.Spec.lemma81ThetaOne
#print ZhangLS.Spec.lemma81ActualC
#print ZhangLS.Spec.lemma81NormalizedSegmentIntegral
#print ZhangLS.Spec.lemma81SegmentPoint
#print ZhangLS.Spec.lemma81Polynomial
#print ZhangLS.Spec.lemma81Omega
#print ZhangLS.Spec.Lemma81AdmissibleSequence
#print ZhangLS.Spec.Lemma23InPsi
#print ZhangLS.Spec.Lemma23InPsi1
#print ZhangLS.Spec.Lemma23GoodPartialSums
#print ZhangLS.Spec.lemma33ActualPrimeMass
#print ZhangLS.Spec.lemma83PaperBeta
#print ZhangLS.Spec.lemma83Kappa
#print ZhangLS.Spec.lemma83ModifiedKappa
#print ZhangLS.Spec.lemma83Lambda
#print ZhangLS.Spec.lemma83ModifiedLambda
#print ZhangLS.Spec.lemma83Xi
#print ZhangLS.Spec.proposition71TruncatedKappaCoefficient
#print ZhangLS.Spec.proposition71TruncatedKappaPolynomial
#print ZhangLS.Spec.proposition71ExceptionalPolynomialMean
#print ZhangLS.Spec.proposition71_original_seven_five
#print ZhangLS.Spec.proposition71_actual_finite_mellin_sum
#print ZhangLS.Spec.proposition71OriginalSigmaTruncated
#print ZhangLS.Spec.proposition71_original_sigma_expanded
#print ZhangLS.Spec.proposition71SmallConductorAggregate
#print ZhangLS.Spec.proposition71OriginalQuarterAggregate
#print ZhangLS.Spec.proposition71_original_quarter_aggregate_power_saving
#print ZhangLS.Spec.proposition71DoubleMellinIntegrand
#print ZhangLS.Spec.proposition71_actual_double_mellin_sum
#print ZhangLS.Spec.proposition71_weighted_primitive_cauchy_bound
#print ZhangLS.Spec.proposition71LocalScale
#print ZhangLS.Spec.proposition71LocalizedIndices
#print ZhangLS.Spec.proposition71SigmaStar
#print ZhangLS.Spec.proposition71LocalizedDyadicMean
#print ZhangLS.Spec.proposition71_actual_localized_dyadic_power_saving
#print ZhangLS.Spec.proposition71LocalizedConductorBlock
#print ZhangLS.Spec.proposition71LocalizedDyadicAggregate
#print ZhangLS.Spec.proposition71DyadicScale
#print ZhangLS.Spec.proposition71DyadicBlockCount
#print ZhangLS.Spec.proposition71LocalizedLargeAggregate
#print ZhangLS.Spec.proposition71OriginalSigmaStar
#print ZhangLS.Spec.proposition71OriginalLocalizedLargeAggregate
#print ZhangLS.Spec.proposition71_original_localized_large_little_o
#print ZhangLS.Spec.proposition71_actual_large_delta_tail
#print ZhangLS.Spec.proposition71_actual_delta_offcenter
#print ZhangLS.Spec.proposition71TauFiveQuadraticMass
#print ZhangLS.Spec.proposition71SigmaTerm
#print ZhangLS.Spec.proposition71SigmaLargeLTerm
#print ZhangLS.Spec.proposition71SigmaLargeLTail
#print ZhangLS.Spec.proposition71SigmaSeries
#print ZhangLS.Spec.proposition71SigmaOffLocalTerm
#print ZhangLS.Spec.proposition71SigmaOffLocalTail
#print ZhangLS.Spec.proposition71_sigma_series_summable
#print ZhangLS.Spec.proposition71_sigma_exact_localization
#print ZhangLS.Spec.proposition71_sigma_exact_truncation
#print ZhangLS.Spec.proposition71OffLocalLargeAggregate
#print ZhangLS.Spec.proposition71_offlocal_large_aggregate_power_saving
#print ZhangLS.Spec.proposition71ActualSmallConductorAggregate
#print ZhangLS.Spec.proposition71ActualLargeConductorAggregate
#print ZhangLS.Spec.proposition71ActualConductorAggregate
#print ZhangLS.Spec.proposition71OriginalSigmaSeries
#print ZhangLS.Spec.proposition71_original_sigma_series_expanded
#print ZhangLS.Spec.proposition71OriginalConductorAggregate
#print ZhangLS.Spec.proposition71_original_seven_thirteen_majorant_little_o
#print ZhangLS.Spec.NormalizedAssumptionA
#print ZhangLS.Spec.AssumptionAWithConstant
#print ZhangLS.Spec.lemma23PaperP
#print ZhangLS.Spec.lemma56PaperT
#print ZhangLS.Spec.lemma44PaperAlpha
#print ZhangLS.Spec.lemma51PaperT0
#print ZhangLS.Spec.lemma52PaperBetaOne
#print ZhangLS.Spec.lemma52PaperBetaTwo
#print ZhangLS.Spec.lemma52PaperBetaThree
