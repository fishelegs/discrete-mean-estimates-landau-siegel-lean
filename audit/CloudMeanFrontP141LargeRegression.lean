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
import ZhangLS.Spec.Proposition141WeightedSmallAggregate
import ZhangLS.Spec.Proposition141LargeMellinMean
import ZhangLS.Spec.Proposition141LocalizedGeometry
import ZhangLS.Spec.Proposition141LocalizedLargeMean
import ZhangLS.Spec.Proposition141LargeConductorSaving
import ZhangLS.Spec.Proposition141UniformLargeSaving
import ZhangLS.Spec.Proposition141DyadicCover
import ZhangLS.Spec.ConductorTotientWeight
import ZhangLS.Spec.Proposition141LargeConductorBlock
import ZhangLS.Spec.Proposition141DivisorWeightedBudget
import ZhangLS.Spec.Proposition141SourceLargeBlock
import ZhangLS.Spec.Proposition141SourceLargeAggregate
import ZhangLS.Spec.Proposition141NormalizedLargeAggregate
import ZhangLS.Spec.PolynomialLogDecay
import ZhangLS.Spec.Proposition141SourceOuterSupport
import ZhangLS.Spec.Proposition141LargeAggregateRate
set_option autoImplicit false
open ZhangLS.Spec Complex Finset
open scoped Classical ComplexConjugate
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

example (D₁ D₂ d h:ℕ) (R:ℝ) (a:ℕ→ℂ) :
    proposition141SourceLargeModuli D₁ D₂ d h R a =
      (primitiveDyadicModuli R).filter (fun r=>D₂∣h*r ∧ (h*r/D₂).Coprime D₁ ∧ a (d*(h*r/D₂))≠0) := rfl
example {D:ℕ} (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) :
    proposition141NormalizedLargeAggregate χ β κ a =
      ‖(lemma51PaperT0 D:ℂ)^β‖/Real.sqrt (D:ℝ)*
        ∑D₁∈D.divisors,proposition141SourceLargeAggregate χ β κ a D₁ (D/D₁) ⌊lemma23PaperP D⌋₊ := rfl
example (D₁ D₂ d h:ℕ) (R:ℝ) :
    proposition141SourceLargeModuli D₁ D₂ d h R (fun _=>0)=∅ := by
  ext r
  simp [proposition141SourceLargeModuli]
example : polynomialLogHalfConstant 0=1 := by norm_num [polynomialLogHalfConstant]
#print axioms ZhangLS.Spec.proposition141WeightedSmallConductorAggregate
#print axioms ZhangLS.Spec.proposition141_weighted_small_aggregate_le
#print axioms ZhangLS.Spec.proposition141_uniform_weighted_small_conductor_aggregate
#print axioms ZhangLS.Spec.proposition141_double_mellin_norm
#print axioms ZhangLS.Spec.proposition141_delta_line_norm_integrable
#print axioms ZhangLS.Spec.proposition141_delta_line_norm_integral
#print axioms ZhangLS.Spec.proposition141PrimitiveModulusPairs
#print axioms ZhangLS.Spec.proposition141WeightedFiniteMean
#print axioms ZhangLS.Spec.proposition141_actual_weighted_finite_mellin_mean
#print axioms ZhangLS.Spec.proposition141LocalScale
#print axioms ZhangLS.Spec.proposition141LocalizedIndices
#print axioms ZhangLS.Spec.proposition141_mem_localized_indices
#print axioms ZhangLS.Spec.proposition141_localized_geometry
#print axioms ZhangLS.Spec.proposition141_localized_length_budget
#print axioms ZhangLS.Spec.proposition141LocalizedWeightedMean
#print axioms ZhangLS.Spec.proposition141_localized_mean_nonneg
#print axioms ZhangLS.Spec.proposition141LargeMeanSquareConstant
#print axioms ZhangLS.Spec.proposition141_large_mean_square_constant_pos
#print axioms ZhangLS.Spec.proposition141_actual_localized_large_mean_square
#print axioms ZhangLS.Spec.proposition141_large_conductor_geometric_budget
#print axioms ZhangLS.Spec.proposition141LargeMeanConstant
#print axioms ZhangLS.Spec.proposition141_large_mean_constant_pos
#print axioms ZhangLS.Spec.proposition141_actual_localized_large_mean_saving
#print axioms ZhangLS.Spec.proposition141_supported_conductor_scale
#print axioms ZhangLS.Spec.proposition141_uniform_localized_large_saving
#print axioms ZhangLS.Spec.proposition141DyadicScale
#print axioms ZhangLS.Spec.proposition141DyadicBlockCount
#print axioms ZhangLS.Spec.proposition141_dyadic_scale_lower
#print axioms ZhangLS.Spec.proposition141_dyadic_scale_pos
#print axioms ZhangLS.Spec.proposition141_dyadic_block_count_bound
#print axioms ZhangLS.Spec.proposition141_dyadic_cover
#print axioms ZhangLS.Spec.proposition141_dyadic_cover_unique
#print axioms ZhangLS.Spec.conductorTotientWeight_three_halves
#print axioms ZhangLS.Spec.conductorTotientWeight_bound
#print axioms ZhangLS.Spec.proposition141_localized_mean_expanded
#print axioms ZhangLS.Spec.proposition141LocalizedConductorBlock
#print axioms ZhangLS.Spec.proposition141_localized_block_nonneg
#print axioms ZhangLS.Spec.proposition141_localized_block_le_mean
#print axioms ZhangLS.Spec.proposition141_uniform_localized_conductor_block
#print axioms ZhangLS.Spec.proposition141_divisor_tau_five_harmonic
#print axioms ZhangLS.Spec.proposition141_complementary_divisor_sum
#print axioms ZhangLS.Spec.proposition141_complementary_divisor_budget
#print axioms ZhangLS.Spec.proposition141_normalized_complementary_divisor_budget
#print axioms ZhangLS.Spec.proposition141SourceLargeModuli
#print axioms ZhangLS.Spec.proposition141SourceLargeBlock
#print axioms ZhangLS.Spec.proposition141_source_large_moduli_mem
#print axioms ZhangLS.Spec.proposition141_source_large_block_le
#print axioms ZhangLS.Spec.proposition141_source_large_block_cutoff
#print axioms ZhangLS.Spec.proposition141_uniform_source_large_block
#print axioms ZhangLS.Spec.proposition141SourceLargeAggregate
#print axioms ZhangLS.Spec.proposition141_large_outer_weight_sum
#print axioms ZhangLS.Spec.proposition141_uniform_source_large_aggregate
#print axioms ZhangLS.Spec.proposition141NormalizedLargeAggregate
#print axioms ZhangLS.Spec.proposition141_floor_P_log_seven
#print axioms ZhangLS.Spec.proposition141_exterior_power_identity
#print axioms ZhangLS.Spec.proposition141_uniform_normalized_large_aggregate
#print axioms ZhangLS.Spec.polynomialLogHalfConstant
#print axioms ZhangLS.Spec.polynomialLogHalfConstant_pos
#print axioms ZhangLS.Spec.polynomialLog_half_power
#print axioms ZhangLS.Spec.polynomialLog_div_decay
#print axioms ZhangLS.Spec.proposition141_source_outer_support
#print axioms ZhangLS.Spec.proposition141_source_large_moduli_empty
#print axioms ZhangLS.Spec.proposition141_uniform_source_outer_support
#print axioms ZhangLS.Spec.proposition141LargeAggregateConstant
#print axioms ZhangLS.Spec.proposition141_large_aggregate_constant_pos
#print axioms ZhangLS.Spec.proposition141_uniform_large_aggregate_rate
#print axioms ZhangLS.Spec.proposition141_uniform_large_aggregate_little_o
