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
import ZhangLS.Spec.Proposition141OffDiagonalCoefficientSum
import ZhangLS.Spec.Proposition141PrimitiveOffDiagonalSum
import ZhangLS.Spec.Proposition141SourceSmallSum
import ZhangLS.Spec.Proposition141SourceSmallAggregate
import ZhangLS.Spec.Proposition141SmallScalarRate
import ZhangLS.Spec.Proposition141NormalizedSmallAggregate
import ZhangLS.Spec.Proposition141LongTailSigma
import ZhangLS.Spec.Proposition141SourceLongTailBlock
import ZhangLS.Spec.Proposition141SmallLongTailAggregate
import ZhangLS.Spec.Proposition141UnlocalizedSmallAggregate
import ZhangLS.Spec.Proposition141CompleteConductorRate
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

example (D D₁ D₂ d h:ℕ) (a:ℕ→ℂ) :
    proposition141SourceSmallModuli D D₁ D₂ d h a =
      (Icc 1 (D^3)).filter (fun r=>1<r ∧ r<D^3 ∧ D₂∣r*h ∧
        (r*h/D₂).Coprime D₁ ∧ a (d*(r*h/D₂))≠0) := rfl
example {D:ℕ} (χ:RealPrimitiveCharacter D) (h r:ℕ) :
    proposition141SmallPrimitiveFamily χ h r =
      univ.filter (fun θ:DirichletCharacter ℂ r=>θ.IsPrimitive ∧ ∀hDN:D∣r*h,
        θ.changeLevel (r.dvd_mul_right h)≠χ.chi.changeLevel hDN) := rfl
example {D r:ℕ} (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ) (κ:ℕ→ℂ) (D₁ d h l:ℕ) :
    proposition141SigmaLongTailTerm χ θ β κ D₁ d h l =
      if lemma23PaperP D^3<(l:ℝ) then proposition141SigmaTerm χ θ β κ D₁ d h l else 0 := rfl
example {D r:ℕ} (χ:RealPrimitiveCharacter D) (θ:DirichletCharacter ℂ r) (β:ℂ) (κ:ℕ→ℂ) (D₁ d h l:ℕ)
    (hl:(l:ℝ)≤lemma23PaperP D^3) : proposition141SigmaLongTailTerm χ θ β κ D₁ d h l=0 := by
  simp only [proposition141SigmaLongTailTerm,if_neg (not_lt.mpr hl)]
example {D:ℕ} (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) :
    proposition141CompleteConductorMajorant χ β κ a =
      proposition141NormalizedUnlocalizedSmallAggregate χ β κ a+
        proposition141NormalizedUnlocalizedLargeAggregate χ β κ a := rfl
#print axioms ZhangLS.Spec.proposition141_uniform_off_diagonal_finite_sum_bound
#print axioms ZhangLS.Spec.proposition141_uniform_primitive_off_diagonal_sum_bound
#print axioms ZhangLS.Spec.proposition141SourceSmallModuli
#print axioms ZhangLS.Spec.proposition141_source_small_moduli_mem
#print axioms ZhangLS.Spec.proposition141_uniform_source_small_character_sum
#print axioms ZhangLS.Spec.proposition141SourceSmallAggregate
#print axioms ZhangLS.Spec.proposition141_source_small_weight_sum
#print axioms ZhangLS.Spec.proposition141_uniform_source_small_aggregate
#print axioms ZhangLS.Spec.proposition141_decay_le_inverse_seventh
#print axioms ZhangLS.Spec.proposition141_small_normalized_scalar
#print axioms ZhangLS.Spec.proposition141_floor_P_cube_log_five
#print axioms ZhangLS.Spec.proposition141_small_log_budget
#print axioms ZhangLS.Spec.proposition141NormalizedSmallPrefix
#print axioms ZhangLS.Spec.proposition141_uniform_normalized_small_prefix
#print axioms ZhangLS.Spec.proposition141_four_t0_le_P
#print axioms ZhangLS.Spec.proposition141_individual_local_upper
#print axioms ZhangLS.Spec.proposition141SigmaLongTailTerm
#print axioms ZhangLS.Spec.proposition141SigmaLongTail
#print axioms ZhangLS.Spec.proposition141_long_tail_term_majorant
#print axioms ZhangLS.Spec.proposition141_actual_long_tail_bound
#print axioms ZhangLS.Spec.proposition141_actual_sigma_prefix
#print axioms ZhangLS.Spec.proposition141SourceLongTailBlock
#print axioms ZhangLS.Spec.proposition141_source_long_tail_block_bound
#print axioms ZhangLS.Spec.proposition141NormalizedSmallLongTailAggregate
#print axioms ZhangLS.Spec.proposition141_actual_small_long_tail_aggregate_bound
#print axioms ZhangLS.Spec.proposition141NormalizedUnlocalizedSmallAggregate
#print axioms ZhangLS.Spec.proposition141_actual_unlocalized_small_aggregate_split
#print axioms ZhangLS.Spec.proposition141_uniform_unlocalized_small_aggregate_rate
#print axioms ZhangLS.Spec.proposition141CompleteConductorMajorant
#print axioms ZhangLS.Spec.proposition141_complete_conductor_rate
#print axioms ZhangLS.Spec.proposition141_complete_conductor_little_o
