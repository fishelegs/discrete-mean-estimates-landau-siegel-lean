import ZhangLS.Spec.Proposition141GaussFrontArithmetic
import ZhangLS.Spec.Proposition141OriginalAdditiveReduction
import ZhangLS.Spec.Proposition141ChiMainNormalization
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
import ZhangLS.Spec.Proposition141FrontObjects
import ZhangLS.Spec.Proposition141FrontGeometry
import ZhangLS.Spec.Proposition141FrontMean
import ZhangLS.Spec.Proposition141ExceptionalMean
import ZhangLS.Spec.Proposition141OriginalGaussReduction
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

example (D:ℕ) : proposition141Indices D=Icc 1 ⌊2*lemma61PaperP4 D⌋₊ :=
  proposition141_indices_eq_closed_prefix D
example {D p:ℕ} [NeZero p] (χ:RealPrimitiveCharacter D) (κ a:ℕ→ℂ) (ψ:DirichletCharacter ℂ p) :
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    proposition141GaussDeltaOneTerm χ κ a ψ =
      (gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar/((D*p:ℕ):ℂ))*
        ∑'m:ℕ,proposition71DeltaOneDoubleTerm D (fun n=>κ n*ψ (n:ZMod p))
          (proposition141Indices D) (fun n=>a n*ψ⁻¹ (n:ZMod p)) ((D*p:ℕ):ℝ) m := rfl
example {D p:ℕ} (χ:RealPrimitiveCharacter D) (ψ:DirichletCharacter ℂ p) :
    (lemma44CharacterTwist χ ψ)⁻¹=lemma44CharacterTwist χ ψ⁻¹ := proposition141_twist_inverse χ ψ
example (D:ℕ) (f:ℂ→ℂ) : proposition141SegmentIntegral D f=lemma81NormalizedSegmentIntegral D 1 f :=
  proposition141_segment_exact D f
example {D:ℕ} (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) :
    proposition141GaussDeltaOneMean χ β κ a =
      ∑ψ∈lemma33ActualFamily D,proposition141ShiftWeight D ψ.1.val β*proposition141GaussDeltaOneTerm χ κ a ψ.2 := rfl

example {D:ℕ} (χ:RealPrimitiveCharacter D) (β:ℂ) (κ a:ℕ→ℂ) :
    proposition141AdditiveSourceMean χ β κ a=
      ∑p∈lemma33PrimeWindow D,proposition141ShiftWeight D p β*
        proposition141PrimeAdditiveArithmetic (p:=p) χ κ a := rfl
example (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba) (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀D:ℕ,D₀≤D → ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
      ∀κ a:ℕ→ℂ,Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D →
          ‖proposition141ThetaTwo χ β κ a-proposition141AdditiveSourceMean χ β κ a‖≤
            ε*lemma33ActualPrimeMass D :=
  proposition141_original_additive_reduction Bκ Ba hBκ hBa ε hε
example {D:ℕ} (χ:RealPrimitiveCharacter D) (κ:ℕ→ℂ) (p d k:ℕ) :
    proposition141ChiInducedInner χ κ p d k=
      if hk:0<k then
        letI : NeZero k := ⟨Nat.ne_of_gt hk⟩
        letI : NeZero (D*k) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne k)⟩
        let θ := χ.chi.changeLevel (D.dvd_mul_right k)
        gaussSum θ⁻¹ ZMod.stdAddChar*
          ∑'l:ℕ+,κ (d*l)*θ (-((l:ℕ):ZMod (D*k)))*conj (θ (p:ZMod (D*k)))*
            lemma53PaperDelta D ((l:ℝ)/((D:ℝ)*(p:ℝ)*(k:ℝ)))
      else 0 := rfl
example {D:ℕ} (χ:RealPrimitiveCharacter D) (hD:1<D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D) (β:ℂ) (κ a:ℕ→ℂ) :
    proposition141ChiInducedTotal χ β κ a=proposition141MainTerm χ β κ a :=
  proposition141_chi_induced_total_eq_main χ hD hmod β κ a
#print axioms ZhangLS.Spec.proposition141_actual_family_primitive_sum
#print axioms ZhangLS.Spec.proposition141_front_character_series_summable
#print axioms ZhangLS.Spec.proposition141_gauss_front_character_expansion
#print axioms ZhangLS.Spec.proposition141_gauss_front_prime_arithmetic
#print axioms ZhangLS.Spec.proposition141_gauss_front_arithmetic_mean
#print axioms ZhangLS.Spec.proposition141AdditiveSourceMean
#print axioms ZhangLS.Spec.proposition141_gauss_front_additive_difference
#print axioms ZhangLS.Spec.proposition141_original_additive_reduction
#print axioms ZhangLS.Spec.proposition141_real_character_unit_square
#print axioms ZhangLS.Spec.proposition141_chi_induced_normalized_phase
#print axioms ZhangLS.Spec.proposition141ChiInducedInner
#print axioms ZhangLS.Spec.proposition141_chi_induced_normalized_row
#print axioms ZhangLS.Spec.proposition141ChiInducedTotal
#print axioms ZhangLS.Spec.proposition141_chi_induced_total_eq_main
