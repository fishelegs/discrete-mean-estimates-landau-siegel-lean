import ZhangLS.Spec.Proposition26OriginalTransfer
import ZhangLS.Spec.Proposition26OriginalObjects
import ZhangLS.Spec.Proposition26ArithmeticEnergy
import ZhangLS.Spec.Proposition26E2Energy
import ZhangLS.Spec.Proposition26ChiHarmonic
import ZhangLS.Spec.Proposition26OuterWeight
import ZhangLS.Spec.Proposition26EnergyAlgebra

set_option autoImplicit false
set_option maxHeartbeats 3000000
open Complex ComplexConjugate MeasureTheory Finset
open scoped Classical
namespace ZhangLS.Spec

theorem proposition26_regression_J2 {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    proposition26J2 χ ψ s =
      ∑' n : ℕ, LSeries.term (fun n => χ.evalNat n*ψ (n:ZMod p)) s n *
        (lemma111Tent (Real.log (n:ℝ)/Real.log (lemma23PaperP D)+
          1/250-Real.log ((D:ℝ)*lemma51PaperT0 D)/Real.log (lemma23PaperP D)):ℂ) := rfl

theorem proposition26_regression_H2 {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    proposition26H2 χ ψ s =
      conj (-(100635/100000:ℂ)-(22789/100000:ℂ)*I)*
        (∑ n∈lemma82StrictCutoff (lemma23PaperP D^(249/500:ℝ)),
          (χ.evalNat n*ψ (n:ZMod p))/(n:ℂ)^s *
            ((1-Real.log (n:ℝ)/Real.log (lemma23PaperP D^(249/500:ℝ)):ℝ):ℂ)*
              (((lemma23PaperP D^(249/500:ℝ))/(n:ℝ):ℝ):ℂ)^(lemma82SmoothingBeta D 6))+
      conj (-(68738/100000:ℂ)+(160688/100000:ℂ)*I)*
        (∑ n∈lemma82StrictCutoff (lemma23PaperP D^(1/2:ℝ)*lemma56PaperT D^(-10:ℤ)),
          (χ.evalNat n*ψ (n:ZMod p))/(n:ℂ)^s *
            ((1-Real.log (n:ℝ)/Real.log (lemma23PaperP D^(1/2:ℝ)*lemma56PaperT D^(-10:ℤ)):ℝ):ℂ)*
              (((lemma23PaperP D^(1/2:ℝ)*lemma56PaperT D^(-10:ℤ))/(n:ℝ):ℝ):ℂ)^
                (lemma82SmoothingBeta D 7)) := rfl

theorem proposition26_regression_Xi3 {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) :
    proposition26XiThreeStar χ c Y =
      ∑ ψ∈lemma81GoodFamily χ, ∑ ρ∈lemma81ZeroFinset D ψ.2,
        (lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ).re *
          (Real.sqrt Real.pi/lemma23PaperL D^400*
            Real.exp (-(ρ.im-(lemma23PaperCenter D).im)^2/(4*(lemma23PaperL D^400)^2))) *
          ‖proposition26JDefect χ ψ.2 ρ‖*‖proposition26H2 χ ψ.2 ρ‖ := rfl

theorem proposition26_regression_E2_square {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (hL : 0 < lemma23PaperL D) :
    (lemma23PaperL D^(-68:ℤ)*
      (∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),
        ‖lemma112ShortPolynomial χ ψ (s+I*(v:ℂ))‖*
          Real.exp (-(v^2)/(4*lemma23PaperL D^30))))^2 ≤
      (2*Real.sqrt Real.pi*lemma23PaperL D^(-121:ℤ))*
        (∫ v in (-(lemma23PaperL D^20))..(lemma23PaperL D^20),
          ‖lemma112ShortPolynomial χ ψ (s+I*(v:ℂ))‖^2*
            Real.exp (-(v^2)/(4*lemma23PaperL D^30))) :=
  proposition26_actual_E2_square χ ψ s hL

theorem proposition26_regression_full_gaussian_mass {D : ℕ} (hL : 0<lemma23PaperL D) :
    (∫ v : ℝ, Real.exp (-(v^2)/(4*lemma23PaperL D^30))) =
      2*Real.sqrt Real.pi*lemma23PaperL D^15 :=
  proposition26_error_gaussian_mass hL

theorem proposition26_regression_source_arithmetic {D : ℕ} (c : ℝ)
    (a : ℕ → ℂ) (hα : 0 < lemma44PaperAlpha D) :
    ‖proposition71MainTerm D c a (fun n => conj (a n))‖ ≤
      (2/lemma44PaperAlpha D)*
        (∑ j : Fin 3, ‖∑ d∈lemma81PolynomialIndices D, ∑ r∈lemma81PolynomialIndices D,
          (↑|ArithmeticFunction.moebius r|:ℂ)*
            lemma83Lambda (lemma83PaperBeta D c) (d*r) (1-lemma83PaperBeta D c j)/
              ((d:ℂ)*(r:ℂ)*(Nat.totient r:ℂ))*
          (∑ m∈lemma81PolynomialIndices D, a (d*r*m)/(m:ℂ)^(1-lemma83PaperBeta D c j))*
          (∑ n∈lemma81PolynomialIndices D, conj (a (d*r*n))*
            lemma83Xi (lemma83PaperBeta D c) j n d r/(n:ℂ))‖)*
          (∑ p : lemma33PrimeIndex D, (p.val:ℝ)) :=
  proposition26_main_term_norm c a (fun n => conj (a n)) hα

theorem proposition26_regression_actual_target :
    Proposition26Target ↔
    ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
      ∀ ε : ℝ, 0<ε → ∃ N : ℕ, 2≤N ∧
        ∀ D : ℕ, N≤D → ∀ χ : RealPrimitiveCharacter D,
          NormalizedAssumptionA χ →
          ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
            (∀ ψ∈lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
            |proposition26XiThreeStar χ c Y| ≤
              ε*((6/Real.pi^2)*realLDerivAtOne χ^2*
                ∏ p∈D.primeFactors, (p:ℝ)/((p:ℝ)+1))*
                (∑ p : lemma33PrimeIndex D, (p.val:ℝ)) := Iff.rfl

theorem proposition26_regression_chi_harmonic {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 8≤Real.log (D:ℝ)) {s : ℂ}
    (hs : s.re=1) (hnorm : ‖s‖≤(D:ℝ)) {x : ℝ} (hx : 1≤x) :
    ‖∑ n∈Finset.Icc 1 ⌊x⌋₊, χ.evalNat n*(n:ℂ)^(-s)‖ ≤
      (14*Real.exp 16+2)*Real.log (D:ℝ) :=
  proposition26_chi_harmonic_uniform χ hD hL hs hnorm hx

theorem proposition26_regression_chi_BV {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1<D) (hL : 8≤Real.log (D:ℝ)) {s : ℂ}
    (hs : s.re=1) (hnorm : ‖s‖≤(D:ℝ)) (N : ℕ) (f : ℕ→ℂ) :
    ‖∑ i∈range N,f i*(χ.evalNat (i+1)*((i+1:ℕ):ℂ)^(-s))‖ ≤
      ((14*Real.exp 16+2)*Real.log (D:ℝ))*
        (‖f (N-1)‖+∑ i∈range (N-1),‖f (i+1)-f i‖) :=
  proposition26_chi_harmonic_variation χ hD hL hs hnorm N f

theorem proposition26_regression_energy_homogeneity {D : ℕ}
    (χ : RealPrimitiveCharacter D) (c : ℝ)
    (Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ)
    (F : (ψ : lemma33CharacterIndex D) → ℂ → ℂ) (z : ℂ) :
    proposition26Energy χ c Y (fun ψ s => z*F ψ s) = ‖z‖^2*proposition26Energy χ c Y F := by
  unfold proposition26Energy
  simp only [norm_mul,mul_pow,Finset.mul_sum]
  apply sum_congr rfl
  intro ψ hψ
  apply sum_congr rfl
  intro ρ hρ
  ring

theorem proposition26_regression_outer_phi (S : Finset ℕ) (N : ℕ) (hN : 1≤N)
    (hS : S⊆Icc 1 N) :
    (∑ d∈S, ∑ r∈S, (d:ℝ)⁻¹*((Nat.totient r:ℝ)⁻¹)^2) ≤
      (1+Real.log (N:ℝ))*(∑' r : ℕ, ((Nat.totient r:ℝ)⁻¹)^2) :=
  proposition26_outer_totient_sum S N hN hS


/-- Replay the proved target with the actual prime mass and source a expanded. -/
theorem proposition26_regression_proved_target :
    ∃ c : ℝ, 0<c ∧ Lemma52CompatibleConstant c ∧
      ∀ ε : ℝ, 0<ε → ∃ N : ℕ, 2≤N ∧
        ∀ D : ℕ, N≤D → ∀ χ : RealPrimitiveCharacter D,
          NormalizedAssumptionA χ →
          ∀ Y : (ψ : lemma33CharacterIndex D) → ℂ → ℂ,
            (∀ ψ∈lemma81GoodFamily χ, Lemma23ActualBranch ψ.2 (Y ψ)) →
            |∑ ψ∈lemma81GoodFamily χ, ∑ ρ∈lemma81ZeroFinset D ψ.2,
              (lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ).re *
                (Real.sqrt Real.pi/lemma23PaperL D^400*
                  Real.exp (-(ρ.im-(lemma23PaperCenter D).im)^2/(4*(lemma23PaperL D^400)^2))) *
                ‖proposition26JDefect χ ψ.2 ρ‖*‖proposition26H2 χ ψ.2 ρ‖| ≤
              ε*((6/Real.pi^2)*realLDerivAtOne χ^2*
                ∏ p∈D.primeFactors, (p:ℝ)/((p:ℝ)+1))*
                (∑ p : lemma33PrimeIndex D, (p.val:ℝ)) := proposition26_proved

/-- The theorem also applies directly to the literal complex source Xi3 sum. -/
theorem proposition26_regression_literal_complex_sum :
    ∃c:ℝ,0<c ∧ Lemma52CompatibleConstant c ∧
      ∀ε:ℝ,0<ε → ∃N:ℕ,2≤N ∧ ∀D:ℕ,N≤D →
        ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
          ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
            (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
            ‖∑ψ∈lemma81GoodFamily χ,∑ρ∈lemma81ZeroFinset D ψ.2,
              lemma23ActualCoefficient ψ.2 (Y ψ) D c ρ*
                (‖proposition26JDefect χ ψ.2 ρ‖:ℂ)*(‖proposition26H2 χ ψ.2 ρ‖:ℂ)*
                  lemma81Omega D ρ‖≤ε*lemma171MainTerm χ*lemma33ActualPrimeMass D := by
  obtain ⟨c,hc,hcompat,hp⟩ := proposition26_proved
  obtain ⟨Ni,hi⟩ := proposition26_original_Xi3_complex_identity hcompat
  refine ⟨c,hc,hcompat,?_⟩
  intro ε hε
  obtain ⟨Np,hNp,hp⟩ := hp ε hε
  refine ⟨max Np Ni,hNp.trans (le_max_left _ _),?_⟩
  intro D hD χ hA Y hY
  rw [hi D ((le_max_right _ _).trans hD) χ Y hY,Complex.norm_real,Real.norm_eq_abs]
  exact hp D ((le_max_left _ _).trans hD) χ hA Y hY

/-- Fixed-bound-before-profile quantifiers for the actual BV norm. -/
theorem proposition26_regression_uniform_BV :
    ∃c:ℝ,0<c ∧ Lemma52CompatibleConstant c ∧
      ∀V:ℝ,0<V → ∃K:ℝ,0<K ∧ ∃N:ℕ,2≤N ∧
        ∀D:ℕ,N≤D → ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
          ∀v:ℝ,|v|≤lemma23PaperL D^20 → ∀w:ℕ→ℂ,
            Proposition26VariationBound w V →
            (∀n:ℕ,lemma81Cutoff D≤(n:ℝ) → w n=0) →
            ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
              (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
              (∑ψ∈lemma81GoodFamily χ,∑ρ∈lemma81ZeroFinset D ψ.2,
                proposition26Weight c Y ψ ρ *
                  ‖lemma81Polynomial D (proposition26TwistedCoefficient χ v w) ψ.2 ρ‖^2)≤
                K*(∑p:lemma33PrimeIndex D,(p.val:ℝ))*lemma23PaperL D^20 :=
  proposition26_uniform_bv_energy


/-- The actual J-defect and arbitrary fixed-V norm share a proved common c. -/
theorem proposition26_regression_actual_defect_package :
    ∃c:ℝ,0<c ∧ Lemma52CompatibleConstant c ∧ Proposition26BVNormAt c ∧
      ∃K:ℝ,0<K ∧ ∃N:ℕ,2≤N ∧ ∀D:ℕ,N≤D →
        ∀χ:RealPrimitiveCharacter D,NormalizedAssumptionA χ →
          ∀Y:(ψ:lemma33CharacterIndex D)→ℂ→ℂ,
            (∀ψ∈lemma81GoodFamily χ,Lemma23ActualBranch ψ.2 (Y ψ)) →
            (∑ψ∈lemma81GoodFamily χ,∑ρ∈lemma81ZeroFinset D ψ.2,
              proposition26Weight c Y ψ ρ*‖proposition26JDefect χ ψ.2 ρ‖^2)≤
                K*(∑p:lemma33PrimeIndex D,(p.val:ℝ))*(Real.log (D:ℝ))^(-28:ℤ) :=
  proposition26_original_defect_energy

end ZhangLS.Spec
#print axioms ZhangLS.Spec.proposition26_regression_J2
#print axioms ZhangLS.Spec.proposition26_regression_H2
#print axioms ZhangLS.Spec.proposition26_regression_Xi3
#print axioms ZhangLS.Spec.proposition26_regression_E2_square
#print axioms ZhangLS.Spec.proposition26_regression_full_gaussian_mass
#print axioms ZhangLS.Spec.proposition26_regression_source_arithmetic
#print axioms ZhangLS.Spec.proposition26_regression_actual_target

#print axioms ZhangLS.Spec.proposition26_regression_chi_harmonic
#print axioms ZhangLS.Spec.proposition26_regression_chi_BV
#print axioms ZhangLS.Spec.proposition26_regression_energy_homogeneity

#print axioms ZhangLS.Spec.proposition26_regression_outer_phi

#print axioms ZhangLS.Spec.proposition26_regression_outer_phi
#print axioms ZhangLS.Spec.proposition26_regression_proved_target
#print axioms ZhangLS.Spec.proposition26_regression_literal_complex_sum
#print axioms ZhangLS.Spec.proposition26_regression_uniform_BV

#print axioms ZhangLS.Spec.proposition26_regression_actual_defect_package
