import ZhangLS.Spec.Proposition141PrimeSourceMean
set_option autoImplicit false
open ZhangLS.Spec Complex Finset
open scoped Classical ComplexConjugate

example (D D₁ D₂ p d k:ℕ) (κ:ℕ→ℂ) :
    proposition141PrincipalTerm D D₁ D₂ p d k κ 0=0 := by
  simp [proposition141PrincipalTerm,tauDeltaDilatedTerm]
example (D D₁ D₂ p d k:ℕ) (κ:ℕ→ℂ) :
    proposition141PrincipalRow D D₁ D₂ p d k κ (fun _=>0)=0 := by
  simp [proposition141PrincipalRow]
example (D D₁ D₂ p:ℕ) (κ:ℕ→ℂ) :
    proposition141PrincipalCorrection D D₁ D₂ p κ (fun _=>0)=0 := by
  simp [proposition141PrincipalCorrection,proposition141PrincipalRow]
example (z:ℂ) : Proposition141KappaBound 0 (fun n=>if n=0 then z else 0) := by
  intro n hn
  simp [Nat.ne_of_gt hn]
example (D:ℕ) : (∑d∈D.divisors,(lemma34Tau 5 d:ℝ)*(lemma34Tau 2 (D/d):ℝ))=
    (lemma34Tau 7 D:ℝ) := proposition141_principal_divisor_convolution D
example : (∑d∈(1:ℕ).divisors,(lemma34Tau 5 d:ℝ)*(lemma34Tau 2 (1/d):ℝ))=1 := by
  rw [proposition141_principal_divisor_convolution]
  exact_mod_cast (lemma34_tau_multiplicative 7).map_one
example (D p:ℕ) : proposition141ShiftWeight D p 0=1 := proposition141_zero_shift D p
example {D D₁ D₂ p d k:ℕ} [NeZero (D₂*k)] (κ:ℕ→ℂ) :
    proposition141PrincipalInner D D₁ D₂ p d k κ =
      gaussSum (1:DirichletCharacter ℂ (D₂*k))⁻¹ ZMod.stdAddChar *
        ∑'l:ℕ,if 0<l then κ ((D₁*d)*l) *
          (1:DirichletCharacter ℂ (D₂*k)) (-(l:ZMod (D₂*k))) *
            conj ((1:DirichletCharacter ℂ (D₂*k)) (p:ZMod (D₂*k))) *
              lemma53PaperDelta D ((l:ℝ)/((D₂:ℝ)*(p:ℝ)*(k:ℝ))) else 0 :=
  proposition141_principal_literal_gauss κ
example {D D₁ D₂ p:ℕ} {Ba:ℝ} {κ a:ℕ→ℂ}
    (ha:Proposition141AdmissibleSequence D Ba a) :
    Summable (proposition141PrincipalOuterTerm D D₁ D₂ p κ a) ∧
      (∑'i:ℕ×ℕ,proposition141PrincipalOuterTerm D D₁ D₂ p κ a i)=
        proposition141PrincipalCorrection D D₁ D₂ p κ a :=
  ⟨(proposition141_principal_original_outer_sum ha).summable,
    (proposition141_principal_original_outer_sum ha).tsum_eq⟩
example {D D₁ D₂ p d k:ℕ} (hD:1<D) (hL:2000≤lemma23PaperL D)
    {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ} (hκ:Proposition141KappaBound B κ)
    (hD₁:0<D₁) (hd:0<d) (hq:1≤(D₂:ℝ)*(p:ℝ)*(k:ℝ))
    (hqP:(D₂:ℝ)*(p:ℝ)*(k:ℝ)≤lemma23PaperP D^10) :
    Summable (proposition141PrincipalTerm D D₁ D₂ p d k κ) :=
  (proposition141_principal_inner_bound hD hL hB hκ hD₁ hd hq hqP).1
example (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba) (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ‖proposition141PrincipalTotal χ β κ a‖≤ε*lemma33ActualPrimeMass D :=
  proposition141_uniform_principal_saving Bκ Ba hBκ hBa ε hε

example (D:ℕ) (x:ℝ) : ‖lemma53PaperDeltaOne D x‖=‖lemma53PaperDelta D x‖ :=
  proposition141_deltaOne_norm D x
example {D p:ℕ} [NeZero p] (χ:RealPrimitiveCharacter D) (n:ℕ) (κ:ℕ→ℂ) :
    proposition141PrimeGaussSingle (p:=p) χ n κ 0=0 := by
  simp [proposition141PrimeGaussSingle]
example (D p n:ℕ) (κ:ℕ→ℂ) : proposition141PrimeDivisibleTerm D p n κ 0=0 := by
  simp [proposition141PrimeDivisibleTerm,proposition141DeltaOneTerm]
example {D p n:ℕ} (hp:0<p) (κ:ℕ→ℂ) (j:ℕ) :
    proposition141DeltaOneTerm D κ (fun _=>1) 1 ((D:ℝ)*(p:ℝ)*(n:ℝ)) (p*j)=
      proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)) j :=
  proposition141_divisible_reindexed hp κ j
example {D p n:ℕ} (hp:0<p) (κ:ℕ→ℂ)
    (hs:Summable (proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)))) :
    Summable (proposition141PrimeDivisibleTerm D p n κ) ∧
      (∑'m:ℕ,proposition141PrimeDivisibleTerm D p n κ m)=
        ∑'j:ℕ,proposition141DeltaOneTerm D κ (fun _=>1) p ((D:ℝ)*(n:ℝ)) j :=
  proposition141_divisible_original_sum hp κ hs
example {D p n:ℕ} (hD:1<D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) (hn:n∈proposition141Indices D) :
    (D*n).Coprime p ∧ D.Coprime p := proposition141_prime_short_unit hD hmod hp hn
example {D p:ℕ} [NeZero p] (χ:RealPrimitiveCharacter D) (n m:ℕ) (κ:ℕ→ℂ) :
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (D:ℂ)⁻¹*proposition141PrimeGaussSingle (p:=p) χ n κ m=
      if 0<m then ((D*p:ℕ):ℂ)⁻¹*κ m*
        lemma53PaperDeltaOne D ((m:ℝ)/((D:ℝ)*(p:ℝ)*(n:ℝ)))*
          (∑ψ∈(univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ=>ψ.IsPrimitive),
            gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*
              ψ (m:ZMod p)*ψ⁻¹ (n:ZMod p)) else 0 :=
  proposition141_prime_gauss_single_literal χ n m κ
example {D p:ℕ} [NeZero p] (χ:RealPrimitiveCharacter D)
    (hD:1<D) (hL:2000≤lemma23PaperL D)
    (hmod:2*(D:ℝ)^2*lemma61PaperP4 D≤lemma23PaperP D)
    (hp:p∈lemma56PaperPrimes D) {B:ℝ} (hB:0≤B) {κ:ℕ→ℂ}
    (hκ:Proposition141KappaBound B κ) (a:ℕ→ℂ) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    proposition141PrimeGaussArithmetic (p:=p) χ κ a-
      proposition141PrimeAdditiveArithmetic (p:=p) χ κ a=
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))/(D:ℂ)*
        ((p:ℂ)⁻¹*proposition141PrimeSmallCorrection D p κ a-
          proposition141PrimeDivisibleCorrection D p κ a) :=
  proposition141_prime_source_corrections_identity χ hD hL hmod hp hB hκ a
example (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba) (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ‖∑p∈lemma33PrimeWindow D,if hp:0<p then
          letI : NeZero p := ⟨Nat.ne_of_gt hp⟩
          proposition141ShiftWeight D p β*(proposition141PrimeGaussArithmetic (p:=p) χ κ a-
            proposition141PrimeAdditiveArithmetic (p:=p) χ κ a) else 0‖≤ε*lemma33ActualPrimeMass D :=
  proposition141_uniform_actual_prime_source_saving Bκ Ba hBκ hBa ε hε
example (Bκ Ba:ℝ) (hBκ:0<Bκ) (hBa:0<Ba) (ε:ℝ) (hε:0<ε) :
    ∃D₀:ℕ,2≤D₀ ∧ ∀{D:ℕ} (χ:RealPrimitiveCharacter D),D₀≤D →
      ∀β:ℂ,‖β‖<5*lemma44PaperAlpha D → ∀κ a:ℕ→ℂ,
      Proposition141KappaBound Bκ κ → Proposition141AdmissibleSequence D Ba a →
        ‖proposition141PrincipalTotal χ β κ a+proposition141PrimeFrontCorrectionTotal χ β κ a‖≤
          ε*lemma33ActualPrimeMass D :=
  proposition141_uniform_source_corrections_saving Bκ Ba hBκ hBa ε hε

#print axioms ZhangLS.Spec.proposition71_additive_character_norm
#print axioms ZhangLS.Spec.proposition71_additive_character_correction_norm
#print axioms ZhangLS.Spec.proposition71_normalized_gauss_decomposition
#print axioms ZhangLS.Spec.proposition71_normalized_gauss_nat_decomposition
#print axioms ZhangLS.Spec.proposition71_nat_multiples_tsum
#print axioms ZhangLS.Spec.proposition71_nat_multiples_summable_iff
#print axioms ZhangLS.Spec.proposition141PrincipalWeight
#print axioms ZhangLS.Spec.proposition141PrincipalTerm
#print axioms ZhangLS.Spec.proposition141PrincipalInner
#print axioms ZhangLS.Spec.proposition141PrincipalRow
#print axioms ZhangLS.Spec.proposition141PrincipalCorrection
#print axioms ZhangLS.Spec.proposition141_principal_weight_norm
#print axioms ZhangLS.Spec.proposition141_principal_literal_gauss
#print axioms ZhangLS.Spec.proposition141_moebius_norm_le_one
#print axioms ZhangLS.Spec.proposition141_principal_inner_bound
#print axioms ZhangLS.Spec.proposition141_principal_row_bound
#print axioms ZhangLS.Spec.proposition141_principal_support_scales
#print axioms ZhangLS.Spec.proposition141_principal_harmonic_budget
#print axioms ZhangLS.Spec.proposition141_principal_correction_bound
#print axioms ZhangLS.Spec.proposition141_principal_divisor_convolution
#print axioms ZhangLS.Spec.proposition141PrincipalTotal
#print axioms ZhangLS.Spec.proposition141_principal_gauss_normalization
#print axioms ZhangLS.Spec.proposition141_principal_total_bound
#print axioms ZhangLS.Spec.proposition141PrincipalConstant
#print axioms ZhangLS.Spec.proposition141_principal_constant_pos
#print axioms ZhangLS.Spec.proposition141_principal_quarter_identity
#print axioms ZhangLS.Spec.proposition141_principal_total_quarter_bound
#print axioms ZhangLS.Spec.proposition141_uniform_principal_saving
#print axioms ZhangLS.Spec.proposition141PrincipalOuterTerm
#print axioms ZhangLS.Spec.proposition141_principal_row_of_coefficient_zero
#print axioms ZhangLS.Spec.proposition141_principal_literal_row
#print axioms ZhangLS.Spec.proposition141_principal_outer_off_support
#print axioms ZhangLS.Spec.proposition141_principal_original_outer_sum
#print axioms ZhangLS.Spec.proposition141_principal_positive_indices
#print axioms ZhangLS.Spec.proposition141_deltaOne_norm
#print axioms ZhangLS.Spec.proposition141DeltaOneTerm
#print axioms ZhangLS.Spec.proposition141_deltaOne_term_bound
#print axioms ZhangLS.Spec.proposition141_actual_deltaOne_weighted_sum
#print axioms ZhangLS.Spec.proposition141PrimePhase
#print axioms ZhangLS.Spec.proposition141_prime_phase_value
#print axioms ZhangLS.Spec.proposition141_prime_phase_norm
#print axioms ZhangLS.Spec.proposition141_prime_correction_weight_norm
#print axioms ZhangLS.Spec.proposition141_actual_normalized_gauss_decomposition
#print axioms ZhangLS.Spec.proposition141PrimeSmallCorrection
#print axioms ZhangLS.Spec.proposition141PrimeDivisibleCorrection
#print axioms ZhangLS.Spec.proposition141_tau_five_prime
#print axioms ZhangLS.Spec.proposition141_prime_correction_scales
#print axioms ZhangLS.Spec.proposition141_prime_correction_summable
#print axioms ZhangLS.Spec.proposition141_prime_small_correction_bound
#print axioms ZhangLS.Spec.proposition141_prime_divisible_correction_bound
#print axioms ZhangLS.Spec.proposition141_indices_card_bound
#print axioms ZhangLS.Spec.proposition141_prime_correction_card_budget
#print axioms ZhangLS.Spec.proposition141_prime_corrections_combined_bound
#print axioms ZhangLS.Spec.proposition141PrimeFrontCorrectionTotal
#print axioms ZhangLS.Spec.proposition141_prime_front_total_bound
#print axioms ZhangLS.Spec.proposition141_uniform_prime_front_saving
#print axioms ZhangLS.Spec.proposition141_prime_short_unit
#print axioms ZhangLS.Spec.proposition141PrimeDivisibleTerm
#print axioms ZhangLS.Spec.proposition141_divisible_reindexed
#print axioms ZhangLS.Spec.proposition141_divisible_original_sum
#print axioms ZhangLS.Spec.proposition141PrimeGaussSingle
#print axioms ZhangLS.Spec.proposition141_prime_gauss_single_identity
#print axioms ZhangLS.Spec.proposition141_prime_gauss_single_sum
#print axioms ZhangLS.Spec.proposition141PrimeGaussArithmetic
#print axioms ZhangLS.Spec.proposition141PrimeAdditiveArithmetic
#print axioms ZhangLS.Spec.proposition141_prime_source_corrections_identity
#print axioms ZhangLS.Spec.proposition141_prime_source_total_identity
#print axioms ZhangLS.Spec.proposition141_uniform_actual_prime_source_saving
#print axioms ZhangLS.Spec.proposition141_prime_gauss_single_literal
#print axioms ZhangLS.Spec.proposition141_uniform_source_corrections_saving
