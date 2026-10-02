import ZhangLS.Spec.CoprimeGaussPrimeAverage
import ZhangLS.Spec.AdditiveReciprocity
import ZhangLS.Spec.InducedGaussMainCharacters
set_option autoImplicit false
attribute [local instance] Classical.propDecidable
open ZhangLS.Spec Complex DirichletCharacter Finset

example {m n : ℕ} [NeZero m] [NeZero n] (hmn : m.Coprime n)
    (a : ZMod m) (b : ZMod n) :
    coprimeGaussResidueEquiv hmn (a,b)=((n*a.val+m*b.val:ℕ):ZMod (m*n)) :=
  coprimeGauss_residue_nat hmn a b

example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p) (hcop : D.Coprime p) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    gaussSum (lemma44CharacterTwist χ ψ) ZMod.stdAddChar =
      χ.chi (p:ZMod D)*ψ (D:ZMod p)*gaussSum χ.chi ZMod.stdAddChar*gaussSum ψ ZMod.stdAddChar :=
  coprimeGauss_real_twist_formula χ ψ hcop

example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (hcop : D.Coprime p) (m n : ZMod p) (hm : IsUnit m) (hn : IsUnit n) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (∑ ψ ∈ (univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
      gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*ψ m*ψ⁻¹ n) =
      (gaussSum χ.chi ZMod.stdAddChar*χ.chi (p:ZMod D))*
        ((p.totient:ℂ)*ZMod.stdAddChar (m*((D:ZMod p)*n)⁻¹)+1) :=
  coprimeGauss_primitive_prime_average χ hp hcop m n hm hn

example {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (m n : ZMod p) (h : ¬IsUnit m ∨ ¬IsUnit n) :
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    (∑ ψ ∈ (univ:Finset (DirichletCharacter ℂ p)).filter (fun ψ => ψ.IsPrimitive),
      gaussSum (lemma44CharacterTwist χ ψ⁻¹) ZMod.stdAddChar*ψ m*ψ⁻¹ n)=0 :=
  coprimeGauss_primitive_average_nonunit χ m n h
example {D N p : ℕ} [NeZero N] [NeZero p] (hcop : N.Coprime p) (l : ℕ) :
    lemma53PaperDeltaOne D ((l:ℝ)/((N:ℝ)*(p:ℝ))) *
      ZMod.stdAddChar ((l:ZMod p)*(N:ZMod p)⁻¹) =
    lemma53PaperDelta D ((l:ℝ)/((N:ℝ)*(p:ℝ))) *
      ZMod.stdAddChar (-(l:ZMod N)*(p:ZMod N)⁻¹) :=
  additiveReciprocity_delta hcop l
-- GENERATED AXIOM CHECKS
#print axioms ZhangLS.Spec.additiveReciprocity_stdAddChar
#print axioms ZhangLS.Spec.additiveReciprocity_product_phase
#print axioms ZhangLS.Spec.additiveReciprocity_delta
#print axioms ZhangLS.Spec.coprimeGauss_prime_average_summand
#print axioms ZhangLS.Spec.coprimeGauss_full_prime_average
#print axioms ZhangLS.Spec.coprimeGauss_primitive_prime_average
#print axioms ZhangLS.Spec.coprimeGauss_primitive_prime_average_error
#print axioms ZhangLS.Spec.coprimeGauss_primitive_average_nonunit
#print axioms ZhangLS.Spec.coprimeGauss_real_twist_values
#print axioms ZhangLS.Spec.coprimeGauss_real_twist_formula
#print axioms ZhangLS.Spec.coprimeGaussResidueEquiv
#print axioms ZhangLS.Spec.coprimeGauss_residue_coordinates
#print axioms ZhangLS.Spec.coprimeGauss_residue_nat
#print axioms ZhangLS.Spec.coprimeGauss_additive_factorization
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_formula_dvd
#print axioms ZhangLS.Spec.inducedGauss_conductor_formula
#print axioms ZhangLS.Spec.inducedGauss_level_one_value
#print axioms ZhangLS.Spec.inducedGauss_primitive_norm
#print axioms ZhangLS.Spec.inducedGauss_mobius_norm_le_one
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_norm_le
#print axioms ZhangLS.Spec.inducedGauss_norm_le_sqrt_conductor
#print axioms ZhangLS.Spec.inducedGauss_inverse_norm_le_sqrt_conductor
#print axioms ZhangLS.Spec.inducedGauss_nonprincipal_conductor_gt_one
#print axioms ZhangLS.Spec.inducedGauss_sum_zmod_eq_range
#print axioms ZhangLS.Spec.inducedGauss_sum_range_multiples
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_nat
#print axioms ZhangLS.Spec.inducedGauss_mobius_indicator
#print axioms ZhangLS.Spec.inducedGauss_mobius_indicator_divisors
#print axioms ZhangLS.Spec.inducedGauss_scaled_additive
#print axioms ZhangLS.Spec.inducedGauss_coprime_sum_mobius
#print axioms ZhangLS.Spec.inducedGauss_divisor_inner
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_formula
#print axioms ZhangLS.Spec.inducedGaussInflation
#print axioms ZhangLS.Spec.inducedGauss_inflation_zero
#print axioms ZhangLS.Spec.inducedGauss_inflation_one
#print axioms ZhangLS.Spec.inducedGauss_inflation_formula
#print axioms ZhangLS.Spec.inducedGauss_principal_value
#print axioms ZhangLS.Spec.inducedGauss_changeLevel_neg_nat
#print axioms ZhangLS.Spec.inducedGauss_phase_product
#print axioms ZhangLS.Spec.inducedGauss_real_changeLevel_inv
#print axioms ZhangLS.Spec.inducedGauss_real_phase_product
#print axioms ZhangLS.Spec.inducedGauss_totient_denominator
#print axioms ZhangLS.Spec.inducedGauss_coprime_filter
#print axioms ZhangLS.Spec.inducedGauss_real_square
#print axioms ZhangLS.Spec.proposition71_prime_primitive_iff
#print axioms ZhangLS.Spec.proposition71_full_gauss_average
#print axioms ZhangLS.Spec.proposition71_principal_gauss
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_average
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_error
#print axioms ZhangLS.Spec.proposition71_gauss_average_nonunit
#print axioms ZhangLS.Spec.proposition71_primitive_gauss_average_all
