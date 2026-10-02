import ZhangLS.Spec.CoprimeGaussResidues
import ZhangLS.Spec.Lemma44ProductDirichletSeries

/-! # Coprime Gauss product for the actual χψ twist

The first character is the original real primitive χ; the second is arbitrary,
so principal-character subtraction is covered as well. The proof is a genuine
CRT permutation of all residues, with the existing all-nonunit product bridge.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter Finset
open scoped Classical

/-- Exact character factors under the nonstandard CRT permutation, valid
on nonunits as well because the actual product-character bridge covers them. -/
theorem coprimeGauss_real_twist_values {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (hcop : D.Coprime p)
    (a : ZMod D) (b : ZMod p) :
    lemma44CharacterTwist χ ψ (coprimeGaussResidueEquiv hcop (a,b)) =
      χ.chi (p:ZMod D)*ψ (D:ZMod p)*χ.chi a*ψ b := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  rw [coprimeGauss_residue_nat,lemma44CharacterTwist_eval_nat]
  simp only [Nat.cast_add,Nat.cast_mul,ZMod.natCast_zmod_val,ZMod.natCast_self,
    zero_mul,add_zero,zero_add,map_mul]
  ring

/-- Genuine coprime Gauss product, including nonprimitive ψ. -/
theorem coprimeGauss_real_twist_formula {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (hcop : D.Coprime p) :
    letI : NeZero D := ⟨χ.modulus_ne_zero⟩
    letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    gaussSum (lemma44CharacterTwist χ ψ) ZMod.stdAddChar =
      χ.chi (p:ZMod D)*ψ (D:ZMod p)*gaussSum χ.chi ZMod.stdAddChar*gaussSum ψ ZMod.stdAddChar := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let e := coprimeGaussResidueEquiv hcop
  let f : ZMod (D*p) → ℂ := fun z => lemma44CharacterTwist χ ψ z*ZMod.stdAddChar z
  have he : (∑ ab : ZMod D × ZMod p, f (e ab))=∑ z : ZMod (D*p), f z :=
    Fintype.sum_equiv e _ _ (fun _ => rfl)
  change (∑ z : ZMod (D*p), f z)=_
  rw [← he,Fintype.sum_prod_type]
  dsimp only [f,e]
  simp_rw [coprimeGauss_real_twist_values χ ψ hcop,coprimeGauss_additive_factorization hcop]
  unfold gaussSum
  simp only [mul_sum,sum_mul]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro a ha
  apply sum_congr rfl
  intro b hb
  ring

end ZhangLS.Spec
