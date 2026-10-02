import ZhangLS.Spec.FixedModulusGcdSums
import ZhangLS.Spec.Proposition141Objects

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex
open scoped Classical ComplexConjugate

/-- Regression against the unchanged original Proposition14.1 arithmetic
object: its arbitrary kappa sequence, actual chi, and Delta kernel survive. -/
theorem fixedDGcd_original_innerMain_reindex {D : ℕ} (χ : RealPrimitiveCharacter D)
    (κ : ℕ → ℂ) (p d k : ℕ) :
    proposition141InnerMain χ κ p d k =
      ∑' i : fixedDCoprimeGcdIndex D k,
        χ.chi (((i.1.val:ℕ)*(i.2.val:ℕ):ℕ):ZMod D) *
          κ (d*((i.1.val:ℕ)*(i.2.val:ℕ))) *
          lemma53PaperDelta D (((i.1.val*i.2.val:ℕ+):ℝ)/((D:ℝ)*p*k)) := by
  unfold proposition141InnerMain
  simpa only [PNat.mul_coe] using fixedDCoprimeGcd_filtered_tsum D k
    (fun l : ℕ+ => χ.chi ((l:ℕ):ZMod D)*κ (d*l)*
      lemma53PaperDelta D ((l:ℝ)/((D:ℝ)*p*k)))

def fixedDGcd_nonSquarefreeRegression : fixedDCoprimeGcdIndex 12 5 :=
  ⟨⟨⟨6,by decide⟩,by decide,by decide⟩,⟨⟨3,by decide⟩,by decide⟩⟩

example : ((fixedDCoprimeGcdLift fixedDGcd_nonSquarefreeRegression).val:ℕ)=18 := rfl
example : Nat.gcd ((fixedDCoprimeGcdLift fixedDGcd_nonSquarefreeRegression).val:ℕ) 12=6 :=
  fixedDCoprimeGcd_lift_gcd _
example : ¬Nat.Coprime 6 (12/6) := by decide
example : ¬Nat.Coprime 3 12 := by decide
example : IsUnit (3:ZMod ((12/6)*5)) :=
  fixedDGcd_quotient_isUnit (fixedDCoprimeGcdForget fixedDGcd_nonSquarefreeRegression)
    (by decide)
example : ZMod.stdAddChar (-(18:ZMod 60)*(7:ZMod 60)⁻¹) =
    ZMod.stdAddChar (-(3:ZMod 10)*(7:ZMod 10)⁻¹) :=
  fixedDGcd_divisor_inverse_phase (D:=12) (d:=6) (k:=5) (p:=7) (by decide) (by decide) 3

example : ZMod.stdAddChar (-(60:ZMod 12)*(5:ZMod 12)⁻¹) = (1:ℂ) := by
  have h : ZMod.stdAddChar (-(60:ZMod 12)*(5:ZMod 12)⁻¹) =
      ZMod.stdAddChar (-(5:ZMod 1)*(5:ZMod 1)⁻¹) :=
    fixedDGcd_divisor_inverse_phase (D:=12) (d:=12) (k:=1) (p:=5)
      (by decide) (by decide) 5
  have hzero : -(5:ZMod 1)*(5:ZMod 1)⁻¹ = 0 := Subsingleton.elim _ _
  simpa only [hzero, AddChar.map_zero_eq_one] using h

example : IsUnit (0:ZMod 1) := by
  rw [Subsingleton.elim (0:ZMod 1) 1]
  exact isUnit_one

example : Nat.Coprime 0 1 := by decide

#check proposition141InnerMain
#check proposition141MainTerm
#check proposition141ThetaTwo
#check Proposition141Target
#check fixedDGcd_original_deltaOne_phase
#check fixedDGcd_phase_character_expansion

#print axioms fixedDGcd_divisor_quotient_pos
#print axioms fixedDGcd_divisor_inverse_phase
#print axioms fixedDGcd_quotient_isUnit
#print axioms fixedDGcd_quotient_p_isUnit
#print axioms fixedDGcd_phase_character_expansion
#print axioms fixedDGcdLift
#print axioms fixedDGcd_lift_gcd
#print axioms fixedDGcd_lift_injective
#print axioms fixedDGcd_lift_surjective
#print axioms fixedDGcdEquiv
#print axioms fixedDGcd_coprime_iff
#print axioms fixedDGcd_quotient_pos
#print axioms fixedDGcd_tsum_reindex
#print axioms fixedDGcd_coprime_tsum_reindex
#print axioms fixedDGcd_nested_tsum
#print axioms fixedDGcd_cast_inverse
#print axioms fixedDGcd_additive_quotient
#print axioms fixedDGcd_inverse_phase_quotient
#print axioms fixedDGcd_inverse_divisor
#print axioms fixedDGcd_inverse_quotient
#print axioms fixedDGcd_original_delta_phase
#print axioms fixedDGcd_original_deltaOne_phase
#print axioms fixedDCoprimeGcdForget
#print axioms fixedDCoprimeGcdLift
#print axioms fixedDCoprimeGcd_lift_gcd
#print axioms fixedDCoprimeGcd_lift_injective
#print axioms fixedDCoprimeGcd_lift_surjective
#print axioms fixedDCoprimeGcdEquiv
#print axioms fixedDCoprimeGcd_tsum_reindex
#print axioms fixedDGcd_character_zero_extension
#print axioms fixedDGcd_scaled_kernel_argument
#print axioms fixedDCoprimeGcd_filtered_tsum
#print axioms fixedDCoprimeGcd_filtered_nested_tsum
#print axioms fixedDGcd_original_innerMain_reindex

#print axioms fixedDGcdIndex
#print axioms fixedDCoprimeGcdIndex
#print axioms fixedDGcd_nonSquarefreeRegression

end ZhangLS.Spec
