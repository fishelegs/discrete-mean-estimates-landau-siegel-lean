import ZhangLS.Spec.Lemma56ActualPrimeMassNormalization
import ZhangLS.Spec.Lemma56TwistClassification

/-! # Section 14: actual product-character cancellation

The character in the prime sum is χ times the conjugate of θ. This module
classifies its primitive inducer after the principal and χ-induced θ have
both been removed. Equality and inequality of characters are proved through
induction, including the unit-domain bridge, rather than their displayed names.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter
open scoped ComplexConjugate

/-- The actual product on the common modulus in (14.7) and (14.8). -/
noncomputable def proposition141PrimeCharacter {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : D ∣ N) (θ : DirichletCharacter ℂ N) :
    DirichletCharacter ℂ N := χ.chi.changeLevel hD * θ⁻¹

/-- Equality of genuine natural-number evaluations gives equality after
induction to any common multiple. -/
theorem proposition141_equal_nat_evaluations_induce {d r N : ℕ} [NeZero N]
    (ξ : DirichletCharacter ℂ d) (η : DirichletCharacter ℂ r)
    (hd : d ∣ N) (hr : r ∣ N)
    (heq : (fun n : ℕ => ξ (n : ZMod d)) = (fun n : ℕ => η (n : ZMod r))) :
    ξ.changeLevel hd = η.changeLevel hr := by
  ext u
  rw [changeLevel_eq_cast_of_dvd,changeLevel_eq_cast_of_dvd]
  have h := congrFun heq u.val.val
  simpa only [ZMod.natCast_val] using h

/-- Removing χ-induced θ removes precisely the principal product. -/
theorem proposition141_prime_character_nonprincipal {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : D ∣ N) (θ : DirichletCharacter ℂ N)
    (hne : θ ≠ χ.chi.changeLevel hD) :
    proposition141PrimeCharacter χ hD θ ≠ 1 := by
  intro h
  apply hne
  have h' : χ.chi.changeLevel hD = θ := mul_inv_eq_one.mp h
  exact h'.symm

/-- Removing principal θ removes precisely the χ-induced product. -/
theorem proposition141_prime_character_not_chi_induced {D N : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : D ∣ N) (θ : DirichletCharacter ℂ N)
    (hθ : θ ≠ 1) :
    proposition141PrimeCharacter χ hD θ ≠ χ.chi.changeLevel hD := by
  intro h
  apply hθ
  have hi : θ⁻¹ = 1 := by
    apply mul_left_cancel (a := χ.chi.changeLevel hD)
    simpa only [mul_one] using h
  exact inv_eq_one.mp hi

/-- Both exceptional terms have really been removed before nonprincipal 5.6
can be applied to the primitive inducer of the product. -/
theorem proposition141_actual_product_inducer_admissible {D N : ℕ} [NeZero N]
    (χ : RealPrimitiveCharacter D) (hD : D ∣ N) (θ : DirichletCharacter ℂ N)
    (hθ : θ ≠ 1) (hne : θ ≠ χ.chi.changeLevel hD) :
    let ξ := proposition141PrimeCharacter χ hD θ
    1 < ξ.conductor ∧ ξ.primitiveCharacter.IsPrimitive ∧
      (fun n : ℕ => ξ.primitiveCharacter (n : ZMod ξ.conductor)) ≠
        (fun n : ℕ => χ.chi (n : ZMod D)) := by
  dsimp only
  let ξ := proposition141PrimeCharacter χ hD θ
  have hξ : ξ ≠ 1 := proposition141_prime_character_nonprincipal χ hD θ hne
  have h0 := ξ.conductor_ne_zero
  have h1 : ξ.conductor ≠ 1 := fun h => hξ (eq_one_iff_conductor_eq_one.mpr h)
  change 1 < ξ.conductor ∧ ξ.primitiveCharacter.IsPrimitive ∧ _
  refine ⟨by omega,ξ.primitiveCharacter_isPrimitive,?_⟩
  intro heq
  have he := proposition141_equal_nat_evaluations_induce ξ.primitiveCharacter χ.chi
    ξ.conductor_dvd_level hD heq
  rw [changeLevel_primitiveCharacter] at he
  exact proposition141_prime_character_not_chi_induced χ hD θ hθ he

/-- The actual product conductor is at most D times the conductor of θ,
not the conductor of θ alone. -/
theorem proposition141_product_conductor_le {D N : ℕ} [NeZero N]
    (χ : RealPrimitiveCharacter D) (hD : D ∣ N) (θ : DirichletCharacter ℂ N) :
    (proposition141PrimeCharacter χ hD θ).conductor ≤ D * θ.conductor := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hd := conductor_mul_dvd_lcm_conductor (χ.chi.changeLevel hD) θ⁻¹
  rw [lemma44_conductor_changeLevel χ.chi,χ.primitive,conductor_inv] at hd
  have hDp : 0 < D := Nat.pos_of_ne_zero χ.modulus_ne_zero
  have hθp : 0 < θ.conductor := Nat.pos_of_ne_zero θ.conductor_ne_zero
  exact (Nat.le_of_dvd (Nat.lcm_pos hDp hθp) hd).trans
    (Nat.lcm_le_mul hDp hθp)

/-- On units of the actual common modulus, induction does not alter the
prime character. No assertion of equality on nonunits is used. -/
theorem proposition141_product_inducer_eval {D N : ℕ} [NeZero N]
    (χ : RealPrimitiveCharacter D) (hD : D ∣ N) (θ : DirichletCharacter ℂ N)
    (n : ℕ) (hn : n.Coprime N) :
    (proposition141PrimeCharacter χ hD θ).primitiveCharacter
        (n : ZMod (proposition141PrimeCharacter χ hD θ).conductor) =
      χ.chi (n : ZMod D) * conj (θ (n : ZMod N)) := by
  let ξ := proposition141PrimeCharacter χ hD θ
  have hi := changeLevel_eq_cast_of_dvd ξ.primitiveCharacter ξ.conductor_dvd_level
    (ZMod.unitOfCoprime n hn)
  simp only [changeLevel_primitiveCharacter,ZMod.coe_unitOfCoprime,
    ZMod.cast_natCast ξ.conductor_dvd_level n] at hi
  have hc := changeLevel_eq_cast_of_dvd χ.chi hD (ZMod.unitOfCoprime n hn)
  simp only [ZMod.coe_unitOfCoprime,ZMod.cast_natCast hD n] at hc
  rw [← hi]
  change (χ.chi.changeLevel hD * θ⁻¹) (n : ZMod N) = _
  rw [MulChar.mul_apply,hc,← MulChar.star_apply' θ (n : ZMod N)]
  rfl

end ZhangLS.Spec
