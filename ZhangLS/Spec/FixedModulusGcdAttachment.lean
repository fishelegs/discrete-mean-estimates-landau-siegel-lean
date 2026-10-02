import ZhangLS.Spec.FixedModulusGcdBridge

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex
open scoped Classical ComplexConjugate

/-- The quotient modulus in the actual fixed-D decomposition is nonzero. -/
theorem fixedDGcd_divisor_quotient_pos {D d : ℕ} [NeZero D] [NeZero d]
    (hd : d ∣ D) : 0 < D/d :=
  Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne D)) hd)
    (Nat.pos_of_ne_zero (NeZero.ne d))

private theorem inverse_phase_modulus_congr {N M : ℕ} [NeZero N] [NeZero M]
    (h : N = M) (a p : ℕ) :
    ZMod.stdAddChar (-(a:ZMod N)*(p:ZMod N)⁻¹) =
      ZMod.stdAddChar (-(a:ZMod M)*(p:ZMod M)⁻¹) := by
  subst M
  rfl

/-- Exact reduction of the original D*k phase to (D/d)*k. -/
theorem fixedDGcd_divisor_inverse_phase {D d k p : ℕ} [NeZero D] [NeZero d] [NeZero k]
    (hd : d ∣ D) (hp : Nat.Coprime p (D*k)) (l : ℕ) :
    letI : NeZero (D*k) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne k)⟩
    letI : NeZero ((D/d)*k) :=
      ⟨Nat.mul_ne_zero (Nat.ne_of_gt (fixedDGcd_divisor_quotient_pos hd)) (NeZero.ne k)⟩
    ZMod.stdAddChar (-((d*l:ℕ):ZMod (D*k))*(p:ZMod (D*k))⁻¹) =
      ZMod.stdAddChar (-(l:ZMod ((D/d)*k))*(p:ZMod ((D/d)*k))⁻¹) := by
  letI : NeZero (D*k) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne k)⟩
  letI : NeZero ((D/d)*k) :=
    ⟨Nat.mul_ne_zero (Nat.ne_of_gt (fixedDGcd_divisor_quotient_pos hd)) (NeZero.ne k)⟩
  have hmod : d*((D/d)*k) = D*k := by rw [← mul_assoc, Nat.mul_div_cancel' hd]
  have hp' : Nat.Coprime p (d*((D/d)*k)) := by rwa [hmod]
  have h := fixedDGcd_inverse_phase_quotient (d:=d) (M:=(D/d)*k) hp' l
  letI : NeZero (d*((D/d)*k)) := ⟨by rw [hmod]; exact NeZero.ne (D*k)⟩
  exact (inverse_phase_modulus_congr hmod.symm (d*l) p).trans h

/-- The old (l,k)=1 restriction, combined with the genuine gcd quotient,
proves the remaining l1 is a unit before character expansion. -/
theorem fixedDGcd_quotient_isUnit {D : ℕ} (i : fixedDGcdIndex D) {k : ℕ}
    (hk : Nat.Coprime (fixedDGcdLift i : ℕ) k) :
    IsUnit ((i.2.val:ℕ) : ZMod ((D/(i.1.val:ℕ))*k)) := by
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  exact i.2.property.mul_right ((fixedDGcd_coprime_iff i k).mp hk).2

/-- Coprimality of p in the original modulus implies its unit property
in the exact smaller modulus. -/
theorem fixedDGcd_quotient_p_isUnit {D d k p : ℕ} (hd : d ∣ D)
    (hp : Nat.Coprime p (D*k)) : IsUnit (p : ZMod ((D/d)*k)) := by
  apply (ZMod.isUnit_iff_coprime _ _).mpr
  exact hp.of_dvd_right (Nat.mul_dvd_mul_right (Nat.div_dvd_of_dvd hd) k)

/-- Character expansion is applied only after the fixed-D gcd factor is
removed. Both residue units are proved from the original hypotheses. -/
theorem fixedDGcd_phase_character_expansion {D k p : ℕ} [NeZero D] [NeZero k]
    (i : fixedDGcdIndex D) (hp : Nat.Coprime p (D*k))
    (hk : Nat.Coprime (fixedDGcdLift i : ℕ) k) :
    letI : NeZero (D*k) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne k)⟩
    letI : NeZero ((D/(i.1.val:ℕ))*k) :=
      ⟨Nat.mul_ne_zero (Nat.ne_of_gt (fixedDGcd_quotient_pos
        (Nat.pos_of_ne_zero (NeZero.ne D)) i)) (NeZero.ne k)⟩
    ZMod.stdAddChar (-((fixedDGcdLift i : ℕ) : ZMod (D*k))*(p:ZMod (D*k))⁻¹) =
      (((D/(i.1.val:ℕ))*k).totient:ℂ)⁻¹ *
        ∑ θ : DirichletCharacter ℂ ((D/(i.1.val:ℕ))*k),
          gaussSum θ⁻¹ ZMod.stdAddChar * θ (-((i.2.val:ℕ):ZMod ((D/(i.1.val:ℕ))*k))) *
            conj (θ (p:ZMod ((D/(i.1.val:ℕ))*k))) := by
  letI : NeZero (i.1.val:ℕ) := ⟨Nat.ne_of_gt i.1.val.property⟩
  letI : NeZero (D*k) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne k)⟩
  letI : NeZero ((D/(i.1.val:ℕ))*k) :=
    ⟨Nat.mul_ne_zero (Nat.ne_of_gt (fixedDGcd_quotient_pos
      (Nat.pos_of_ne_zero (NeZero.ne D)) i)) (NeZero.ne k)⟩
  have hphase := fixedDGcd_divisor_inverse_phase i.1.property hp (i.2.val:ℕ)
  simp only [fixedDGcdLift, PNat.mul_coe]
  rw [hphase]
  have hu := fixedDGcd_quotient_p_isUnit i.1.property hp
  obtain ⟨u,hu⟩ := hu
  have hexp := proposition141_additive_phase_character_expansion
    ((i.2.val:ℕ):ZMod ((D/(i.1.val:ℕ))*k)) (fixedDGcd_quotient_isUnit i hk) u
  rw [← hu, ZMod.inv_coe_unit]
  exact hexp

end ZhangLS.Spec
