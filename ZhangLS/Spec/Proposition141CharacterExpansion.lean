import ZhangLS.Spec.Lemma33GaussTransform

/-! # Exact additive-to-multiplicative expansion in (14.7)

The common modulus D*k is not prime. These orthogonality and Gauss
expansion lemmas therefore work for every nonzero modulus, with the unit
conditions explicit. The zero branch justifies dropping (l,D*k)=1 only
AFTER the multiplicative characters have been inserted.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical ComplexConjugate

/-- Hermitian orthogonality at arbitrary nonzero modulus, including a
possibly nonunit second argument. -/
theorem proposition141_general_hermitian_orthogonality {N : ℕ} [NeZero N]
    {a b : ZMod N} (ha : IsUnit a) :
    (∑ θ : DirichletCharacter ℂ N, θ a * conj (θ b)) =
      if a=b then (N.totient:ℂ) else 0 := by
  calc
    _ = ∑ θ : DirichletCharacter ℂ N, θ a * θ⁻¹ b := by
      apply sum_congr rfl
      intro θ hθ
      rw [← MulChar.star_apply' θ b]
      rfl
    _ = ∑ θ : DirichletCharacter ℂ N, θ⁻¹ a * θ b := by
      exact Fintype.sum_bijective (fun θ : DirichletCharacter ℂ N => θ⁻¹)
        inv_involutive.bijective
        (fun θ => θ a * θ⁻¹ b) (fun θ => θ⁻¹ a * θ b) (fun θ => by simp)
    _ = _ := by
      obtain ⟨u,rfl⟩ := ha
      simpa only [MulChar.inv_apply,Ring.inverse_unit,ZMod.inv_coe_unit] using
        (DirichletCharacter.sum_char_inv_mul_char_eq (R := ℂ) (n := N) u.isUnit b)

/-- Exact Gauss averaging for composite modulus N; no primitive restriction
is introduced at this stage of the paper. -/
theorem proposition141_general_gauss_average {N : ℕ} [NeZero N]
    (a : ZMod N) (ha : IsUnit a) :
    (∑ θ : DirichletCharacter ℂ N, gaussSum θ⁻¹ ZMod.stdAddChar * θ a) =
      (N.totient:ℂ)*ZMod.stdAddChar a := by
  have horth (b : ZMod N) :
      (∑ θ : DirichletCharacter ℂ N, θ⁻¹ b * θ a) =
        if a=b then (N.totient:ℂ) else 0 := by
    have h := proposition141_general_hermitian_orthogonality (b := b) ha
    rw [← h]
    apply sum_congr rfl
    intro θ hθ
    rw [← MulChar.star_apply' θ b]
    exact mul_comm _ _
  calc
    _ = ∑ b : ZMod N, ZMod.stdAddChar b *
        ∑ θ : DirichletCharacter ℂ N, θ⁻¹ b * θ a := by
      simp only [gaussSum,sum_mul,mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro θ hθ
      ring
    _ = _ := by simp_rw [horth]; simp [mul_comm]

/-- Character expansion of the actual additive phase in (14.7), with
p represented by its proved unit in the common modulus. -/
theorem proposition141_additive_phase_character_expansion {N : ℕ} [NeZero N]
    (l : ZMod N) (hl : IsUnit l) (p : (ZMod N)ˣ) :
    ZMod.stdAddChar (-l * ((p⁻¹ : (ZMod N)ˣ) : ZMod N)) =
      (N.totient:ℂ)⁻¹ * ∑ θ : DirichletCharacter ℂ N,
        gaussSum θ⁻¹ ZMod.stdAddChar * θ (-l) * conj (θ (p:ZMod N)) := by
  have ha : IsUnit (-l * ((p⁻¹ : (ZMod N)ˣ) : ZMod N)) := hl.neg.mul (p⁻¹).isUnit
  have hh := proposition141_general_gauss_average _ ha
  have he (θ : DirichletCharacter ℂ N) :
      θ (-l * ((p⁻¹ : (ZMod N)ˣ) : ZMod N)) = θ (-l) * conj (θ (p:ZMod N)) := by
    rw [map_mul]
    change θ (-l) * θ ((p⁻¹ : (ZMod N)ˣ) : ZMod N) =
      θ (-l) * star (θ (p:ZMod N))
    rw [MulChar.star_apply',MulChar.inv_apply,Ring.inverse_unit]
  simp_rw [he] at hh
  have hphi : (N.totient:ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))).ne'
  calc
    _ = (N.totient:ℂ)⁻¹ * ((N.totient:ℂ)*ZMod.stdAddChar (-l * ((p⁻¹ : (ZMod N)ˣ) : ZMod N))) := by
      field_simp
    _ = _ := by rw [← hh]; simp_rw [mul_assoc]

/-- The omitted nonunit l terms vanish because of θ(-l), for every θ,
not because the additive exponential itself vanishes. -/
theorem proposition141_nonunit_character_phase_zero {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (l p : ZMod N) (hl : ¬IsUnit l) :
    gaussSum θ⁻¹ ZMod.stdAddChar * θ (-l) * conj (θ p) = 0 := by
  have hneg : ¬IsUnit (-l) := by
    intro hh
    exact hl (by simpa only [neg_neg] using hh.neg)
  rw [MulChar.map_nonunit θ hneg,mul_zero,zero_mul]

end ZhangLS.Spec
