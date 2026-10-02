import ZhangLS.Spec.RealDirichletCharacter

/-!
# Primitive products of characters of coprime levels

Changing the level preserves the conductor. Two characters with coprime
conductors cannot cancel a conductor factor on multiplication. In particular,
the twist in Section 4 is genuinely primitive at level `D * p`.
-/

namespace ZhangLS.Spec

open DirichletCharacter

set_option maxHeartbeats 1000000

/-- Extension to a multiple of the modulus preserves the conductor. -/
theorem lemma44_conductor_changeLevel {n m : ℕ} [NeZero n] [NeZero m]
    (χ : DirichletCharacter ℂ n) (h : n ∣ m) :
    (χ.changeLevel h).conductor = χ.conductor := by
  let ψ := χ.changeLevel h
  let k := ψ.conductor
  letI : NeZero k := ⟨ψ.conductor_ne_zero⟩
  have hψ : DirichletCharacter.changeLevel ψ.conductor_dvd_level ψ.primitiveCharacter = ψ :=
    ψ.changeLevel_primitiveCharacter
  have hcommon : DirichletCharacter.changeLevel (n.dvd_mul_right k) χ =
      DirichletCharacter.changeLevel (k.dvd_mul_left n) ψ.primitiveCharacter := by
    letI : NeZero (n * k * m) := ⟨Nat.mul_ne_zero
      (Nat.mul_ne_zero (NeZero.ne n) (NeZero.ne k)) (NeZero.ne m)⟩
    apply DirichletCharacter.changeLevel_injective (Nat.dvd_mul_right (n * k) m)
    rw [← DirichletCharacter.changeLevel_trans, ← DirichletCharacter.changeLevel_trans]
    have hm : m ∣ n * k * m := Nat.dvd_mul_left m (n * k)
    rw [DirichletCharacter.changeLevel_trans χ h hm,
      DirichletCharacter.changeLevel_trans ψ.primitiveCharacter ψ.conductor_dvd_level hm,
      hψ]
  have hχgcd := DirichletCharacter.factorsThrough_gcd χ ψ.primitiveCharacter hcommon
  have hdiv : χ.conductor ∣ k :=
    (DirichletCharacter.conductor_dvd_of_mem_conductorSet χ hχgcd).trans (Nat.gcd_dvd_right n k)
  have hfactor : ψ.FactorsThrough χ.conductor := by
    refine ⟨χ.conductor_dvd_level.trans h, χ.primitiveCharacter, ?_⟩
    rw [DirichletCharacter.changeLevel_trans χ.primitiveCharacter χ.conductor_dvd_level h,
      χ.changeLevel_primitiveCharacter]
  exact Nat.dvd_antisymm (DirichletCharacter.conductor_dvd_of_mem_conductorSet ψ hfactor) hdiv

/-- On one level, coprime conductors multiply exactly. -/
theorem lemma44_conductor_mul_of_coprime {N : ℕ} [NeZero N]
    (χ ψ : DirichletCharacter ℂ N) (hcop : χ.conductor.Coprime ψ.conductor) :
    (χ * ψ).conductor = χ.conductor * ψ.conductor := by
  have hχ : χ.conductor ∣ (χ * ψ).conductor * ψ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor (χ * ψ) ψ⁻¹
    simp only [mul_inv_cancel_right, DirichletCharacter.conductor_inv] at h
    exact h.trans (Nat.lcm_dvd_mul _ _)
  have hψ : ψ.conductor ∣ (χ * ψ).conductor * χ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor (χ * ψ) χ⁻¹
    rw [show χ * ψ * χ⁻¹ = ψ by simp [mul_comm, mul_left_comm, mul_assoc],
      DirichletCharacter.conductor_inv] at h
    exact h.trans (Nat.lcm_dvd_mul _ _)
  have hχ' : χ.conductor ∣ (χ * ψ).conductor := hcop.dvd_of_dvd_mul_right hχ
  have hψ' : ψ.conductor ∣ (χ * ψ).conductor := hcop.symm.dvd_of_dvd_mul_right hψ
  apply Nat.dvd_antisymm
  · have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor χ ψ
    rw [hcop.lcm_eq_mul] at h
    exact h
  · exact hcop.mul_dvd_of_dvd_of_dvd hχ' hψ'

/-- The actual twist at the product modulus. -/
noncomputable def lemma44CharacterTwist {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) :
    DirichletCharacter ℂ (D * p) :=
  χ.chi.changeLevel (D.dvd_mul_right p) * ψ.changeLevel (p.dvd_mul_left D)

/-- Primitivity of `χψ` is proved rather than passed to the functional equation. -/
theorem lemma44CharacterTwist_isPrimitive {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hψ : ψ.IsPrimitive) (hcop : D.Coprime p) :
    (lemma44CharacterTwist χ ψ).IsPrimitive := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne p)⟩
  have hχcond : (χ.chi.changeLevel (D.dvd_mul_right p)).conductor = D := by
    rw [lemma44_conductor_changeLevel]
    exact χ.primitive
  have hψcond : (ψ.changeLevel (p.dvd_mul_left D)).conductor = p := by
    rw [lemma44_conductor_changeLevel]
    exact hψ
  change (lemma44CharacterTwist χ ψ).conductor = D * p
  unfold lemma44CharacterTwist
  rw [lemma44_conductor_mul_of_coprime, hχcond, hψcond]
  simpa [hχcond, hψcond] using hcop

end ZhangLS.Spec
