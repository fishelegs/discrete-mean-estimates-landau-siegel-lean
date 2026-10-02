import ZhangLS.Spec.Proposition141SmallConductor

/-! # Section 14 off-diagonal conductor exclusion

For D=D₁D₂ with D₁>1 and (D₁,k)=1, χ cannot be induced to
D₂k. The proof uses divisibility of actual conductors, not different names.
-/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Complex DirichletCharacter
open scoped ComplexConjugate

/-- The precise elementary obstruction in the final paragraph of Section 14. -/
theorem proposition141_off_diagonal_not_dvd {D D₁ D₂ k : ℕ}
    (hD : D = D₁*D₂) (hD₂ : 0 < D₂) (hD₁ : 1 < D₁)
    (hk : D₁.Coprime k) : ¬D ∣ D₂*k := by
  intro hd
  have hd' : D₂*D₁ ∣ D₂*k := by simpa only [hD,mul_comm D₁ D₂] using hd
  have hdiv : D₁ ∣ k := (Nat.mul_dvd_mul_iff_left hD₂).mp hd'
  have hone : D₁ = 1 := (hk.gcd_eq_one ▸ Nat.gcd_eq_left hdiv).symm
  omega

/-- Characters from a modulus not divisible by D cannot become χ after
induction to D times that modulus. -/
theorem proposition141_lift_ne_chi_of_not_dvd {D m : ℕ} [NeZero m]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ m)
    (hDm : ¬D ∣ m) :
    θ.changeLevel (m.dvd_mul_left D) ≠ χ.chi.changeLevel (D.dvd_mul_right m) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*m) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne m)⟩
  intro h
  have hc := congrArg DirichletCharacter.conductor h
  rw [lemma44_conductor_changeLevel θ,lemma44_conductor_changeLevel χ.chi,χ.primitive] at hc
  exact hDm (hc ▸ θ.conductor_dvd_level)

/-- Both admissibility exclusions for the actual off-diagonal product's
primitive inducer. Only θ≠principal is assumed; χ-exclusion is proved. -/
theorem proposition141_off_diagonal_inducer_admissible {D m : ℕ} [NeZero m]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ m)
    (hDm : ¬D ∣ m) (hθ : θ ≠ 1) :
    let ξ := lemma44CharacterTwist χ θ⁻¹
    1 < ξ.conductor ∧ ξ.primitiveCharacter.IsPrimitive ∧
      (fun n : ℕ => ξ.primitiveCharacter (n : ZMod ξ.conductor)) ≠
        (fun n : ℕ => χ.chi (n : ZMod D)) := by
  letI : NeZero (D*m) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne m)⟩
  have hn : θ.changeLevel (m.dvd_mul_left D) ≠ 1 := by
    intro h
    exact hθ ((changeLevel_eq_one_iff (m.dvd_mul_left D)).mp h)
  have he : proposition141PrimeCharacter χ (D.dvd_mul_right m)
      (θ.changeLevel (m.dvd_mul_left D)) = lemma44CharacterTwist χ θ⁻¹ := by
    simp only [proposition141PrimeCharacter,lemma44CharacterTwist,map_inv]
  have hh := proposition141_actual_product_inducer_admissible χ (D.dvd_mul_right m)
    (θ.changeLevel (m.dvd_mul_left D)) hn
    (proposition141_lift_ne_chi_of_not_dvd χ θ hDm)
  dsimp only at hh ⊢
  rw [he] at hh
  exact hh

/-- Product-conductor bound for the off-diagonal prime sum, with the
original θ conductor retained after induction. -/
theorem proposition141_off_diagonal_product_conductor_le {D m : ℕ} [NeZero m]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ m) :
    (lemma44CharacterTwist χ θ⁻¹).conductor ≤ D*θ.conductor := by
  letI : NeZero (D*m) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne m)⟩
  have h := proposition141_product_conductor_le χ (D.dvd_mul_right m)
    (θ.changeLevel (m.dvd_mul_left D))
  simpa only [proposition141PrimeCharacter,lemma44CharacterTwist,map_inv,
    lemma44_conductor_changeLevel θ] using h

/-- Unit evaluation of the actual off-diagonal product's primitive inducer. -/
theorem proposition141_off_diagonal_inducer_eval {D m : ℕ} [NeZero m]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ m)
    (n : ℕ) (hn : n.Coprime (D*m)) :
    (lemma44CharacterTwist χ θ⁻¹).primitiveCharacter
      (n : ZMod (lemma44CharacterTwist χ θ⁻¹).conductor) =
        χ.chi (n : ZMod D) * conj (θ (n : ZMod m)) := by
  letI : NeZero (D*m) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne m)⟩
  let ξ := lemma44CharacterTwist χ θ⁻¹
  have hi := changeLevel_eq_cast_of_dvd ξ.primitiveCharacter ξ.conductor_dvd_level
    (ZMod.unitOfCoprime n hn)
  simp only [changeLevel_primitiveCharacter,ZMod.coe_unitOfCoprime,
    ZMod.cast_natCast ξ.conductor_dvd_level n] at hi
  rw [← hi,lemma44CharacterTwist_eval_nat,← MulChar.star_apply' θ (n : ZMod m)]
  rfl

/-- The actual off-diagonal product also falls under the proved nonprincipal
5.6. Its source θ need not be primitive; the conductor bound is genuine. -/
theorem proposition141_small_off_diagonal_inducer_prime_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, 2 ≤ D₀ ∧
      ∀ {D m : ℕ} [NeZero m] (χ : RealPrimitiveCharacter D)
      (θ : DirichletCharacter ℂ m),
      D₀ ≤ D → NormalizedAssumptionA χ → ¬D ∣ m → θ ≠ 1 → θ.conductor < D^3 →
      ∀ τ : ℝ, |τ| ≤ D →
        ‖lemma56PrimeSum D (lemma44CharacterTwist χ θ⁻¹).primitiveCharacter τ‖ ≤
          C * lemma56PrimeMass D * lemma56Decay D := by
  obtain ⟨C,hC,D₀,hD₀,hbound⟩ := proposition141_small_product_inducer_prime_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D m _ χ θ hDN hA hDm hθ hr τ hτ
  letI : NeZero (D*m) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne m)⟩
  have hn : θ.changeLevel (m.dvd_mul_left D) ≠ 1 := by
    intro h
    exact hθ ((changeLevel_eq_one_iff (m.dvd_mul_left D)).mp h)
  have hc : (θ.changeLevel (m.dvd_mul_left D)).conductor < D^3 := by
    rwa [lemma44_conductor_changeLevel θ]
  have he : proposition141PrimeCharacter χ (D.dvd_mul_right m)
      (θ.changeLevel (m.dvd_mul_left D)) = lemma44CharacterTwist χ θ⁻¹ := by
    simp only [proposition141PrimeCharacter,lemma44CharacterTwist,map_inv]
  have hh := hbound χ (D.dvd_mul_right m) (θ.changeLevel (m.dvd_mul_left D)) hDN hA hn
    (proposition141_lift_ne_chi_of_not_dvd χ θ hDm) hc τ hτ
  rw [he] at hh
  exact hh

end ZhangLS.Spec
