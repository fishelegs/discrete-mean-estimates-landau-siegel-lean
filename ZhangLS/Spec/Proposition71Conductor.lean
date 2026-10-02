import ZhangLS.Spec.Lemma56ActualPrimeMassNormalization
import ZhangLS.Spec.Lemma56TwistClassification

/-! # The actual nonprincipal conductor in the error term of Proposition 7.1

These lemmas remove, rather than assume, the modulus-one and exceptional-character
obstructions at the small-conductor application of the proved nonprincipal 5.6.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex DirichletCharacter
set_option maxHeartbeats 2000000

/-- A nonprincipal character has a genuine primitive inducer of modulus greater than one. -/
theorem proposition71_nonprincipal_conductor_gt_one {k : ℕ} [NeZero k]
    (θ : DirichletCharacter ℂ k) (hθ : θ ≠ 1) : 1 < θ.conductor := by
  have h0 := θ.conductor_ne_zero
  have h1 : θ.conductor ≠ 1 := fun h => hθ (eq_one_iff_conductor_eq_one.mpr h)
  omega

/-- Equality of actual natural-number evaluations implies equality of the
characters after induction to a common modulus. -/
theorem proposition71_equal_nat_evaluations_changeLevel {D r : ℕ} [NeZero D] [NeZero r]
    (χ : DirichletCharacter ℂ D) (θ : DirichletCharacter ℂ r)
    (heq : (fun n : ℕ => θ (n : ZMod r)) = (fun n : ℕ => χ (n : ZMod D))) :
    θ.changeLevel (r.dvd_mul_left D) = χ.changeLevel (D.dvd_mul_right r) := by
  letI : NeZero (D*r) := ⟨Nat.mul_ne_zero (NeZero.ne D) (NeZero.ne r)⟩
  ext u
  rw [changeLevel_eq_cast_of_dvd,changeLevel_eq_cast_of_dvd]
  have h := congrFun heq u.val.val
  simpa only [ZMod.natCast_val] using h

/-- Primitive characters of distinct moduli cannot have the same actual values
on the natural numbers. This is the conductor distinction needed in Section 7. -/
theorem proposition71_small_primitive_distinct {D r : ℕ} [NeZero r]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ r)
    (hθ : θ.IsPrimitive) (hr : r < D) :
    (fun n : ℕ => θ (n : ZMod r)) ≠ (fun n : ℕ => χ.chi (n : ZMod D)) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  letI : NeZero (D*r) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne r)⟩
  intro heq
  have hc := congrArg DirichletCharacter.conductor
    (proposition71_equal_nat_evaluations_changeLevel χ.chi θ heq)
  rw [lemma44_conductor_changeLevel θ,lemma44_conductor_changeLevel χ.chi,
    hθ,χ.primitive] at hc
  omega

/-- In particular, the *actual* primitive inducer used in (7.13) is allowed
by nonprincipal Lemma 5.6 whenever its conductor lies below D. -/
theorem proposition71_actual_inducer_admissible {D k : ℕ} [NeZero k]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ k)
    (hθ : θ ≠ 1) (hr : θ.conductor < D) :
    1 < θ.conductor ∧ θ.primitiveCharacter.IsPrimitive ∧
    (fun n : ℕ => θ.primitiveCharacter (n : ZMod θ.conductor)) ≠
      (fun n : ℕ => χ.chi (n : ZMod D)) := by
  letI : NeZero θ.conductor := ⟨θ.conductor_ne_zero⟩
  exact ⟨proposition71_nonprincipal_conductor_gt_one θ hθ,
    θ.primitiveCharacter_isPrimitive,
    proposition71_small_primitive_distinct χ θ.primitiveCharacter
      θ.primitiveCharacter_isPrimitive hr⟩

/-- The Section 7 conductor range r<D automatically lies below the paper's T. -/
theorem proposition71_small_conductor_lt_T {D r : ℕ}
    (hD : 0 < D) (hL : 1 ≤ lemma23PaperL D) (hr : r < D) :
    (r : ℝ) < lemma56PaperT D := by
  have hp : lemma23PaperL D ≤ lemma23PaperL D ^ (11 / 10 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le hL
      (show (1 : ℝ) ≤ 11 / 10 by norm_num)
  have he : Real.exp (lemma23PaperL D) = (D : ℝ) := by
    exact Real.exp_log (by exact_mod_cast hD)
  have hDT : (D : ℝ) ≤ lemma56PaperT D := by
    rw [← he]
    exact Real.exp_le_exp.mpr hp
  exact (by exact_mod_cast hr : (r : ℝ) < (D : ℝ)).trans_le hDT

/-- Uniform actual prime-window decay for every nonprincipal inducer of conductor
below D. Neither a nonprincipal assumption on the inducer nor an inequality of
its evaluations with χ is added as a hypothesis. -/
theorem proposition71_small_actual_inducer_prime_bound :
    ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D k : ℕ} [NeZero k]
      (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ k),
      D₀ ≤ D → 1 < D → 1 ≤ lemma23PaperL D → NormalizedAssumptionA χ →
      θ ≠ 1 → θ.conductor < D → ∀ τ : ℝ, |τ| ≤ D →
        ‖lemma56PrimeSum D θ.primitiveCharacter τ‖ ≤
          C * lemma56PrimeMass D * lemma56Decay D := by
  obtain ⟨C,hC,D₀,hbound⟩ := lemma56_uniform_primitive_prime_window_normalized_bound
  refine ⟨C,hC,D₀,?_⟩
  intro D k _ χ θ hDN hD hL hA hθ hr τ hτ
  letI : NeZero θ.conductor := ⟨θ.conductor_ne_zero⟩
  have hd := proposition71_actual_inducer_admissible χ θ hθ hr
  exact hbound χ θ.primitiveCharacter hDN hD hA hd.2.1 hd.1
    (proposition71_small_conductor_lt_T (by omega) hL hr) hd.2.2 τ hτ

end ZhangLS.Spec
