import ZhangLS.Spec.CompositeRamanujanCenterPrimePowers

set_option autoImplicit false
namespace ZhangLS.Spec.CompositeRamanujanCenterRegression
open ZhangLS.Spec.CompositeRamanujanCenter Complex
open scoped Classical ComplexConjugate

theorem totient_twelve : (12 : ℕ).totient = 4 := by decide
theorem totient_eight : (8 : ℕ).totient = 4 := by decide
theorem totient_six : (6 : ℕ).totient = 2 := by decide
theorem totient_three : (3 : ℕ).totient = 2 := by decide
theorem totient_two : (2 : ℕ).totient = 1 := by decide

theorem modulus_one_zero : ramanujanSum 1 0 = 1 := ramanujanSum_one 0
theorem modulus_one_seven : ramanujanSum 1 7 = 1 := ramanujanSum_one 7
theorem zero_composite : ramanujanSum 12 0 = 4 := by
  rw [ramanujanSum_zero]
  norm_num [totient_twelve]

theorem prime_power_coprime : ramanujanSum 8 1 = 0 := by
  have h := prime_power_coprime_zero (q := 2) (by decide) 1 1 (by decide)
  exact h

theorem prime_power_middle_two : ramanujanSum 8 4 = -4 := by
  have h := prime_power_middle (q := 2) (by decide) 2 1 (by decide)
  norm_num at h
  exact h

theorem prime_power_middle_three : ramanujanSum 9 6 = -3 := by
  have h := prime_power_middle (q := 3) (by decide) 1 2 (by decide)
  simpa using h

theorem prime_power_divisible : ramanujanSum 8 16 = 4 := by
  rw [ramanujanSum_divisible 8 16 (by decide)]
  norm_num [totient_eight]

/-- gcd(12,6)=6, quotient 2, so the normalized center is -1. -/
theorem composite_gcd_middle : ramanujanSum 12 6 = -4 := by
  have h := normalized_gcd 12 6
  norm_num [totient_twelve, totient_two,
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2)] at h
  linear_combination 4 * h

/-- gcd(12,4)=4, quotient 3, so the normalized center is -1/2. -/
theorem composite_gcd_three : ramanujanSum 12 4 = -2 := by
  have h := normalized_gcd 12 4
  norm_num [totient_twelve, totient_three,
    ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)] at h
  linear_combination 4 * h

/-- gcd(12,2)=2, quotient 6 squarefree composite; the center is +1/2. -/
theorem composite_squarefree_quotient : ramanujanSum 12 2 = 2 := by
  have h := normalized_gcd 12 2
  have hm : ArithmeticFunction.moebius 6 = 1 := by
    have h6 := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (by decide : Nat.Coprime 2 3)
    rw [ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2),
      ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)] at h6
    norm_num at h6
    exact h6
  norm_num [totient_twelve, totient_six, hm] at h
  linear_combination 4 * h

theorem divisor_formula_composite : ramanujanSum 12 6 =
    ∑ g ∈ (Nat.gcd 12 6).divisors,
      (g : ℂ) * (ArithmeticFunction.moebius (12 / g) : ℂ) :=
  ramanujanSum_divisor_formula 12 6

theorem original_inverse_descends : reciprocalPhase 12 4 5 = reciprocalPhase 3 1 5 := by
  have h := scaled_reciprocal_phase (d := 4) (k := 3) 1 5 (by decide)
  exact h

theorem composite_centered_expansion :
    reciprocalPhase 12 4 5 + (1 / 2 : ℂ) = nonprincipalExpansion 3 1 5 := by
  have h := gcd_nonprincipal_expansion 12 4 5 (by decide)
  rw [composite_gcd_three] at h
  norm_num [totient_twelve] at h
  exact h

theorem quotient_one_zero :
    reciprocalPhase 12 24 5 - ramanujanSum 12 24 / ((12 : ℕ).totient : ℂ) = 0 :=
  quotient_one_centered_zero 12 24 5 (by decide)

theorem numerator_zero_centered :
    reciprocalPhase 12 0 5 - ramanujanSum 12 0 / ((12 : ℕ).totient : ℂ) = 0 :=
  divisible_centered_zero 12 0 5 (dvd_zero _)

/-- This imprimitive level is retained in the family; only its conductor-one terms leave. -/
theorem level_nine_no_conductor_one (θ : DirichletCharacter ℂ 9)
    (hθ : θ ∈ nonprincipalCharacters 9) : 1 < θ.conductor :=
  nonprincipal_conductor_gt_one hθ

theorem imprimitive_member (θ : DirichletCharacter ℂ 3) (hθ : θ ≠ 1) :
    θ.changeLevel (by decide : 3 ∣ 9) ∈ nonprincipalCharacters 9 := by
  simp only [nonprincipalCharacters, Finset.mem_filter, Finset.mem_univ, true_and]
  exact fun h => hθ ((DirichletCharacter.changeLevel_eq_one_iff (by decide : 3 ∣ 9)).mp h)

theorem imprimitive_member_conductor (θ : DirichletCharacter ℂ 3) (hθ : θ ≠ 1) :
    1 < (θ.changeLevel (by decide : 3 ∣ 9)).conductor :=
  nonprincipal_conductor_gt_one (imprimitive_member θ hθ)

theorem level_one_empty : nonprincipalCharacters 1 = ∅ := level_one_characters
theorem level_one_zero : nonprincipalExpansion 1 11 0 = 0 := level_one_expansion 11 0

/-- Concrete inverse and sign checks against the actual ZMod definitions. -/
theorem actual_inverse_residue :
    reciprocalPhase 3 1 5 = ZMod.stdAddChar (2 : ZMod 3) := by
  unfold reciprocalPhase
  congr 1

theorem positive_phase_differs_from_negative :
    reciprocalPhase 3 1 5 ≠ ZMod.stdAddChar (-(1 : ZMod 3) * (5 : ZMod 3)⁻¹) := by
  intro h
  unfold reciprocalPhase at h
  have hres := ZMod.injective_stdAddChar h
  exact (by decide : (1 : ZMod 3) * (5 : ZMod 3)⁻¹ ≠
    -(1 : ZMod 3) * (5 : ZMod 3)⁻¹) hres

end ZhangLS.Spec.CompositeRamanujanCenterRegression
