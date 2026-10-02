import ZhangLS.Spec.Lemma55

/-! Actual analytic objects, closed local boundaries, and the unchanged
full-height original Lemma 5.5 target. No proof of the full target is asserted. -/

open Complex ZhangLS.Spec

set_option maxRecDepth 4096
set_option maxHeartbeats 600000

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (x : ℝ) :
    ((@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) (x : ℂ)).im = 0 :=
  dirichletLFunction_im_eq_zero_real χ hD x

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) {s : ℂ}
    (hσ : 1 - 1 / Real.log (D : ℝ) ≤ s.re) (hnorm : ‖s‖ ≤ 2) :
    ‖(@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) s‖ ≤ 4 * Real.exp 1 * Real.log (D : ℝ) :=
  lemma55_actual_L_near_one_bound χ hD hL hσ hnorm

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) {s : ℂ}
    (hs : ‖s - 1‖ ≤ 1 / (4 * Real.log (D : ℝ))) :
    ‖deriv (deriv ((@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi))) s‖ ≤
      128 * Real.exp 1 * Real.log (D : ℝ) ^ 3 :=
  lemma55_actual_second_derivative_bound χ hD hL hs

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2 ≤ Real.log (D : ℝ)) {s : ℂ}
    (hs : ‖s - 1‖ ≤ 1 / (4 * Real.log (D : ℝ))) :
    ‖(@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) s - (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) 1 -
        deriv ((@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi)) 1 * (s - 1)‖ ≤
      (128 * Real.exp 1 * Real.log (D : ℝ) ^ 3) * ‖s - 1‖ ^ 2 :=
  lemma55_actual_taylor_remainder_bound χ hD hL hs

example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : (3 : ℕ) ^ 10000000 ≤ D) (hA : NormalizedAssumptionA χ) :
    ∃ ρ : ℝ, 0 < 1 - ρ ∧
      1 - ρ ≤ 64 * Real.log (D : ℝ) ^ (-2022 : ℤ) ∧
      (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) (ρ : ℂ) = 0 ∧
      deriv ((@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi)) (ρ : ℂ) ≠ 0 ∧
      ∀ s : ℂ, ‖s - 1‖ ≤ 64 * Real.log (D : ℝ) ^ (-2022 : ℤ) →
        (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) s = 0 → s = (ρ : ℂ) :=
  lemma55_actual_simple_real_zero_locally_unique χ hDN hA

-- The actual center derivative is also covered by the closed disk estimate.
example {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hDN : lemma57ExplicitModulusThreshold ≤ D) (hA : NormalizedAssumptionA χ) :
    (1 : ℝ) / 32 ≤ deriv (realLValue χ) 1 := by
  apply lemma55_actual_real_derivative_lower_bound χ hDN hA
  simpa using (lemma55_local_zero_budget hDN).1.le

-- The original height is 2D, and the left boundary is 1-2/log D.
example (D : ℕ) (s : ℂ) : Lemma55InZeroRegion D s ↔
    1 - 2 / Real.log (D : ℝ) < s.re ∧ |s.im| < 2 * (D : ℝ) := Iff.rfl

-- This checks the faithful full target definition, not its proof.
example : Lemma55Target =
    (∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
      D₀ ≤ D → 1 < D → NormalizedAssumptionA χ →
        ∃ ρ : ℝ, 0 < 1 - ρ ∧
          1 - ρ ≤ C * Real.log (D : ℝ) ^ (-2022 : ℤ) ∧
          (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) (ρ : ℂ) = 0 ∧
          deriv ((@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi)) (ρ : ℂ) ≠ 0 ∧
          ∀ s : ℂ, (1 - 2 / Real.log (D : ℝ) < s.re ∧ |s.im| < 2 * (D : ℝ)) →
            (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) s = 0 → s = (ρ : ℂ)) := rfl

#print axioms RealPrimitiveCharacter.norm_sum_Icc_evalNat_le_length
#print axioms lemma55_rpow_near_one_le_exp
#print axioms RealPrimitiveCharacter.norm_characterAbelIntegral_le_near_one
#print axioms lemma55_actual_L_near_one_bound
#print axioms lemma55_actual_second_derivative_bound
#print axioms lemma55_actual_first_derivative_variation
#print axioms lemma55_actual_taylor_remainder_bound
#print axioms RealPrimitiveCharacter.inverse_eq_self
#print axioms dirichletLFunction_im_eq_zero_real
#print axioms dirichletLFunction_real_eq_realLValue
#print axioms realLValue_hasDerivAt
#print axioms realLValue_deriv_eq_re
#print axioms real_axis_value_theorem_proved
#print axioms real_axis_analytic_compatibility_proved
#print axioms lemma55_local_zero_budget
#print axioms lemma55_actual_real_derivative_lower_bound
#print axioms lemma55_actual_simple_real_zero
#print axioms lemma55_actual_local_zero_unique
#print axioms lemma55_actual_simple_real_zero_locally_unique
