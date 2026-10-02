import ZhangLS.Spec.Lemma58

/-! Expanded original annulus, actual mathlib L-function and derivative,
inner and outer equality endpoints, center of the stronger closed disk. -/

open Complex ZhangLS.Spec
set_option maxHeartbeats 1000000


example : ∃ C : ℝ, 0 < C ∧ ∃ D₀ : ℕ, ∀ {D : ℕ} (χ : RealPrimitiveCharacter D),
    D₀ ≤ D → 1 < D → NormalizedAssumptionA χ → ∀ s : ℂ,
      (Real.pi / Real.log (Real.exp (Real.log (D : ℝ) ^ (9 : ℕ))) ≤ ‖s - 1‖ ∧
        ‖s - 1‖ ≤ 10 * (Real.pi / Real.log (Real.exp (Real.log (D : ℝ) ^ (9 : ℕ))))) →
      ‖(@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) s -
        deriv (@DirichletCharacter.LFunction D ⟨χ.modulus_ne_zero⟩ χ.chi) 1 * (s - 1)‖ ≤
        C * Real.log (D : ℝ) ^ (-15 : ℤ) := lemma58_proved

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) (hA : NormalizedAssumptionA χ)
    {s : ℂ} (hs : ‖s - 1‖ = 10 * lemma44PaperAlpha D) :
    ‖dirichletLFunction χ s - LDerivAtOne χ * (s - 1)‖ ≤
      lemma58ErrorConstant * Real.log (D : ℝ) ^ (-15 : ℤ) :=
  lemma58_actual_full_disk_linear_error χ hD hL hA hs.le

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) (hA : NormalizedAssumptionA χ)
    {s : ℂ} (hs : ‖s - 1‖ = lemma44PaperAlpha D) :
    ‖dirichletLFunction χ s - LDerivAtOne χ * (s - 1)‖ ≤
      lemma58ErrorConstant * Real.log (D : ℝ) ^ (-15 : ℤ) := by
  apply lemma58_actual_full_disk_linear_error χ hD hL hA
  rw [hs]
  have hp := (lemma44_alpha_pos_le_one (D := D) (by change 3 ≤ Real.log (D : ℝ); linarith)).1
  linarith

example {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hL : 2000 ≤ Real.log (D : ℝ)) (hA : NormalizedAssumptionA χ) :
    ‖dirichletLFunction χ 1 - LDerivAtOne χ * ((1 : ℂ) - 1)‖ ≤
      lemma58ErrorConstant * Real.log (D : ℝ) ^ (-15 : ℤ) := by
  apply lemma58_actual_full_disk_linear_error χ hD hL hA
  simp only [sub_self, norm_zero]
  have hp := (lemma44_alpha_pos_le_one (D := D) (by change 3 ≤ Real.log (D : ℝ); linarith)).1
  positivity

#print axioms lemma58_error_constant_pos
#print axioms lemma58_alpha_eq_log_power
#print axioms lemma58_original_radius_in_taylor_disk
#print axioms lemma58_actual_value_at_one_small
#print axioms lemma58_actual_full_disk_linear_error
#print axioms lemma58_at_explicit_constant
#print axioms lemma58_proved
