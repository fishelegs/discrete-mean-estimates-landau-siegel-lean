import ZhangLS.Spec.DivisorSmallPowerBudget

/-! A fixed symbolic sixteenth-power budget for the actual τ₅. -/
set_option autoImplicit false
namespace ZhangLS.Spec.DivisorHyperbolicBudget

/-- Kept symbolic: no expansion of the published quarter-power constant. -/
noncomputable def smallPowerConstant : ℝ :=
  (divisorPowerQuarterConstant 625) ^ (1 / 4 : ℝ)

theorem smallPowerConstant_pos : 0 < smallPowerConstant :=
  Real.rpow_pos_of_pos (divisorPower_quarter_constant_pos 625) _

/-- τ₅⁴ ≤ τ₆₂₅ followed by the published τ₆₂₅ quarter-power budget. -/
theorem tau_five_sixteenth (r : ℕ) (hr : 1 ≤ r) :
    (lemma34Tau 5 r : ℝ) ≤ smallPowerConstant * (r : ℝ) ^ (1 / 16 : ℝ) := by
  have hfour : (lemma34Tau 5 r : ℝ) ^ 4 ≤ (lemma34Tau 625 r : ℝ) := by
    exact_mod_cast divisorPower_tau_fourth (by norm_num : 1 ≤ 5) r
  have hquarter := divisorPower_tau_quarter (by norm_num : 1 ≤ 625) r
  have hrR : 0 < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hr0 : 0 ≤ (r : ℝ) := hrR.le
  have hroot := Real.rpow_le_rpow
    (pow_nonneg (Nat.cast_nonneg (lemma34Tau 5 r)) 4) (hfour.trans hquarter)
    (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [Real.mul_rpow (divisorPower_quarter_constant_pos 625).le
      (Real.rpow_nonneg hr0 _),
    ← Real.rpow_natCast (lemma34Tau 5 r : ℝ) 4,
    ← Real.rpow_mul (Nat.cast_nonneg (lemma34Tau 5 r)),
    ← Real.rpow_mul hr0] at hroot
  have hleft : ((4 : ℕ) : ℝ) * (1 / 4 : ℝ) = 1 := by norm_num
  have hright : (1 / 4 : ℝ) * (1 / 4 : ℝ) = 1 / 16 := by norm_num
  simpa only [hleft, hright, Real.rpow_one, smallPowerConstant] using hroot

end ZhangLS.Spec.DivisorHyperbolicBudget
