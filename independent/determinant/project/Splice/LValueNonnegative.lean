import Splice.HyperbolaAbel

/-!
# Nonnegativity of the actual real L-value

The convolution coefficients are nonnegative. The explicit square-root
summatory error rules out a negative leading coefficient by evaluating at
one sufficiently large positive square. No nonvanishing result is used.
-/

noncomputable section

open Finset

namespace Splice

/-- Nonnegative convolution coefficients and the elementary square-root error
already imply the nonnegativity needed in the prime-mass adapter. -/
theorem LOne_nonneg {D : ℕ} [NeZero D]
    (χ : DirichletCharacter ℂ D) (hne : χ ≠ 1)
    (hreal : ∀ x : ZMod D, (χ x).im = 0) : 0 ≤ LOne χ := by
  by_contra hneg
  have ha : LOne χ < 0 := lt_of_not_ge hneg
  let b : ℝ := -LOne χ
  have hb : 0 < b := neg_pos.mpr ha
  let r : ℝ := 6 / b + 1
  have hr1 : 1 < r := by
    dsimp [r]
    have := div_pos (by norm_num : (0 : ℝ) < 6) hb
    linarith
  have hr : 0 < r := zero_lt_one.trans hr1
  have hD : (0 : ℝ) < D := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne D))
  let x : ℝ := (D : ℝ) * r ^ 2
  have hx : (D : ℝ) ≤ x := by
    dsimp [x]
    nlinarith [mul_nonneg hD.le (show 0 ≤ r ^ 2 - 1 by nlinarith)]
  have hs : 0 ≤ positiveSum (nu χ) x := by
    exact Finset.sum_nonneg fun n hn ↦ nu_nonneg χ hreal n
  have herror := nu_summatory_error_six_sqrt χ hne hx
  have hroot : Real.sqrt ((D : ℝ) * x) = (D : ℝ) * r := by
    rw [show (D : ℝ) * x = ((D : ℝ) * r) ^ 2 by dsimp [x]; ring]
    exact Real.sqrt_sq (mul_nonneg hD.le hr.le)
  rw [hroot] at herror
  have hupper : b * ((D : ℝ) * r ^ 2) ≤ 6 * ((D : ℝ) * r) := by
    have h := (le_abs_self (positiveSum (nu χ) x - LOne χ * x)).trans herror
    dsimp [x, b] at *
    nlinarith
  have hbr : b * r ≤ 6 := by
    apply (mul_le_mul_iff_left₀ (mul_pos hD hr)).mp
    calc
      b * r * ((D : ℝ) * r) = b * ((D : ℝ) * r ^ 2) := by ring
      _ ≤ 6 * ((D : ℝ) * r) := hupper
  have hbr_eq : b * r = 6 + b := by
    dsimp [r]
    field_simp [hb.ne'] <;> ring
  linarith

#print axioms LOne_nonneg

end Splice
