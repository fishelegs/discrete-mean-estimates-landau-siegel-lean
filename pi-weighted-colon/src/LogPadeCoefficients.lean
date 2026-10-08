import LogPadeRecurrence
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.NumberTheory.Harmonic.Defs

noncomputable section

namespace PiWeightedColon

open Polynomial Finset

/-- The explicit normalized logarithmic Padé denominator coefficient. -/
def logPadePCoeff (r j : ℕ) : ℚ :=
  (-1 : ℚ) ^ j * r.choose j * (2 * r - j).choose r / (2 * r).choose r

/-- The explicit numerator coefficient, using finite harmonic numbers. -/
def logPadeLCoeff (r j : ℕ) : ℚ :=
  -2 * logPadePCoeff r j * (harmonic r - harmonic (r - j))

def logPadeP (r : ℕ) : Polynomial ℚ :=
  ∑ j ∈ range (r + 1), monomial j (logPadePCoeff r j)

def logPadeL (r : ℕ) : Polynomial ℚ :=
  ∑ j ∈ range (r + 1), monomial j (logPadeLCoeff r j)

theorem logPadePCoeff_above (r j : ℕ) (h : r < j) : logPadePCoeff r j = 0 := by
  simp [logPadePCoeff, Nat.choose_eq_zero_of_lt h]

theorem logPadeLCoeff_above (r j : ℕ) (h : r < j) : logPadeLCoeff r j = 0 := by
  simp [logPadeLCoeff, logPadePCoeff_above r j h]

theorem logPadeP_coeff (r j : ℕ) : (logPadeP r).coeff j = logPadePCoeff r j := by
  unfold logPadeP
  simp only [finsetSum_coeff, coeff_monomial]
  by_cases h : j < r + 1
  · simp [h]
  · simp [h, logPadePCoeff_above r j (by omega)]

theorem logPadeL_coeff (r j : ℕ) : (logPadeL r).coeff j = logPadeLCoeff r j := by
  unfold logPadeL
  simp only [finsetSum_coeff, coeff_monomial]
  by_cases h : j < r + 1
  · simp [h]
  · simp [h, logPadeLCoeff_above r j (by omega)]

theorem logPadePCoeff_zero (r : ℕ) : logPadePCoeff r 0 = 1 := by
  have h : ((2 * r).choose r : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega : r ≤ 2 * r)).ne'
  simp [logPadePCoeff, h]

theorem logPadeLCoeff_zero (r : ℕ) : logPadeLCoeff r 0 = 0 := by
  simp [logPadeLCoeff]

theorem logPadePCoeff_one (r : ℕ) : logPadePCoeff (r + 1) 1 = -(r + 1 : ℚ) / 2 := by
  unfold logPadePCoeff
  rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega,
    show 2 * (r + 1) = (2 * r + 1) + 1 by omega]
  simp only [pow_one, Nat.choose_one_right, Nat.cast_add, Nat.cast_one]
  rw [Nat.cast_choose ℚ (by omega : r + 1 ≤ 2 * r + 1),
    Nat.cast_choose ℚ (by omega : r + 1 ≤ 2 * r + 1 + 1)]
  rw [show 2 * r + 1 - (r + 1) = r by omega,
    show 2 * r + 1 + 1 - (r + 1) = r + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have hf : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have hg : ((2 * r).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * r)
  field_simp
  ring

theorem logPadeLCoeff_one (r : ℕ) : logPadeLCoeff (r + 1) 1 = 1 := by
  unfold logPadeLCoeff
  rw [logPadePCoeff_one, Nat.add_sub_cancel, harmonic_succ]
  have hn : (r + 1 : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

end PiWeightedColon
