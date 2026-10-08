import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic

noncomputable section

namespace PiWeightedColon

open Polynomial

/-- The three-term recurrence coefficient, indexed for the step `r → r+2`. -/
def logPadeBeta (r : ℕ) : ℚ :=
  (r + 1 : ℚ) ^ 2 / (4 * (2 * r + 1) * (2 * r + 3))

/-- The factorial constant appearing in the adjacent determinant. -/
def logPadeD (r : ℕ) : ℚ :=
  (r.factorial : ℚ) ^ 4 / ((2 * r).factorial * (2 * r + 1).factorial)

/-- Recurrence presentation, identified with the finite sums in `LogPadeFiniteIdentity`. -/
def logPadeRecPair : ℕ → Polynomial ℚ × Polynomial ℚ
  | 0 => (1, 0)
  | 1 => (1 - C (1 / 2) * X, X)
  | r + 2 =>
    let v := logPadeRecPair (r + 1)
    let u := logPadeRecPair r
    ((1 - C (1 / 2) * X) * v.1 - C (logPadeBeta r) * X ^ 2 * u.1,
      (1 - C (1 / 2) * X) * v.2 - C (logPadeBeta r) * X ^ 2 * u.2)

def logPadeRecP (r : ℕ) : Polynomial ℚ := (logPadeRecPair r).1
def logPadeRecL (r : ℕ) : Polynomial ℚ := (logPadeRecPair r).2

theorem logPadeRecP_zero : logPadeRecP 0 = 1 := rfl
theorem logPadeRecL_zero : logPadeRecL 0 = 0 := rfl
theorem logPadeRecP_one : logPadeRecP 1 = 1 - C (1 / 2) * X := rfl
theorem logPadeRecL_one : logPadeRecL 1 = X := rfl
theorem logPadeRecP_step (r : ℕ) : logPadeRecP (r + 2) =
    (1 - C (1 / 2) * X) * logPadeRecP (r + 1) -
      C (logPadeBeta r) * X ^ 2 * logPadeRecP r := rfl
theorem logPadeRecL_step (r : ℕ) : logPadeRecL (r + 2) =
    (1 - C (1 / 2) * X) * logPadeRecL (r + 1) -
      C (logPadeBeta r) * X ^ 2 * logPadeRecL r := rfl

theorem logPadeBeta_pos (r : ℕ) : 0 < logPadeBeta r := by
  unfold logPadeBeta
  positivity

theorem logPadeD_pos (r : ℕ) : 0 < logPadeD r := by
  have h0 : (0 : ℚ) < r.factorial := by exact_mod_cast Nat.factorial_pos r
  have h1 : (0 : ℚ) < (2 * r).factorial := by exact_mod_cast Nat.factorial_pos (2 * r)
  have h2 : (0 : ℚ) < (2 * r + 1).factorial := by exact_mod_cast Nat.factorial_pos (2 * r + 1)
  exact div_pos (pow_pos h0 _) (mul_pos h1 h2)

theorem logPadeD_zero : logPadeD 0 = 1 := by norm_num [logPadeD]

theorem logPadeD_step (r : ℕ) : logPadeD (r + 1) = logPadeBeta r * logPadeD r := by
  have h0 : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have h1 : ((2 * r).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * r)
  have h2 : ((2 * r + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * r + 1)
  unfold logPadeD logPadeBeta
  rw [show 2 * (r + 1) = (2 * r + 1) + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- Exact adjacent determinant for every index, in the recurrence presentation. -/
theorem logPadeRec_adjacent_determinant (r : ℕ) :
    logPadeRecP r * logPadeRecL (r + 1) - logPadeRecP (r + 1) * logPadeRecL r =
      C (logPadeD r) * X ^ (2 * r + 1) := by
  induction r with
  | zero => simp [logPadeRecP_zero, logPadeRecL_zero, logPadeRecL_one, logPadeD_zero]
  | succ r ih =>
    rw [show r + 1 + 1 = r + 2 by omega, logPadeRecP_step, logPadeRecL_step]
    calc
      _ = C (logPadeBeta r) * X ^ 2 *
          (logPadeRecP r * logPadeRecL (r + 1) - logPadeRecP (r + 1) * logPadeRecL r) := by ring
      _ = C (logPadeBeta r) * X ^ 2 * (C (logPadeD r) * X ^ (2 * r + 1)) := by rw [ih]
      _ = C (logPadeD (r + 1)) * X ^ (2 * (r + 1) + 1) := by
        rw [logPadeD_step, C_mul, show 2 * (r + 1) + 1 = 2 + (2 * r + 1) by omega, pow_add]
        ring

theorem logPadeRec_adjacent_ne_zero (r : ℕ) :
    logPadeRecP r * logPadeRecL (r + 1) - logPadeRecP (r + 1) * logPadeRecL r ≠ 0 := by
  rw [logPadeRec_adjacent_determinant]
  exact mul_ne_zero (C_ne_zero.mpr (ne_of_gt (logPadeD_pos r)))
    (pow_ne_zero _ X_ne_zero)

end PiWeightedColon
