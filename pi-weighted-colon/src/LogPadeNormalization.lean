import LogPadeRecurrence
import Mathlib.Data.Complex.Basic

noncomputable section

namespace PiWeightedColon

open Polynomial

/-- Rational recurrence for the normalized pair, ordered `(q,p)`. -/
def logPadeRationalPair : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | 1 => (1 / 2, 2)
  | r + 2 =>
    let v := logPadeRationalPair (r + 1)
    let u := logPadeRationalPair r
    ((1 / 2) * v.1 + logPadeBeta r * u.1,
      (1 / 2) * v.2 + logPadeBeta r * u.2)

def logPadeRationalQ (r : ℕ) : ℚ := (logPadeRationalPair r).1
def logPadeRationalP (r : ℕ) : ℚ := (logPadeRationalPair r).2

theorem logPadeRationalQ_zero : logPadeRationalQ 0 = 1 := rfl
theorem logPadeRationalP_zero : logPadeRationalP 0 = 0 := rfl
theorem logPadeRationalQ_one : logPadeRationalQ 1 = 1 / 2 := rfl
theorem logPadeRationalP_one : logPadeRationalP 1 = 2 := rfl
theorem logPadeRationalQ_step (r : ℕ) : logPadeRationalQ (r + 2) =
    (1 / 2) * logPadeRationalQ (r + 1) + logPadeBeta r * logPadeRationalQ r := rfl
theorem logPadeRationalP_step (r : ℕ) : logPadeRationalP (r + 2) =
    (1 / 2) * logPadeRationalP (r + 1) + logPadeBeta r * logPadeRationalP r := rfl

theorem logPadeRational_adjacent_determinant (r : ℕ) :
    logPadeRationalQ r * logPadeRationalP (r + 1) -
      logPadeRationalQ (r + 1) * logPadeRationalP r = 2 * (-1 : ℚ) ^ r * logPadeD r := by
  induction r with
  | zero => norm_num [logPadeRationalQ_zero, logPadeRationalP_zero, logPadeRationalP_one, logPadeD_zero]
  | succ r ih =>
    rw [show r + 1 + 1 = r + 2 by omega, logPadeRationalQ_step, logPadeRationalP_step]
    calc
      _ = -logPadeBeta r * (logPadeRationalQ r * logPadeRationalP (r + 1) -
          logPadeRationalQ (r + 1) * logPadeRationalP r) := by ring
      _ = -logPadeBeta r * (2 * (-1 : ℚ) ^ r * logPadeD r) := by rw [ih]
      _ = 2 * (-1 : ℚ) ^ (r + 1) * logPadeD (r + 1) := by
        rw [pow_succ, logPadeD_step]
        ring

theorem logPadeRational_adjacent_ne_zero (r : ℕ) :
    logPadeRationalQ r * logPadeRationalP (r + 1) -
      logPadeRationalQ (r + 1) * logPadeRationalP r ≠ 0 := by
  rw [logPadeRational_adjacent_determinant]
  exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ (by norm_num)))
    (ne_of_gt (logPadeD_pos r))

theorem logPade_normalization_base_ne_zero : (1 + Complex.I : ℂ) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  norm_num at hi

theorem logPade_complex_step_constants :
    (1 - (1 / 2 : ℂ) * (1 - Complex.I)) = (1 + Complex.I) / 2 ∧
    (1 - Complex.I) ^ 2 = -(1 + Complex.I) ^ 2 := by
  constructor
  · ring
  · ring_nf
    rw [Complex.I_sq]
    ring

theorem logPadeRec_eval_P (r : ℕ) :
    (logPadeRecP r).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I) =
      (1 + Complex.I) ^ r * (logPadeRationalQ r : ℂ) := by
  induction r using Nat.twoStepInduction with
  | zero => simp [logPadeRecP_zero, logPadeRationalQ_zero]
  | one => norm_num [logPadeRecP_one, logPadeRationalQ_one, Complex.ext_iff]
  | more r ih0 ih1 =>
    rw [logPadeRecP_step, eval₂_sub, eval₂_mul, eval₂_sub, eval₂_one,
      eval₂_mul, eval₂_C, eval₂_X, eval₂_mul, eval₂_mul, eval₂_C, eval₂_pow,
      eval₂_X, ih0, ih1, logPadeRationalQ_step]
    simp only [eq_ratCast]
    push_cast
    rw [logPade_complex_step_constants.1, logPade_complex_step_constants.2,
      pow_succ, pow_succ]
    ring

theorem logPadeRec_eval_L (r : ℕ) :
    2 * Complex.I * (logPadeRecL r).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I) =
      (1 + Complex.I) ^ r * (logPadeRationalP r : ℂ) := by
  induction r using Nat.twoStepInduction with
  | zero => simp [logPadeRecL_zero, logPadeRationalP_zero]
  | one => norm_num [logPadeRecL_one, logPadeRationalP_one, Complex.ext_iff]
  | more r ih0 ih1 =>
    rw [logPadeRecL_step, eval₂_sub, eval₂_mul, eval₂_sub, eval₂_one,
      eval₂_mul, eval₂_C, eval₂_X, eval₂_mul, eval₂_mul, eval₂_C, eval₂_pow, eval₂_X]
    rw [logPadeRationalP_step]
    simp only [eq_ratCast]
    push_cast
    rw [logPade_complex_step_constants.1, logPade_complex_step_constants.2]
    calc
      _ = ((1 + Complex.I) / 2) * (2 * Complex.I *
          (logPadeRecL (r + 1)).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I)) +
          (logPadeBeta r : ℂ) * (1 + Complex.I) ^ 2 * (2 * Complex.I *
          (logPadeRecL r).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I)) := by ring
      _ = _ := by rw [ih0, ih1, pow_succ, pow_succ]; ring

theorem logPadeRec_normalized_P_rational (r : ℕ) :
    (logPadeRecP r).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I) / (1 + Complex.I) ^ r =
      (logPadeRationalQ r : ℂ) := by
  rw [logPadeRec_eval_P]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ logPade_normalization_base_ne_zero)

theorem logPadeRec_normalized_L_rational (r : ℕ) :
    (2 * Complex.I * (logPadeRecL r).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I)) /
      (1 + Complex.I) ^ r = (logPadeRationalP r : ℂ) := by
  rw [logPadeRec_eval_L]
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ logPade_normalization_base_ne_zero)

end PiWeightedColon
