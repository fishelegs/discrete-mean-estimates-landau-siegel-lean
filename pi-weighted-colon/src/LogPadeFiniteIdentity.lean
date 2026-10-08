import LogPadeCoefficientRecurrence
import LogPadeNormalization

noncomputable section

namespace PiWeightedColon

open Polynomial

theorem logPadeP_zero : logPadeP 0 = 1 := by
  norm_num [logPadeP, logPadePCoeff]
theorem logPadeL_zero : logPadeL 0 = 0 := by
  norm_num [logPadeL, logPadeLCoeff, logPadePCoeff]
theorem logPadeP_one : logPadeP 1 = 1 - C (1 / 2) * X := by
  norm_num [logPadeP, logPadePCoeff, Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial]
  ring
theorem logPadeL_one : logPadeL 1 = X := by
  norm_num [logPadeL, logPadeLCoeff, logPadePCoeff, harmonic,
    Finset.sum_range_succ, ← C_mul_X_pow_eq_monomial]
  rw [← C_mul]
  norm_num

theorem logPadeP_step (r : ℕ) : logPadeP (r + 2) =
    (1 - C (1 / 2) * X) * logPadeP (r + 1) -
      C (logPadeBeta r) * X ^ 2 * logPadeP r := by
  ext j
  simp only [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_C_mul]
  cases j with
  | zero => simp [logPadeP_coeff, logPadePCoeff_zero]
  | succ j =>
    cases j with
    | zero =>
      simp [coeff_X_pow_mul', logPadeP_coeff, logPadePCoeff_zero, logPadePCoeff_one]
      ring
    | succ k =>
      simp only [coeff_X_mul, coeff_X_pow_mul, logPadeP_coeff]
      exact logPadePCoeff_recurrence r k

theorem logPadeL_step (r : ℕ) : logPadeL (r + 2) =
    (1 - C (1 / 2) * X) * logPadeL (r + 1) -
      C (logPadeBeta r) * X ^ 2 * logPadeL r := by
  ext j
  simp only [sub_mul, one_mul, mul_assoc, coeff_sub, coeff_C_mul]
  cases j with
  | zero => simp [logPadeL_coeff, logPadeLCoeff_zero]
  | succ j =>
    cases j with
    | zero => simp [coeff_X_pow_mul', logPadeL_coeff, logPadeLCoeff_zero, logPadeLCoeff_one]
    | succ k =>
      simp only [coeff_X_mul, coeff_X_pow_mul, logPadeL_coeff]
      exact logPadeLCoeff_recurrence r k

/-- The recurrence family is the specified finite binomial/harmonic family at every order. -/
theorem logPade_finite_eq_recurrence (r : ℕ) :
    logPadeP r = logPadeRecP r ∧ logPadeL r = logPadeRecL r := by
  induction r using Nat.twoStepInduction with
  | zero => simp [logPadeP_zero, logPadeL_zero, logPadeRecP_zero, logPadeRecL_zero]
  | one => simp [logPadeP_one, logPadeL_one, logPadeRecP_one, logPadeRecL_one]
  | more r ih0 ih1 =>
    rw [logPadeP_step, logPadeL_step, logPadeRecP_step, logPadeRecL_step,
      ih0.1, ih0.2, ih1.1, ih1.2]
    exact ⟨rfl, rfl⟩

/-- Exact adjacent determinant for the explicit finite-sum logarithmic Padé polynomials. -/
theorem logPade_adjacent_determinant (r : ℕ) :
    logPadeP r * logPadeL (r + 1) - logPadeP (r + 1) * logPadeL r =
      C (logPadeD r) * X ^ (2 * r + 1) := by
  rw [(logPade_finite_eq_recurrence r).1, (logPade_finite_eq_recurrence r).2,
    (logPade_finite_eq_recurrence (r + 1)).1, (logPade_finite_eq_recurrence (r + 1)).2]
  exact logPadeRec_adjacent_determinant r

theorem logPade_adjacent_ne_zero (r : ℕ) :
    logPadeP r * logPadeL (r + 1) - logPadeP (r + 1) * logPadeL r ≠ 0 := by
  rw [(logPade_finite_eq_recurrence r).1, (logPade_finite_eq_recurrence r).2,
    (logPade_finite_eq_recurrence (r + 1)).1, (logPade_finite_eq_recurrence (r + 1)).2]
  exact logPadeRec_adjacent_ne_zero r

theorem logPade_normalized_P_rational (r : ℕ) :
    (logPadeP r).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I) / (1 + Complex.I) ^ r =
      (logPadeRationalQ r : ℂ) := by
  rw [(logPade_finite_eq_recurrence r).1]
  exact logPadeRec_normalized_P_rational r

theorem logPade_normalized_L_rational (r : ℕ) :
    (2 * Complex.I * (logPadeL r).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I)) /
      (1 + Complex.I) ^ r = (logPadeRationalP r : ℂ) := by
  rw [(logPade_finite_eq_recurrence r).2]
  exact logPadeRec_normalized_L_rational r

/-- The specified finite-sum pair evaluated and normalized at `1-i`. -/
def logPadeNormalizedQ (r : ℕ) : ℂ :=
  (logPadeP r).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I) / (1 + Complex.I) ^ r

def logPadeNormalizedP (r : ℕ) : ℂ :=
  (2 * Complex.I * (logPadeL r).eval₂ (algebraMap ℚ ℂ) (1 - Complex.I)) /
    (1 + Complex.I) ^ r

theorem logPadeNormalizedQ_eq (r : ℕ) : logPadeNormalizedQ r = (logPadeRationalQ r : ℂ) :=
  logPade_normalized_P_rational r

theorem logPadeNormalizedP_eq (r : ℕ) : logPadeNormalizedP r = (logPadeRationalP r : ℂ) :=
  logPade_normalized_L_rational r

theorem logPadeNormalizedQ_rational (r : ℕ) : ∃ a : ℚ, logPadeNormalizedQ r = (a : ℂ) :=
  ⟨logPadeRationalQ r, logPadeNormalizedQ_eq r⟩

theorem logPadeNormalizedP_rational (r : ℕ) : ∃ a : ℚ, logPadeNormalizedP r = (a : ℂ) :=
  ⟨logPadeRationalP r, logPadeNormalizedP_eq r⟩

theorem logPadeNormalized_adjacent_determinant (r : ℕ) :
    logPadeNormalizedQ r * logPadeNormalizedP (r + 1) -
      logPadeNormalizedQ (r + 1) * logPadeNormalizedP r =
      2 * (-1 : ℂ) ^ r * (logPadeD r : ℂ) := by
  rw [logPadeNormalizedQ_eq, logPadeNormalizedQ_eq,
    logPadeNormalizedP_eq, logPadeNormalizedP_eq]
  exact_mod_cast logPadeRational_adjacent_determinant r

theorem logPadeNormalized_adjacent_ne_zero (r : ℕ) :
    logPadeNormalizedQ r * logPadeNormalizedP (r + 1) -
      logPadeNormalizedQ (r + 1) * logPadeNormalizedP r ≠ 0 := by
  rw [logPadeNormalizedQ_eq, logPadeNormalizedQ_eq,
    logPadeNormalizedP_eq, logPadeNormalizedP_eq]
  exact_mod_cast logPadeRational_adjacent_ne_zero r

theorem logPade_real_adjacent_determinant (r : ℕ) :
    (logPadeRationalQ r : ℝ) * logPadeRationalP (r + 1) -
      (logPadeRationalQ (r + 1) : ℝ) * logPadeRationalP r =
      2 * (-1 : ℝ) ^ r * (logPadeD r : ℝ) := by
  exact_mod_cast logPadeRational_adjacent_determinant r

theorem logPade_real_adjacent_ne_zero (r : ℕ) :
    (logPadeRationalQ r : ℝ) * logPadeRationalP (r + 1) -
      (logPadeRationalQ (r + 1) : ℝ) * logPadeRationalP r ≠ 0 := by
  exact_mod_cast logPadeRational_adjacent_ne_zero r

end PiWeightedColon
