import LogPadeFiniteIdentity

noncomputable section

namespace PiWeightedColon.Regression

open Polynomial

theorem log_pade_finite_identity_exact_type : ∀ r : ℕ,
    logPadeP r * logPadeL (r + 1) - logPadeP (r + 1) * logPadeL r =
      C ((r.factorial : ℚ) ^ 4 / ((2 * r).factorial * (2 * r + 1).factorial)) *
        X ^ (2 * r + 1) := logPade_adjacent_determinant

theorem log_pade_finite_identification_all_orders : ∀ r : ℕ,
    logPadeP r = logPadeRecP r ∧ logPadeL r = logPadeRecL r :=
  logPade_finite_eq_recurrence

theorem log_pade_factorial_constant_positive : ∀ r : ℕ,
    (0 : ℚ) < (r.factorial : ℚ) ^ 4 / ((2 * r).factorial * (2 * r + 1).factorial) :=
  logPadeD_pos

theorem log_pade_first_polynomials :
    logPadeP 0 = 1 ∧ logPadeL 0 = 0 ∧
      logPadeP 1 = 1 - C (1 / 2) * X ∧ logPadeL 1 = X :=
  ⟨logPadeP_zero, logPadeL_zero, logPadeP_one, logPadeL_one⟩

theorem log_pade_second_polynomials :
    logPadeP 2 = 1 - X + C (1 / 6) * X ^ 2 ∧
      logPadeL 2 = X - C (1 / 2) * X ^ 2 := by
  rw [show 2 = 0 + 2 by rfl, logPadeP_step, logPadeL_step]
  rw [logPadeP_zero, logPadeL_zero, logPadeP_one, logPadeL_one]
  norm_num [logPadeBeta]
  have hhalf : (C (1 / 2) : Polynomial ℚ) * 2 = 1 := by
    calc
      _ = C (1 / 2) * C (2 : ℚ) := by rw [map_ofNat]
      _ = 1 := by rw [← C_mul]; norm_num
  have heq : (C (1 / 2) : Polynomial ℚ) ^ 2 - C (1 / 12) = C (1 / 6) := by
    rw [← C_pow, ← C_sub]
    norm_num
  constructor
  · calc
      _ = (1 : Polynomial ℚ) - (C (1 / 2) * 2) * X +
          (C (1 / 2) ^ 2 - C (1 / 12)) * X ^ 2 := by ring
      _ = _ := by rw [hhalf, heq]; ring
  · ring

theorem log_pade_first_rational_pairs :
    logPadeRationalPair 0 = (1, 0) ∧ logPadeRationalPair 1 = (1 / 2, 2) ∧
      logPadeRationalPair 2 = (1 / 3, 1) ∧ logPadeRationalPair 3 = (1 / 5, 19 / 30) := by
  norm_num [logPadeRationalPair, logPadeBeta]

theorem log_pade_first_normalized_determinant :
    logPadeRationalQ 0 * logPadeRationalP 1 -
      logPadeRationalQ 1 * logPadeRationalP 0 = 2 := by
  norm_num [logPadeRationalQ_zero, logPadeRationalP_zero, logPadeRationalQ_one,
    logPadeRationalP_one]

theorem log_pade_second_normalized_determinant :
    logPadeRationalQ 1 * logPadeRationalP 2 -
      logPadeRationalQ 2 * logPadeRationalP 1 = -(1 / 6) := by
  norm_num [logPadeRationalQ, logPadeRationalP, logPadeRationalPair, logPadeBeta]

theorem log_pade_normalized_rational_all_orders : ∀ r : ℕ,
    (∃ a : ℚ, logPadeNormalizedQ r = (a : ℂ)) ∧
      (∃ b : ℚ, logPadeNormalizedP r = (b : ℂ)) := by
  intro r
  exact ⟨logPadeNormalizedQ_rational r, logPadeNormalizedP_rational r⟩

theorem log_pade_normalized_identity_all_orders : ∀ r : ℕ,
    logPadeNormalizedQ r * logPadeNormalizedP (r + 1) -
      logPadeNormalizedQ (r + 1) * logPadeNormalizedP r =
      2 * (-1 : ℂ) ^ r * (logPadeD r : ℂ) := logPadeNormalized_adjacent_determinant

theorem log_pade_normalized_independence_all_orders : ∀ r : ℕ,
    logPadeNormalizedQ r * logPadeNormalizedP (r + 1) -
      logPadeNormalizedQ (r + 1) * logPadeNormalizedP r ≠ 0 :=
  logPadeNormalized_adjacent_ne_zero

theorem log_pade_real_identity_all_orders : ∀ r : ℕ,
    (logPadeRationalQ r : ℝ) * logPadeRationalP (r + 1) -
      (logPadeRationalQ (r + 1) : ℝ) * logPadeRationalP r =
      2 * (-1 : ℝ) ^ r * (logPadeD r : ℝ) := logPade_real_adjacent_determinant

end PiWeightedColon.Regression
