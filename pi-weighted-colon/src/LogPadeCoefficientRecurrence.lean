import LogPadeCoefficients

noncomputable section

namespace PiWeightedColon

open Polynomial

theorem logPadePCoeff_factorial (r j : ℕ) (hj : j ≤ r) :
    logPadePCoeff r j = (-1 : ℚ) ^ j *
      (r.factorial : ℚ) ^ 2 * (2 * r - j).factorial /
      ((r - j).factorial ^ 2 * (2 * r).factorial * j.factorial) := by
  unfold logPadePCoeff
  rw [Nat.cast_choose ℚ hj, Nat.cast_choose ℚ (by omega : r ≤ 2 * r - j),
    Nat.cast_choose ℚ (by omega : r ≤ 2 * r)]
  rw [show 2 * r - j - r = r - j by omega, show 2 * r - r = r by omega]
  have h0 : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have h1 : (j.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have h2 : ((r - j).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (r - j)
  have h3 : ((2 * r).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * r)
  field_simp

theorem logPadePCoeff_recurrence_interior (k m : ℕ) :
    logPadePCoeff (k + m + 1 + 2) (k + 2) =
      logPadePCoeff (k + m + 1 + 1) (k + 2) -
      (1 / 2) * logPadePCoeff (k + m + 1 + 1) (k + 1) -
      logPadeBeta (k + m + 1) * logPadePCoeff (k + m + 1) k := by
  rw [logPadePCoeff_factorial _ _ (by omega), logPadePCoeff_factorial _ _ (by omega),
    logPadePCoeff_factorial _ _ (by omega), logPadePCoeff_factorial _ _ (by omega)]
  rw [show 2 * (k + m + 1 + 2) - (k + 2) = k + 2 * m + 2 + 1 + 1 by omega,
    show 2 * (k + m + 1 + 1) - (k + 2) = k + 2 * m + 2 by omega,
    show 2 * (k + m + 1 + 1) - (k + 1) = k + 2 * m + 2 + 1 by omega,
    show 2 * (k + m + 1) - k = k + 2 * m + 2 by omega,
    show k + m + 1 + 2 - (k + 2) = m + 1 by omega,
    show k + m + 1 + 1 - (k + 2) = m by omega,
    show k + m + 1 + 1 - (k + 1) = m + 1 by omega,
    show k + m + 1 - k = m + 1 by omega,
    show 2 * (k + m + 1 + 2) = 2 * (k + m + 1) + 1 + 1 + 1 + 1 by omega,
    show 2 * (k + m + 1 + 1) = 2 * (k + m + 1) + 1 + 1 by omega]
  unfold logPadeBeta
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have h0 : ((k + m + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + m + 1)
  have h1 : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h3 : ((2 * (k + m + 1)).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * (k + m + 1))
  field_simp
  ring

theorem logPadeLCoeff_recurrence_interior (k m : ℕ) :
    logPadeLCoeff (k + m + 1 + 2) (k + 2) =
      logPadeLCoeff (k + m + 1 + 1) (k + 2) -
      (1 / 2) * logPadeLCoeff (k + m + 1 + 1) (k + 1) -
      logPadeBeta (k + m + 1) * logPadeLCoeff (k + m + 1) k := by
  unfold logPadeLCoeff
  rw [show k + m + 1 + 2 - (k + 2) = m + 1 by omega,
    show k + m + 1 + 1 - (k + 2) = m by omega,
    show k + m + 1 + 1 - (k + 1) = m + 1 by omega,
    show k + m + 1 - k = m + 1 by omega]
  simp only [harmonic_succ]
  rw [logPadePCoeff_factorial _ _ (by omega), logPadePCoeff_factorial _ _ (by omega),
    logPadePCoeff_factorial _ _ (by omega), logPadePCoeff_factorial _ _ (by omega)]
  rw [show 2 * (k + m + 1 + 2) - (k + 2) = k + 2 * m + 2 + 1 + 1 by omega,
    show 2 * (k + m + 1 + 1) - (k + 2) = k + 2 * m + 2 by omega,
    show 2 * (k + m + 1 + 1) - (k + 1) = k + 2 * m + 2 + 1 by omega,
    show 2 * (k + m + 1) - k = k + 2 * m + 2 by omega,
    show k + m + 1 + 2 - (k + 2) = m + 1 by omega,
    show k + m + 1 + 1 - (k + 2) = m by omega,
    show k + m + 1 + 1 - (k + 1) = m + 1 by omega,
    show k + m + 1 - k = m + 1 by omega,
    show 2 * (k + m + 1 + 2) = 2 * (k + m + 1) + 1 + 1 + 1 + 1 by omega,
    show 2 * (k + m + 1 + 1) = 2 * (k + m + 1) + 1 + 1 by omega]
  unfold logPadeBeta
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have h0 : ((k + m + 1).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (k + m + 1)
  have h1 : (m.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
  have h2 : (k.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
  have h3 : ((2 * (k + m + 1)).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * (k + m + 1))
  field_simp
  ring

theorem logPadePCoeff_top (r : ℕ) : logPadePCoeff r r =
    (-1 : ℚ) ^ r * (r.factorial : ℚ) ^ 2 / (2 * r).factorial := by
  rw [logPadePCoeff_factorial r r (le_refl _)]
  simp only [Nat.sub_self, Nat.factorial_zero, Nat.cast_one,
    show 2 * r - r = r by omega]
  have hr : (r.factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero r
  have h2 : ((2 * r).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * r)
  field_simp

theorem logPadePCoeff_recurrence_top (r : ℕ) :
    logPadePCoeff (r + 2) (r + 2) =
      -(1 / 2) * logPadePCoeff (r + 1) (r + 1) - logPadeBeta r * logPadePCoeff r r := by
  rw [logPadePCoeff_top, logPadePCoeff_top, logPadePCoeff_top]
  unfold logPadeBeta
  rw [show 2 * (r + 2) = 2 * r + 1 + 1 + 1 + 1 by omega,
    show 2 * (r + 1) = 2 * r + 1 + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  have hf : ((2 * r).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * r)
  field_simp
  ring

theorem logPadeLCoeff_recurrence_top (r : ℕ) :
    logPadeLCoeff (r + 2) (r + 2) =
      -(1 / 2) * logPadeLCoeff (r + 1) (r + 1) - logPadeBeta r * logPadeLCoeff r r := by
  unfold logPadeLCoeff
  simp only [Nat.sub_self, harmonic_zero, sub_zero]
  rw [logPadePCoeff_top, logPadePCoeff_top, logPadePCoeff_top]
  unfold logPadeBeta
  rw [show 2 * (r + 2) = 2 * r + 1 + 1 + 1 + 1 by omega,
    show 2 * (r + 1) = 2 * r + 1 + 1 by omega]
  simp only [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ, harmonic_succ]
  push_cast
  have hf : ((2 * r).factorial : ℚ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (2 * r)
  field_simp
  ring

theorem logPadePCoeff_recurrence (r k : ℕ) :
    logPadePCoeff (r + 2) (k + 2) = logPadePCoeff (r + 1) (k + 2) -
      (1 / 2) * logPadePCoeff (r + 1) (k + 1) - logPadeBeta r * logPadePCoeff r k := by
  by_cases h : k < r
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show k + 1 ≤ r by omega)
    have hr : r = k + m + 1 := by omega
    rw [hr]
    exact logPadePCoeff_recurrence_interior k m
  · by_cases he : k = r
    · subst k
      rw [logPadePCoeff_above (r + 1) (r + 2) (by omega), zero_sub]
      simpa only [neg_mul] using logPadePCoeff_recurrence_top r
    · rw [logPadePCoeff_above (r + 2) (k + 2) (by omega),
        logPadePCoeff_above (r + 1) (k + 2) (by omega),
        logPadePCoeff_above (r + 1) (k + 1) (by omega),
        logPadePCoeff_above r k (by omega)]
      ring

theorem logPadeLCoeff_recurrence (r k : ℕ) :
    logPadeLCoeff (r + 2) (k + 2) = logPadeLCoeff (r + 1) (k + 2) -
      (1 / 2) * logPadeLCoeff (r + 1) (k + 1) - logPadeBeta r * logPadeLCoeff r k := by
  by_cases h : k < r
  · obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le (show k + 1 ≤ r by omega)
    have hr : r = k + m + 1 := by omega
    rw [hr]
    exact logPadeLCoeff_recurrence_interior k m
  · by_cases he : k = r
    · subst k
      rw [logPadeLCoeff_above (r + 1) (r + 2) (by omega), zero_sub]
      simpa only [neg_mul] using logPadeLCoeff_recurrence_top r
    · rw [logPadeLCoeff_above (r + 2) (k + 2) (by omega),
        logPadeLCoeff_above (r + 1) (k + 2) (by omega),
        logPadeLCoeff_above (r + 1) (k + 1) (by omega),
        logPadeLCoeff_above r k (by omega)]
      ring

end PiWeightedColon
