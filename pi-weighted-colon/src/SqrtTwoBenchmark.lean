import ApproximationPairs

noncomputable section

namespace PiWeightedColon

theorem sqrt_two_bounds : (1 : ℝ) ≤ Real.sqrt 2 ∧ Real.sqrt 2 ≤ 3 / 2 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg (2 : ℝ)
  constructor <;> nlinarith

theorem sqrt_two_integer_norm_ne_zero (p q : ℤ) (hq : 0 < q) :
    p ^ 2 - 2 * q ^ 2 ≠ 0 := by
  intro hz
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hq)
  have hpq : (p : ℝ) ^ 2 = 2 * (q : ℝ) ^ 2 := by
    exact_mod_cast (sub_eq_zero.mp hz)
  have hr : ((p : ℝ) / q) ^ 2 = 2 := by
    rw [div_pow]
    exact (div_eq_iff (pow_ne_zero 2 hq0)).mpr hpq
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hf : ((p : ℝ) / q - Real.sqrt 2) * ((p : ℝ) / q + Real.sqrt 2) = 0 := by
    nlinarith
  rcases mul_eq_zero.mp hf with h | h
  · exact irrational_sqrt_two.ne_rational p q (sub_eq_zero.mp h).symm
  · apply irrational_sqrt_two.ne_rational (-p) q
    push_cast
    rw [neg_div]
    linarith

/-- A direct quadratic-norm benchmark, valid without any coprimality restriction. -/
theorem sqrt_two_quarter_lower_bound : ApproximationLowerBound (Real.sqrt 2) (1 / 4) := by
  intro p q hq
  have hqr : (0 : ℝ) < q := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast (show (1 : ℤ) ≤ q by omega)
  have hq0 : (q : ℝ) ≠ 0 := ne_of_gt hqr
  have hq2 : (1 : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hden : (0 : ℝ) < (q : ℝ) ^ 2 := sq_pos_of_ne_zero hq0
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  obtain ⟨_, hxupper⟩ := sqrt_two_bounds
  have hxnonneg := Real.sqrt_nonneg (2 : ℝ)
  by_cases hlarge : (1 / 4 : ℝ) ≤ |Real.sqrt 2 - (p : ℝ) / q|
  · exact le_trans ((div_le_iff₀ hden).mpr (by nlinarith)) hlarge
  · have hsmall : |Real.sqrt 2 - (p : ℝ) / q| < (1 / 4 : ℝ) := lt_of_not_ge hlarge
    have hrabs : |(p : ℝ) / q| ≤ |Real.sqrt 2 - (p : ℝ) / q| + Real.sqrt 2 := by
      calc
        |(p : ℝ) / q| = |((p : ℝ) / q - Real.sqrt 2) + Real.sqrt 2| := by congr 1; ring
        _ ≤ |(p : ℝ) / q - Real.sqrt 2| + |Real.sqrt 2| := abs_add_le _ _
        _ = |Real.sqrt 2 - (p : ℝ) / q| + Real.sqrt 2 := by
          rw [abs_sub_comm, abs_of_nonneg hxnonneg]
    have hsum : |(p : ℝ) / q + Real.sqrt 2| ≤ 4 := by
      have ht := abs_add_le ((p : ℝ) / q) (Real.sqrt 2)
      rw [abs_of_nonneg hxnonneg] at ht
      linarith
    have hgap := integer_abs_gap (p ^ 2 - 2 * q ^ 2) (sqrt_two_integer_norm_ne_zero p q hq)
    have hfactor : ((p ^ 2 - 2 * q ^ 2 : ℤ) : ℝ) =
        (q : ℝ) ^ 2 * ((p : ℝ) / q - Real.sqrt 2) * ((p : ℝ) / q + Real.sqrt 2) := by
      push_cast
      field_simp
      nlinarith
    have habs : |((p ^ 2 - 2 * q ^ 2 : ℤ) : ℝ)| =
        (q : ℝ) ^ 2 * |Real.sqrt 2 - (p : ℝ) / q| * |(p : ℝ) / q + Real.sqrt 2| := by
      rw [hfactor, abs_mul, abs_mul, abs_of_nonneg (sq_nonneg (q : ℝ)), abs_sub_comm]
    have hprod : (1 : ℝ) ≤ (q : ℝ) ^ 2 * |Real.sqrt 2 - (p : ℝ) / q| * 4 := by
      calc
        1 ≤ |((p ^ 2 - 2 * q ^ 2 : ℤ) : ℝ)| := hgap
        _ = (q : ℝ) ^ 2 * |Real.sqrt 2 - (p : ℝ) / q| * |(p : ℝ) / q + Real.sqrt 2| := habs
        _ ≤ (q : ℝ) ^ 2 * |Real.sqrt 2 - (p : ℝ) / q| * 4 :=
          mul_le_mul_of_nonneg_left hsum (mul_nonneg (sq_nonneg _) (abs_nonneg _))
    apply (div_le_iff₀ hden).mpr
    nlinarith

theorem sqrt_two_integer_rational_bound (p q : ℤ) (hq : 0 < q) :
    1 / (4 * (q : ℝ) ^ 2) ≤ |Real.sqrt 2 - (p : ℝ) / q| := by
  convert sqrt_two_quarter_lower_bound p q hq using 1
  ring

end PiWeightedColon
