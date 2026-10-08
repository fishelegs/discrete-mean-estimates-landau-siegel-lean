import SqrtTwoBenchmark

noncomputable section

namespace PiWeightedColon

/-- The positive Pell sequence beginning with `(1,1)`. -/
def sqrtTwoPellPair : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | n + 1 => let v := sqrtTwoPellPair n; (v.1 + 2 * v.2, v.1 + v.2)

def sqrtTwoPellP (n : ℕ) : ℕ := (sqrtTwoPellPair n).1
def sqrtTwoPellQ (n : ℕ) : ℕ := (sqrtTwoPellPair n).2

theorem sqrtTwoPellP_zero : sqrtTwoPellP 0 = 1 := rfl
theorem sqrtTwoPellQ_zero : sqrtTwoPellQ 0 = 1 := rfl
theorem sqrtTwoPellP_succ (n : ℕ) :
    sqrtTwoPellP (n + 1) = sqrtTwoPellP n + 2 * sqrtTwoPellQ n := rfl
theorem sqrtTwoPellQ_succ (n : ℕ) :
    sqrtTwoPellQ (n + 1) = sqrtTwoPellP n + sqrtTwoPellQ n := rfl

theorem sqrtTwoPell_bounds (n : ℕ) :
    1 ≤ sqrtTwoPellQ n ∧ sqrtTwoPellQ n ≤ sqrtTwoPellP n ∧
    sqrtTwoPellP n ≤ 2 * sqrtTwoPellQ n ∧ n + 1 ≤ sqrtTwoPellQ n := by
  induction n with
  | zero => norm_num [sqrtTwoPellP_zero, sqrtTwoPellQ_zero]
  | succ n ih =>
    rw [sqrtTwoPellP_succ, sqrtTwoPellQ_succ]
    omega

theorem sqrtTwoPell_growth (n : ℕ) :
    sqrtTwoPellQ n < sqrtTwoPellQ (n + 1) ∧
    sqrtTwoPellQ (n + 1) ≤ 3 * sqrtTwoPellQ n := by
  have hb := sqrtTwoPell_bounds n
  rw [sqrtTwoPellQ_succ]
  omega

theorem sqrtTwoPell_norm (n : ℕ) :
    (sqrtTwoPellP n : ℤ) ^ 2 - 2 * (sqrtTwoPellQ n : ℤ) ^ 2 = (-1) ^ (n + 1) := by
  induction n with
  | zero => norm_num [sqrtTwoPellP_zero, sqrtTwoPellQ_zero]
  | succ n ih =>
    rw [sqrtTwoPellP_succ, sqrtTwoPellQ_succ]
    push_cast
    calc
      _ = -((sqrtTwoPellP n : ℤ) ^ 2 - 2 * (sqrtTwoPellQ n : ℤ) ^ 2) := by ring
      _ = -((-1 : ℤ) ^ (n + 1)) := by rw [ih]
      _ = (-1 : ℤ) ^ (n + 1 + 1) := by rw [pow_succ]; ring

theorem sqrtTwoPell_norm_abs (n : ℕ) :
    |(sqrtTwoPellP n : ℤ) ^ 2 - 2 * (sqrtTwoPellQ n : ℤ) ^ 2| = 1 := by
  rw [sqrtTwoPell_norm, abs_pow]
  norm_num

theorem sqrtTwoPell_independent (n : ℕ) :
    (sqrtTwoPellP n : ℤ) * sqrtTwoPellQ (n + 1) -
      (sqrtTwoPellQ n : ℤ) * sqrtTwoPellP (n + 1) ≠ 0 := by
  have he : (sqrtTwoPellP n : ℤ) * sqrtTwoPellQ (n + 1) -
      (sqrtTwoPellQ n : ℤ) * sqrtTwoPellP (n + 1) =
      (sqrtTwoPellP n : ℤ) ^ 2 - 2 * (sqrtTwoPellQ n : ℤ) ^ 2 := by
    rw [sqrtTwoPellP_succ, sqrtTwoPellQ_succ]
    push_cast
    ring
  rw [he, sqrtTwoPell_norm]
  exact pow_ne_zero _ (by norm_num)

theorem sqrtTwoPell_error (n : ℕ) :
    |(sqrtTwoPellQ n : ℝ) * Real.sqrt 2 - sqrtTwoPellP n| ≤
      1 / (2 * (sqrtTwoPellQ n : ℝ)) := by
  obtain ⟨hq, hqp, _, _⟩ := sqrtTwoPell_bounds n
  have hqr : (1 : ℝ) ≤ sqrtTwoPellQ n := by exact_mod_cast hq
  have hqpr : (sqrtTwoPellQ n : ℝ) ≤ sqrtTwoPellP n := by exact_mod_cast hqp
  have hx := sqrt_two_bounds.1
  have hx0 := Real.sqrt_nonneg (2 : ℝ)
  have hnorm : |(sqrtTwoPellP n : ℝ) ^ 2 - 2 * (sqrtTwoPellQ n : ℝ) ^ 2| = 1 := by
    exact_mod_cast sqrtTwoPell_norm_abs n
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hprod : |(sqrtTwoPellQ n : ℝ) * Real.sqrt 2 - sqrtTwoPellP n| *
      ((sqrtTwoPellP n : ℝ) + sqrtTwoPellQ n * Real.sqrt 2) = 1 := by
    have hf : (sqrtTwoPellP n : ℝ) ^ 2 - 2 * (sqrtTwoPellQ n : ℝ) ^ 2 =
        ((sqrtTwoPellP n : ℝ) - sqrtTwoPellQ n * Real.sqrt 2) *
        ((sqrtTwoPellP n : ℝ) + sqrtTwoPellQ n * Real.sqrt 2) := by
      nlinarith [sq_nonneg ((sqrtTwoPellQ n : ℝ) - Real.sqrt 2)]
    rw [hf, abs_mul, abs_sub_comm,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ sqrtTwoPellP n + sqrtTwoPellQ n * Real.sqrt 2)] at hnorm
    exact hnorm
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * sqrtTwoPellQ n)).mpr
  have hsize : 2 * (sqrtTwoPellQ n : ℝ) ≤
      (sqrtTwoPellP n : ℝ) + sqrtTwoPellQ n * Real.sqrt 2 := by
    nlinarith
  calc
    _ ≤ |(sqrtTwoPellQ n : ℝ) * Real.sqrt 2 - sqrtTwoPellP n| *
        ((sqrtTwoPellP n : ℝ) + sqrtTwoPellQ n * Real.sqrt 2) :=
      mul_le_mul_of_nonneg_left hsize (abs_nonneg _)
    _ = 1 := hprod

/-- The first Pell denominator at least `M` and its successor stay below `9M`. -/
theorem sqrtTwoPell_scale (M : ℕ) (hM : 0 < M) : ∃ n : ℕ,
    M ≤ sqrtTwoPellQ n ∧ M ≤ sqrtTwoPellQ (n + 1) ∧
    sqrtTwoPellQ n ≤ 9 * M ∧ sqrtTwoPellQ (n + 1) ≤ 9 * M := by
  have hex : ∃ n : ℕ, M ≤ sqrtTwoPellQ n :=
    ⟨M, le_trans (by omega) (sqrtTwoPell_bounds M).2.2.2⟩
  let n := Nat.find hex
  have hstart : M ≤ sqrtTwoPellQ n := Nat.find_spec hex
  have hnext : M ≤ sqrtTwoPellQ (n + 1) := le_trans hstart (sqrtTwoPell_growth n).1.le
  have hbound : sqrtTwoPellQ n ≤ 3 * M := by
    cases hn : n with
    | zero => simp only [sqrtTwoPellQ_zero]; omega
    | succ k =>
      have hprev : ¬ M ≤ sqrtTwoPellQ k := Nat.find_min hex (by omega : k < n)
      have hg := (sqrtTwoPell_growth k).2
      omega
  refine ⟨n, hstart, hnext, by omega, ?_⟩
  have hg := (sqrtTwoPell_growth n).2
  omega

theorem sqrtTwoPell_error_at_scale (n : ℕ) (Q : ℤ) (hQ : 0 < Q)
    (hscale : (Q : ℝ) ≤ sqrtTwoPellQ n) :
    |(sqrtTwoPellQ n : ℝ) * Real.sqrt 2 - sqrtTwoPellP n| ≤ (1 / 2 : ℝ) / Q := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hden : (0 : ℝ) < 2 * (sqrtTwoPellQ n : ℝ) := by linarith
  calc
    _ ≤ 1 / (2 * (sqrtTwoPellQ n : ℝ)) := sqrtTwoPell_error n
    _ ≤ (1 / 2 : ℝ) / Q := by
      apply (div_le_div_iff₀ hden hQr).mpr
      nlinarith

/-- The recurrence constructs independent approximants at every positive integer scale. -/
theorem sqrt_two_has_approximation_pairs : HasApproximationPairs (Real.sqrt 2) 9 (1 / 2) := by
  intro Q hQ
  have hQnat : 0 < Q.toNat := by omega
  have hcast : (Q.toNat : ℤ) = Q := Int.toNat_of_nonneg hQ.le
  obtain ⟨n, hn, hnext, hn_size, hnext_size⟩ := sqrtTwoPell_scale Q.toNat hQnat
  have hnR : (Q : ℝ) ≤ sqrtTwoPellQ n := by
    have hi : Q ≤ (sqrtTwoPellQ n : ℤ) := by
      have hnI : (Q.toNat : ℤ) ≤ sqrtTwoPellQ n := by exact_mod_cast hn
      simpa only [hcast] using hnI
    exact_mod_cast hi
  have hnextR : (Q : ℝ) ≤ sqrtTwoPellQ (n + 1) := by
    have hi : Q ≤ (sqrtTwoPellQ (n + 1) : ℤ) := by
      have hnI : (Q.toNat : ℤ) ≤ sqrtTwoPellQ (n + 1) := by exact_mod_cast hnext
      simpa only [hcast] using hnI
    exact_mod_cast hi
  refine ⟨sqrtTwoPellP n, sqrtTwoPellQ n, sqrtTwoPellP (n + 1),
    sqrtTwoPellQ (n + 1), ?_, ?_, ?_, ?_, sqrtTwoPell_independent n, ?_, ?_⟩
  · exact_mod_cast (sqrtTwoPell_bounds n).1
  · exact_mod_cast (sqrtTwoPell_bounds (n + 1)).1
  · have hi : (sqrtTwoPellQ n : ℤ) ≤ 9 * Q := by
      have hnI : (sqrtTwoPellQ n : ℤ) ≤ 9 * (Q.toNat : ℤ) := by exact_mod_cast hn_size
      simpa only [hcast] using hnI
    exact_mod_cast hi
  · have hi : (sqrtTwoPellQ (n + 1) : ℤ) ≤ 9 * Q := by
      have hnI : (sqrtTwoPellQ (n + 1) : ℤ) ≤ 9 * (Q.toNat : ℤ) := by exact_mod_cast hnext_size
      simpa only [hcast] using hnI
    exact_mod_cast hi
  · simpa only [Int.cast_natCast] using sqrtTwoPell_error_at_scale n Q hQ hnR
  · simpa only [Int.cast_natCast] using sqrtTwoPell_error_at_scale (n + 1) Q hQ hnextR

theorem sqrt_two_pair_lower_bound : ApproximationLowerBound (Real.sqrt 2) (1 / 18) := by
  have h := approximation_pairs_lower_bound (Real.sqrt 2) 9 (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) sqrt_two_has_approximation_pairs
  norm_num at h ⊢
  exact h

end PiWeightedColon
