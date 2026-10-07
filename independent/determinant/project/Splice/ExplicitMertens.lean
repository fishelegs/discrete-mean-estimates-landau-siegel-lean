import Splice.MertensSupport

/-!
# A numerical elementary Mertens estimate

This file makes the constant in the existing elementary Mertens development
explicit.  The two new estimates are `psi_le_four_mul` and
`higher_prime_power_error_le_two`.  The latter uses a telescoping logarithmic
majorant, rather than an improper integral.  Together with the existing
von-Mangoldt lower estimate, they give the constant `4` for every `x ≥ 1`.

There is no hypothesis asserting a Mertens bound or a prime-mass bound.
-/

namespace Splice.ExplicitMertens

open Real Finset
open ArithmeticFunction hiding log
open Splice.MertensSupport

private theorem log_two_le_one : log (2 : ℝ) ≤ 1 := by
  have h := log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

private theorem log_four_le_two : log (4 : ℝ) ≤ 2 := by
  have h := Real.log_pow (2 : ℝ) 2
  norm_num at h
  rw [h]
  linarith [log_two_le_one]

/-- A deliberately loose but useful elementary logarithm bound. -/
theorem log_le_sqrt_of_pos {x : ℝ} (hx : 0 < x) : log x ≤ sqrt x := by
  have hs : 0 < sqrt x := sqrt_pos.mpr hx
  have h := log_le_sub_one_of_pos (div_pos hs (show (0 : ℝ) < 2 by norm_num))
  rw [log_div hs.ne' (by norm_num), log_sqrt hx.le] at h
  linarith [log_two_le_one]

/-- An explicit Chebyshev bound, obtained from the library's sharper bound. -/
theorem psi_le_four_mul {x : ℝ} (hx : 0 ≤ x) : Chebyshev.psi x ≤ 4 * x := by
  by_cases hx1 : 1 ≤ x
  · have hs : 0 ≤ sqrt x := sqrt_nonneg x
    have hlog := log_le_sqrt_of_pos (show 0 < x by linarith)
    have hmul : 2 * sqrt x * log x ≤ 2 * x := by
      calc
        _ ≤ 2 * sqrt x * sqrt x :=
          mul_le_mul_of_nonneg_left hlog (by positivity)
        _ = 2 * x := by nlinarith [sq_sqrt hx]
    have hmain := mul_le_mul_of_nonneg_right log_four_le_two hx
    have hpsi := Chebyshev.psi_le hx1
    linarith
  · rw [Chebyshev.psi_eq_zero_of_lt_two (by linarith)]
    positivity

/-- The logarithmic majorant whose discrete differences bound the higher-power
error.  The hypothesis is only a lower bound for the real argument. -/
theorem log_tail_step {x : ℝ} (hx : 2 ≤ x) :
    log x / (x * (x - 1)) ≤
      (log (x - 1) + 2) / (x - 1) - (log x + 2) / x := by
  have hxpos : 0 < x := by linarith
  have hmpos : 0 < x - 1 := by linarith
  have hlog : log x - log (x - 1) ≤ 1 / (x - 1) := by
    calc
      _ = log (x / (x - 1)) := (log_div hxpos.ne' hmpos.ne').symm
      _ ≤ x / (x - 1) - 1 := log_le_sub_one_of_pos (div_pos hxpos hmpos)
      _ = 1 / (x - 1) := by field_simp [hmpos.ne']; ring
  have hprod : x * (log x - log (x - 1)) ≤ 2 := by
    calc
      _ ≤ x * (1 / (x - 1)) := mul_le_mul_of_nonneg_left hlog hxpos.le
      _ = x / (x - 1) := by ring
      _ ≤ 2 := (div_le_iff₀ hmpos).mpr (by linarith)
  have heq : (log (x - 1) + 2) / (x - 1) - (log x + 2) / x =
      (x * (log (x - 1) + 2) - (x - 1) * (log x + 2)) / (x * (x - 1)) := by
    field_simp [hxpos.ne', hmpos.ne']
  rw [heq]
  exact (div_le_div_iff_of_pos_right (mul_pos hxpos hmpos)).mpr (by nlinarith)

/-- The total contribution used to dominate all higher prime powers is at most
`2`.  The proof even bounds the corresponding sum over all integers ≥ 2. -/
theorem higher_prime_power_error_le_two : E₁ ≤ 2 := by
  let f : ℕ → ℝ := fun p => if p.Prime then log p / (p * (p - 1)) else 0
  let F : ℕ → ℝ := fun n => (log ((n : ℝ) + 1) + 2) / ((n : ℝ) + 1)
  have hF : ∀ n, 0 ≤ F n := by
    intro n
    dsimp [F]
    apply div_nonneg
    · have : 0 ≤ log ((n : ℝ) + 1) := log_nonneg (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
      linarith
    · positivity
  have hstep : ∀ n, f (n + 2) ≤ F n - F (n + 1) := by
    intro n
    have hterm : f (n + 2) ≤
        log ((n : ℝ) + 2) / (((n : ℝ) + 2) * (((n : ℝ) + 2) - 1)) := by
      dsimp [f]
      split_ifs with hp
      · simp only [Nat.cast_add, Nat.cast_ofNat, le_refl]
      · apply div_nonneg
        · exact log_nonneg (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith)
        · apply mul_nonneg <;> linarith [show (0 : ℝ) ≤ n from Nat.cast_nonneg n]
    have h := hterm.trans (log_tail_step (by have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith :
      (2 : ℝ) ≤ (n : ℝ) + 2))
    have hsub : (n : ℝ) + 2 - 1 = (n : ℝ) + 1 := by ring
    simpa [F, hsub, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using h
  have hpartial : ∀ n, (∑ p ∈ range (n + 2), f p) ≤ 2 - F n := by
    intro n
    induction n with
    | zero => norm_num [Finset.sum_range_succ, f, F]
    | succ n ih =>
      rw [show n + 1 + 2 = (n + 2) + 1 by omega, sum_range_succ]
      have hs := hstep n
      linarith
  change (∑' p : ℕ, f p) ≤ 2
  apply Real.tsum_le_of_sum_range_le E₁.summand_nonneg
  intro n
  rcases n with _ | n
  · simp
  rcases n with _ | n
  · norm_num [f]
  · have h := hpartial n
    have hnonneg := hF n
    convert (show (∑ p ∈ range (n + 2), f p) ≤ 2 by linarith) using 1

/-- Numerical upper error bound for the weighted von-Mangoldt sum. -/
theorem vonMangoldt_error_le_four {x : ℝ} (hx : 1 ≤ x) : E₁Λ x ≤ 4 := by
  unfold E₁Λ
  suffices x * ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d / d ≤ x * (log x + 4) by
    linarith [le_of_mul_le_mul_left this (by linarith)]
  calc
    _ = ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (x / d) := by
      rw [Finset.mul_sum]
      ring_nf
    _ ≤ ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d * (⌊x / d⌋₊ + 1) := by
      gcongr
      exact (Nat.lt_floor_add_one _).le
    _ = (∑ d ∈ Ioc 0 ⌊x⌋₊, log d) + ∑ d ∈ Ioc 0 ⌊x⌋₊, Λ d := by
      simp_rw [mul_add, mul_one]
      rw [Finset.sum_add_distrib, sum_log_eq_sum_mangoldt]
    _ ≤ x * log x + 4 * x := by
      gcongr
      · exact sum_log_le hx
      · exact psi_le_four_mul (by linarith)
    _ = _ := by ring

/-- The explicit elementary Mertens estimate, with no distributional or
character-theoretic premise.  It holds already for `x ≥ 1`. -/
theorem prime_log_div_abs_error_le_four {x : ℝ} (hx : 1 ≤ x) :
    |∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p - log x| ≤ 4 := by
  rw [Nat.primesLE_eq_filter_Ioc_zero]
  change |E₁p x| ≤ 4
  apply abs_le.mpr
  constructor
  · have hcompare := E₁Λ.le_E₁p_add_E₁ hx
    have hlower := E₁Λ.ge hx
    linarith [higher_prime_power_error_le_two]
  · have hcompare := E₁p.le_E₁Λ x
    linarith [vonMangoldt_error_le_four hx]

/-- A finite prime interval has logarithmic mass at least the logarithmic
interval length minus `8`.  This is the directly consumable two-cutoff form. -/
theorem prime_log_div_sub_ge {x y : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    log y - log x - 8 ≤
      (∑ p ∈ Nat.primesLE ⌊y⌋₊, log p / p) -
        ∑ p ∈ Nat.primesLE ⌊x⌋₊, log p / p := by
  have hx' := (abs_le.mp (prime_log_div_abs_error_le_four hx)).2
  have hy' := (abs_le.mp (prime_log_div_abs_error_le_four hy)).1
  linarith

/-- Natural-cutoff version, avoiding a floor in downstream finite-sum code. -/
theorem prime_log_div_abs_error_le_four_nat {n : ℕ} (hn : 1 ≤ n) :
    |∑ p ∈ Nat.primesLE n, log p / p - log n| ≤ 4 := by
  simpa using prime_log_div_abs_error_le_four (x := (n : ℝ)) (by exact_mod_cast hn)

/-- Natural-cutoff interval estimate in the exact form needed by the
finite-prime assembly. -/
theorem prime_log_div_sub_ge_nat {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    log n - log m - 8 ≤
      (∑ p ∈ Nat.primesLE n, log p / p) -
        ∑ p ∈ Nat.primesLE m, log p / p := by
  simpa using prime_log_div_sub_ge (x := (m : ℝ)) (y := (n : ℝ))
    (by exact_mod_cast hm) (by exact_mod_cast hn)

/-- The exact unfiltered logarithmic mass needed between `D^4` and `D^32`. -/
theorem prime_log_div_conductor_interval_ge {D : ℕ} (hD : 1 ≤ D) :
    28 * log D - 8 ≤
      (∑ p ∈ Nat.primesLE (D ^ 32), log p / p) -
        ∑ p ∈ Nat.primesLE (D ^ 4), log p / p := by
  have h := prime_log_div_sub_ge_nat
    (m := D ^ 4) (n := D ^ 32) (one_le_pow₀ hD) (one_le_pow₀ hD)
  simp only [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at h
  linarith

end Splice.ExplicitMertens
