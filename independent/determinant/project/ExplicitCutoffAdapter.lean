import EarlyDeterminantAdapter
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Explicit cutoff arithmetic for the conditional determinant adapter

This file removes the elementary numerical assumptions from
`EarlyDeterminantAdapter.lower_bound_from_same_witness` at the cutoff
`D >= 2^24`.  It does not prove the supplied prime-mass estimate or construct
the coherent finite witness.  In particular, the endpoint remains conditional
on both of those inputs, with exactly the same `m`, `D`, and `k` throughout.

The first tail is also presented as `9 / (D * sqrt D)`, with a proved identity
identifying it with `9 * D^(-3/2)`.  Neither error bound is assumed.

The natural-conductor version casts `D` to the reals before taking powers,
logarithms, or square roots.  There is no asserted identification of `t` with
an L-function; that analytic interpretation remains the caller's obligation.
-/

namespace ExplicitCutoffAdapter

open EarlyDeterminantAdapter

theorem half_le_log_two : (1 : ℝ) / 2 ≤ Real.log 2 := by
  have h := Real.one_sub_inv_le_log_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  norm_num at h ⊢
  exact h

theorem log_eight_le_three : Real.log 8 ≤ 3 := by
  have h8 : Real.log (8 : ℝ) = 3 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 3
    norm_num at h
    exact h
  rw [h8]
  linarith [log_two_le_one]

theorem log_four_le_two : Real.log 4 ≤ 2 := by
  have h4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    have h := Real.log_pow (2 : ℝ) 2
    norm_num at h
    exact h
  rw [h4]
  linarith [log_two_le_one]

theorem conductor_pos {D : ℝ} (hD : (2 : ℝ) ^ 24 ≤ D) : 0 < D := by
  exact lt_of_lt_of_le (by norm_num) hD

theorem log_conductor_ge_twelve {D : ℝ} (hD : (2 : ℝ) ^ 24 ≤ D) :
    12 ≤ Real.log D := by
  have h := Real.log_le_log (show (0 : ℝ) < 2 ^ 24 by norm_num) hD
  rw [Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith [half_le_log_two]

theorem sqrt_conductor_ge_4096 {D : ℝ} (hD : (2 : ℝ) ^ 24 ≤ D) :
    4096 ≤ Real.sqrt D := by
  apply Real.le_sqrt_of_sq_le
  norm_num at hD ⊢
  exact hD

/-- The sharper first-tail bound in the elementary derivation. -/
theorem first_error_le_power {D : ℝ} (hD : (2 : ℝ) ^ 24 ≤ D) :
    9 / (D * Real.sqrt D) ≤ 9 / (2 : ℝ) ^ 36 := by
  have hDpos := conductor_pos hD
  have hs := sqrt_conductor_ge_4096 hD
  have hden : (2 : ℝ) ^ 36 ≤ D * Real.sqrt D := by
    calc
      (2 : ℝ) ^ 36 = (2 : ℝ) ^ 24 * 4096 := by norm_num
      _ ≤ D * Real.sqrt D := mul_le_mul hD hs (by norm_num) hDpos.le
  exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hden

theorem first_error_lt {D : ℝ} (hD : (2 : ℝ) ^ 24 ≤ D) :
    9 / (D * Real.sqrt D) < 1 / 1024 := by
  exact lt_of_le_of_lt (first_error_le_power hD) (by norm_num)

/-- A deliberately coarse denominator bound already suffices for the second
tail, avoiding any numerical approximation to `D^32`. -/
theorem second_error_lt {D k : ℝ} (hD : (2 : ℝ) ^ 24 ≤ D) (hk : 1 ≤ k) :
    3 / (2 * k * D ^ 32) < 1 / 1024 := by
  have hDpos := conductor_pos hD
  have hkpos : 0 < k := lt_of_lt_of_le (by norm_num) hk
  have hD1 : 1 ≤ D := le_trans (by norm_num) hD
  have hpow : D ≤ D ^ 32 := le_self_pow₀ hD1 (by norm_num)
  have hp0 : 0 ≤ D ^ 32 := pow_nonneg hDpos.le _
  have hmul : D ^ 32 ≤ k * D ^ 32 := by
    simpa using mul_le_mul_of_nonneg_right hk hp0
  apply (div_lt_iff₀ (show 0 < 2 * k * D ^ 32 by positivity)).2
  norm_num at hD
  nlinarith

/-- The square-root form is exactly the real-power form, for positive `D`. -/
theorem first_error_eq_rpow {D : ℝ} (hD : 0 < D) :
    9 / (D * Real.sqrt D) = 9 * D ^ (-(3 / 2 : ℝ)) := by
  have hpow : D ^ (3 / 2 : ℝ) = D * Real.sqrt D := by
    calc
      D ^ (3 / 2 : ℝ) = D ^ ((1 : ℝ) + 1 / 2) := by norm_num
      _ = D ^ (1 : ℝ) * D ^ (1 / 2 : ℝ) := Real.rpow_add hD _ _
      _ = D * Real.sqrt D := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
  rw [Real.rpow_neg hD.le, hpow, div_eq_mul_inv]

theorem first_rpow_error_lt {D : ℝ} (hD : (2 : ℝ) ^ 24 ≤ D) :
    9 * D ^ (-(3 / 2 : ℝ)) < 1 / 1024 := by
  rw [← first_error_eq_rpow (conductor_pos hD)]
  exact first_error_lt hD

/-- All numerical hypotheses of the elementary adapter, visibly derived
from the cutoff and `k >= 1`. -/
theorem numerical_cutoff_bounds {D k : ℝ}
    (hD : (2 : ℝ) ^ 24 ≤ D) (hk : 1 ≤ k) :
    12 ≤ Real.log D ∧ Real.log 8 ≤ 3 ∧ Real.log 4 ≤ 2 ∧
      9 * D ^ (-(3 / 2 : ℝ)) < 1 / 1024 ∧
      3 / (2 * k * D ^ 32) < 1 / 1024 := by
  exact ⟨log_conductor_ge_twelve hD, log_eight_le_three, log_four_le_two,
    first_rpow_error_lt hD, second_error_lt hD hk⟩

/-- Explicit-cutoff endpoint with the first error in square-root form. -/
theorem lower_bound_from_same_witness_sqrt
    {D k m t : ℝ} (hD : (2 : ℝ) ^ 24 ≤ D) (hk : 1 ≤ k)
    (hprime : 7 / 8 - 1 / (4 * Real.log D) - 14 * Real.log D * t -
      9 / (D * Real.sqrt D) ≤ m / (32 * Real.log D))
    (w : FiniteWitness (Real.log D) k (D ^ 96) (D ^ 32) m
      (Real.log 8) (Real.log 4)) :
    1 / (1536 * Real.log D) < t ∧ 1 / (4096 * Real.log D) < t := by
  have hDpos := conductor_pos hD
  exact lower_bound_from_same_witness (log_conductor_ge_twelve hD) hk
    (pow_pos hDpos _) (pow_pos hDpos _)
    (Real.log_nonneg (by norm_num)) log_eight_le_three
    (Real.log_nonneg (by norm_num)) log_four_le_two
    (first_error_lt hD) (second_error_lt hD hk) le_rfl hprime w

/-- Explicit-cutoff endpoint in the original real-power notation.  The only
substantive analytic inputs left are the prime-mass estimate and one supplied
coherent finite witness; their existence is not asserted. -/
theorem lower_bound_from_same_witness_rpow
    {D k m t : ℝ} (hD : (2 : ℝ) ^ 24 ≤ D) (hk : 1 ≤ k)
    (hprime : 7 / 8 - 1 / (4 * Real.log D) - 14 * Real.log D * t -
      9 * D ^ (-(3 / 2 : ℝ)) ≤ m / (32 * Real.log D))
    (w : FiniteWitness (Real.log D) k (D ^ 96) (D ^ 32) m
      (Real.log 8) (Real.log 4)) :
    1 / (1536 * Real.log D) < t ∧ 1 / (4096 * Real.log D) < t := by
  apply lower_bound_from_same_witness_sqrt hD hk ?_ w
  simpa only [first_error_eq_rpow (conductor_pos hD)] using hprime

/-- Natural-conductor specialization, with every analytic operation on the
real cast of `D`. -/
theorem lower_bound_from_same_witness_nat
    {D : ℕ} {k m t : ℝ} (hD : 2 ^ 24 ≤ D) (hk : 1 ≤ k)
    (hprime : 7 / 8 - 1 / (4 * Real.log (D : ℝ)) -
      14 * Real.log (D : ℝ) * t - 9 * (D : ℝ) ^ (-(3 / 2 : ℝ)) ≤
      m / (32 * Real.log (D : ℝ)))
    (w : FiniteWitness (Real.log (D : ℝ)) k ((D : ℝ) ^ 96) ((D : ℝ) ^ 32) m
      (Real.log 8) (Real.log 4)) :
    1 / (1536 * Real.log (D : ℝ)) < t ∧
      1 / (4096 * Real.log (D : ℝ)) < t := by
  have hDreal : (2 : ℝ) ^ 24 ≤ (D : ℝ) := by exact_mod_cast hD
  exact lower_bound_from_same_witness_rpow hDreal hk hprime w

/-- The concrete value of kappa used by the determinant specialization. -/
noncomputable def explicitKappa : ℝ :=
  (86713344 : ℝ) ^ (2 / 3 : ℝ) / (4 * 97 ^ 2)

theorem explicitKappa_ge_one : 1 ≤ explicitKappa := by
  have hbase : (194 : ℝ) ^ 3 ≤ 86713344 := by norm_num
  have hp := Real.rpow_le_rpow (show (0 : ℝ) ≤ 194 ^ 3 by positivity)
    hbase (show (0 : ℝ) ≤ 2 / 3 by norm_num)
  have hid : ((194 : ℝ) ^ 3) ^ (2 / 3 : ℝ) = (194 : ℝ) ^ 2 := by
    calc
      ((194 : ℝ) ^ 3) ^ (2 / 3 : ℝ) =
          ((194 : ℝ) ^ (3 : ℝ)) ^ (2 / 3 : ℝ) := by norm_num [Real.rpow_natCast]
      _ = (194 : ℝ) ^ ((3 : ℝ) * (2 / 3)) :=
        (Real.rpow_mul (by norm_num) _ _).symm
      _ = (194 : ℝ) ^ (2 : ℕ) := by norm_num [Real.rpow_natCast]
  rw [hid] at hp
  unfold explicitKappa
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 4 * 97 ^ 2)).2
  norm_num at hp ⊢
  exact hp

/-- Numerical H and cutoff fixed, while retaining the genuinely unproved
prime-mass and coherent-witness inputs as explicit hypotheses. -/
theorem lower_bound_at_explicit_parameters
    {D m t : ℝ} (hD : (2 : ℝ) ^ 24 ≤ D)
    (hprime : 7 / 8 - 1 / (4 * Real.log D) - 14 * Real.log D * t -
      9 * D ^ (-(3 / 2 : ℝ)) ≤ m / (32 * Real.log D))
    (w : FiniteWitness (Real.log D) explicitKappa (D ^ 96) (D ^ 32) m
      (Real.log 8) (Real.log 4)) :
    1 / (1536 * Real.log D) < t ∧ 1 / (4096 * Real.log D) < t := by
  exact lower_bound_from_same_witness_rpow hD explicitKappa_ge_one hprime w

#check log_conductor_ge_twelve
#check first_error_le_power
#check first_error_eq_rpow
#check numerical_cutoff_bounds
#check lower_bound_from_same_witness_sqrt
#check lower_bound_from_same_witness_rpow
#check lower_bound_from_same_witness_nat
#check explicitKappa_ge_one
#check lower_bound_at_explicit_parameters

#print axioms log_conductor_ge_twelve
#print axioms first_error_le_power
#print axioms first_error_eq_rpow
#print axioms numerical_cutoff_bounds
#print axioms lower_bound_from_same_witness_sqrt
#print axioms lower_bound_from_same_witness_rpow
#print axioms lower_bound_from_same_witness_nat
#print axioms explicitKappa_ge_one
#print axioms lower_bound_at_explicit_parameters

end ExplicitCutoffAdapter
