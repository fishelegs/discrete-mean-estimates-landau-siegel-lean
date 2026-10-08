import NewtonIntegral
import BinaryMatrixNonvanishing

noncomputable section

namespace PiWeightedColon

open Polynomial

/-- The actual frequency polynomial whose value at h is the integer origin
entry. The coefficient is zero automatically when c-a>s. -/
def originPolynomial (s a c : ℕ) : ℤ[X] :=
  if a ≤ c then monomial (s - (c - a)) (s.choose (c - a) : ℤ) else 0

def originEntry (s a c : ℕ) (h : ℤ) : ℤ :=
  if a ≤ c ∧ c - a ≤ s then (s.choose (c - a) : ℤ) * h ^ (s - (c - a)) else 0

theorem originPolynomial_eval (s a c : ℕ) (h : ℤ) :
    (originPolynomial s a c).eval h = originEntry s a c h := by
  by_cases ha : a ≤ c
  · by_cases hc : c - a ≤ s
    · simp [originPolynomial, originEntry, ha, hc, eval_monomial]
    · have hz : s.choose (c - a) = 0 := Nat.choose_eq_zero_of_lt (by omega)
      simp [originPolynomial, originEntry, ha, hc, hz]
  · simp [originPolynomial, originEntry, ha]

theorem choose_interchange (s q k : ℕ) :
    s.choose q * (s - q).choose k = s.choose k * (s - k).choose q := by
  have hq := Nat.choose_mul (n := s) (k := q + k) (s := q) (by omega)
  have hk := Nat.choose_mul (n := s) (k := q + k) (s := k) (by omega)
  have hs : (q + k).choose q = (q + k).choose k := Nat.choose_symm_of_eq_add rfl
  simpa only [Nat.add_sub_cancel_left, Nat.add_sub_cancel_right] using
    hq.symm.trans ((congrArg (fun x => s.choose (q + k) * x) hs).trans hk)

theorem originPolynomial_hasse (s a c k : ℕ) (e : Bool) :
    ((originPolynomial s a c).map (Int.castRingHom F2) |>.comp (X + C (endpoint e))).coeff k =
      binaryEntry s a e c k := by
  by_cases ha : a ≤ c
  · simp only [originPolynomial, if_pos ha, map_monomial, Int.coe_castRingHom,
      Int.cast_natCast, monomial_comp, coeff_C_mul, coeff_X_add_C_pow]
    have hm : (s.choose (c - a) : F2) * ((s - (c - a)).choose k : F2) =
        (s.choose k : F2) * ((s - k).choose (c - a) : F2) := by
      simpa only [Nat.cast_mul] using congrArg (fun n : ℕ => (n : F2))
        (choose_interchange s (c - a) k)
    rw [mul_comm (endpoint e ^ _) ((s - (c - a)).choose k : F2), ← mul_assoc, hm]
    have he : s - (c - a) - k = s - k - (c - a) := by omega
    rw [he]
    by_cases hk : k ≤ s
    · by_cases hc : c - a ≤ s - k
      · simp [binaryEntry, hk, ha, hc]
      · have hz := Nat.choose_eq_zero_of_lt (show s - k < c - a by omega)
        simp [binaryEntry, hc, hz]
    · have hz := Nat.choose_eq_zero_of_lt (show s < k by omega)
      simp [binaryEntry, hk, hz]
  · simp [originPolynomial, binaryEntry, ha]

def frequencyNode (e : Bool) (k : ℕ) : ℤ := 2 * (k : ℤ) + if e then 1 else 0

theorem frequencyNode_mod_two (e : Bool) (k : ℕ) :
    (frequencyNode e k : F2) = endpoint e := by
  cases e <;> simp [frequencyNode, endpoint, show (2 : F2) = 0 by decide]

/-- Genuine integer Newton coefficients, computed by monic synthetic division
at the ordered nodes 2k+epsilon. -/
def integerNewtonEntry (s a c k : ℕ) (e : Bool) : ℤ :=
  newtonCoefficient (originPolynomial s a c) (frequencyNode e) k

theorem integerNewtonEntry_zero (s a c : ℕ) (e : Bool) :
    integerNewtonEntry s a c 0 e = originEntry s a c (frequencyNode e 0) := by
  exact originPolynomial_eval s a c (frequencyNode e 0)

theorem frequencyNode_injective (e : Bool) : Function.Injective (frequencyNode e) := by
  intro i j h
  unfold frequencyNode at h
  omega

def newtonEvaluationFactor (e : Bool) (k j : ℕ) : ℤ :=
  ∏ i ∈ Finset.range k, (frequencyNode e j - frequencyNode e i)

theorem newtonEvaluationFactor_above (e : Bool) (k j : ℕ) (hj : j < k) :
    newtonEvaluationFactor e k j = 0 := by
  exact Finset.prod_eq_zero (Finset.mem_range.mpr hj) (sub_self _)

theorem newtonEvaluationFactor_diagonal_ne_zero (e : Bool) (k : ℕ) :
    newtonEvaluationFactor e k k ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  apply sub_ne_zero.mpr
  intro h
  have he := frequencyNode_injective e h
  have hl := Finset.mem_range.mp hi
  omega

/-- Exact integer evaluation factorization of each actual frequency block. -/
theorem originEntry_newton_expansion (s a c j : ℕ) (e : Bool) :
    originEntry s a c (frequencyNode e j) =
      ∑ k ∈ Finset.range (j + 1), integerNewtonEntry s a c k e * newtonEvaluationFactor e k j := by
  simpa only [originPolynomial_eval, integerNewtonEntry, newtonEvaluationFactor]
    using newton_evaluation (originPolynomial s a c) (frequencyNode e) j

theorem integerNewtonEntry_mod_two (s a c k : ℕ) (e : Bool) :
    (integerNewtonEntry s a c k e : F2) = binaryEntry s a e c k := by
  exact (newtonCoefficient_collision (Int.castRingHom F2) _ _ (endpoint e)
    (frequencyNode_mod_two e) k).trans (originPolynomial_hasse s a c k e)

def integerNewtonMatrix (N : ℕ) : Matrix (RowIndex N) (ColIndex N) ℤ :=
  fun r c => integerNewtonEntry (rowS r) (rowA r) (colC c) (colK c) (colE c)

theorem integerNewtonMatrix_mod_two (N : ℕ) :
    (integerNewtonMatrix N).map (Int.castRingHom F2) = binaryMatrix N := by
  ext r c
  exact integerNewtonEntry_mod_two _ _ _ _ _

def squareIntegerNewtonMatrix (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    Matrix (RowIndex N) (RowIndex N) ℤ := fun r c => integerNewtonMatrix N r (e c)

theorem squareIntegerNewtonMatrix_mod_two (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    (squareIntegerNewtonMatrix N e).map (Int.castRingHom F2) = squareBinaryMatrix N e := by
  ext r c
  exact integerNewtonEntry_mod_two _ _ _ _ _

/-- The integral Newton matrix has determinant whose reduction modulo two is
nonzero. This is not yet the original evaluation determinant. -/
theorem integerNewton_det_mod_two_ne_zero (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    ((squareIntegerNewtonMatrix N e).det : F2) ≠ 0 := by
  have h := squareBinaryMatrix_det_ne_zero N e
  rw [Int.cast_det]
  simpa only [← squareIntegerNewtonMatrix_mod_two N e] using h

theorem integerNewton_det_ne_zero (N : ℕ) (e : RowIndex N ≃ ColIndex N) :
    (squareIntegerNewtonMatrix N e).det ≠ 0 := by
  intro h
  have hz := integerNewton_det_mod_two_ne_zero N e
  rw [h, Int.cast_zero] at hz
  exact hz rfl

end PiWeightedColon
