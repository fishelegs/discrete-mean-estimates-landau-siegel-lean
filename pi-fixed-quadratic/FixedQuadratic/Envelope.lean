import FixedQuadratic.Resultant
import FixedQuadratic.Mahler

open Polynomial
open scoped BigOperators
namespace FixedQuadratic

noncomputable def coefficientL1 (P : Polynomial ℂ) : ℝ :=
  ∑ n ∈ P.support, ‖P.coeff n‖

theorem eval_norm_le_coefficientL1 (P : Polynomial ℂ) (z : ℂ) (d : ℕ)
    (hd : P.natDegree ≤ d) :
    ‖P.eval z‖ ≤ coefficientL1 P * (max 1 ‖z‖)^d := by
  classical
  rw [Polynomial.eval_eq_sum, Polynomial.sum_def]
  apply (norm_sum_le _ _).trans
  unfold coefficientL1
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  rw [norm_mul, norm_pow]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖z‖^n ≤ (max 1 ‖z‖)^n := pow_le_pow_left₀ (norm_nonneg _) (le_max_right _ _) _
    _ ≤ (max 1 ‖z‖)^d := pow_le_pow_right₀ (le_max_left _ _) ((Polynomial.le_natDegree_of_ne_zero (Polynomial.mem_support_iff.mp hn)).trans hd)

/-- Exact one-center lower bound including one coefficient-l1 cost. -/
theorem quadratic_coefficient_lower (f P : Polynomial GaussianInt)
    (a : GaussianInt) (x y : ℂ) (d : ℕ) (hP : P.natDegree ≤ d)
    (hf : f.map GaussianInt.toComplex = C (a : ℂ) * ((X - C x) * (X - C y)))
    (ha : a ≠ 0) (hx : (P.map GaussianInt.toComplex).eval x ≠ 0)
    (hy : (P.map GaussianInt.toComplex).eval y ≠ 0) :
    1 ≤ ‖(a : ℂ)‖^d * ‖(P.map GaussianInt.toComplex).eval x‖ *
      (coefficientL1 (P.map GaussianInt.toComplex) * (max 1 ‖y‖)^d) := by
  apply (quadratic_norm_lower f P a x y d hP hf ha hx hy).trans
  apply mul_le_mul_of_nonneg_left
    (eval_norm_le_coefficientL1 _ y d (natDegree_map_le.trans hP))
  positivity

/-- The coefficient norm is positive whenever evaluation is nonzero. -/
theorem coefficientL1_pos_of_eval_ne_zero (P : Polynomial ℂ) (z : ℂ)
    (hz : P.eval z ≠ 0) : 0 < coefficientL1 P := by
  have h := eval_norm_le_coefficientL1 P z P.natDegree le_rfl
  have hp : 0 < ‖P.eval z‖ := norm_pos_iff.mpr hz
  have hpow : 0 < (max 1 ‖z‖)^P.natDegree := pow_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) _
  exact pos_of_mul_pos_left (lt_of_lt_of_le hp h) hpow.le

/-- The exact single-center Mahler form of the arithmetic replacement, with
one l1 denominator and exponent d, valid also for degree upper bounds. -/
theorem quadratic_l1_mahler_lower (f P : Polynomial GaussianInt)
    (a : GaussianInt) (x y : ℂ) (d : ℕ) (hP : P.natDegree ≤ d)
    (hf : f.map GaussianInt.toComplex = C (a : ℂ) * ((X-C x)*(X-C y)))
    (ha : a ≠ 0) (hx : (P.map GaussianInt.toComplex).eval x ≠ 0)
    (hy : (P.map GaussianInt.toComplex).eval y ≠ 0) :
    (max 1 ‖x‖)^d /
      (coefficientL1 (P.map GaussianInt.toComplex) *
        (‖(a : ℂ)‖ * max 1 ‖x‖ * max 1 ‖y‖)^d) ≤
      ‖(P.map GaussianInt.toComplex).eval x‖ := by
  have h := quadratic_coefficient_lower f P a x y d hP hf ha hx hy
  have hB := coefficientL1_pos_of_eval_ne_zero (P.map GaussianInt.toComplex) x hx
  have haC : (a : ℂ) ≠ 0 := GaussianInt.toComplex_eq_zero.not.mpr ha
  have hR : 0 < max 1 ‖x‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hS : 0 < max 1 ‖y‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  apply (div_le_iff₀ (mul_pos hB (pow_pos (mul_pos (mul_pos (norm_pos_iff.mpr haC) hR) hS) d))).mpr
  have hh := mul_le_mul_of_nonneg_left h (pow_nonneg hR.le d)
  simp only [mul_pow] at *
  nlinarith [hh]

end FixedQuadratic
