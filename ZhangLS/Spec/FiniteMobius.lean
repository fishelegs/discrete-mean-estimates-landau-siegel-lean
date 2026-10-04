import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic.Ring

/-!
# Exact finite truncated Möbius identity

A reusable, unnumbered arithmetic-function identity. The convolution unit `1` is delta;
`ArithmeticFunction.zeta` is the function equal to one at every positive integer.
All arithmetic functions take value zero at zero, as in Mathlib.
The coefficient ring is an arbitrary commutative ring, so the theorem applies directly
with complex coefficients. No analytic bound or signed-family gain is asserted.
-/

namespace ZhangLS.Spec.FiniteMobius

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius ArithmeticFunction.zeta

variable {R : Type*} [CommRing R]

/-- The literal inclusive truncation `mu(n) * 1_(n <= U)`. -/
def truncated (U : ℕ) : ArithmeticFunction R :=
  ⟨fun n => if n ≤ U then (moebius n : R) else 0, by simp⟩

@[simp] theorem truncated_apply (U n : ℕ) :
    truncated (R := R) U n = if n ≤ U then (moebius n : R) else 0 := rfl

@[simp] theorem truncated_apply_of_le {U n : ℕ} (h : n ≤ U) :
    truncated (R := R) U n = (moebius n : R) := by simp [h]

@[simp] theorem truncated_apply_of_lt {U n : ℕ} (h : U < n) :
    truncated (R := R) U n = 0 := by simp [Nat.not_le.mpr h]

/-- The generic coefficient version is precisely the canonical cast of the integer truncation. -/
theorem truncated_intCast (U : ℕ) :
    (truncated (R := ℤ) U : ArithmeticFunction R) = truncated (R := R) U := by
  ext n
  by_cases h : n ≤ U <;> simp [h]

/-- The finite-inverse defect, with the convolution unit, not the constant-one function. -/
def defect (U : ℕ) : ArithmeticFunction R :=
  1 - truncated (R := R) U * (zeta : ArithmeticFunction R)

/-- Every term in the relevant divisor sum uses the original Möbius coefficient. -/
theorem truncated_mul_zeta_eq_one {U n : ℕ} (hn : n ≤ U) :
    (truncated (R := R) U * (zeta : ArithmeticFunction R)) n =
      (1 : ArithmeticFunction R) n := by
  rw [← coe_moebius_mul_coe_zeta (R := R)]
  rw [ArithmeticFunction.mul_apply, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro d hd
  rw [truncated_apply_of_le ((Nat.divisor_le
    (Nat.fst_mem_divisors_of_mem_antidiagonal hd)).trans hn)]
  rfl

/-- In particular this includes the constant coefficient n=1. -/
theorem defect_eq_zero {U n : ℕ} (hn : n ≤ U) : defect (R := R) U n = 0 := by
  simp [defect, sub_eq_add_neg, truncated_mul_zeta_eq_one hn]

/-- If f vanishes through U and g through V, their convolution vanishes through UV. -/
theorem mul_eq_zero_of_le {f g : ArithmeticFunction R} {U V n : ℕ}
    (hf : ∀ a, a ≤ U → f a = 0) (hg : ∀ b, b ≤ V → g b = 0)
    (hn : n ≤ U * V) : (f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  obtain ⟨hdprod, _⟩ := Nat.mem_divisorsAntidiagonal.mp hd
  by_cases ha : d.1 ≤ U
  · rw [hf _ ha, zero_mul]
  by_cases hb : d.2 ≤ V
  · rw [hg _ hb, mul_zero]
  have ha' : U < d.1 := Nat.lt_of_not_ge ha
  have hb' : V < d.2 := Nat.lt_of_not_ge hb
  have hlt : U * V < d.1 * d.2 := by
    calc
      U * V ≤ U * d.2 := Nat.mul_le_mul_left U (Nat.le_of_lt hb')
      _ < d.1 * d.2 := Nat.mul_lt_mul_of_pos_right ha' (Nat.zero_lt_of_lt hb')
  exact False.elim ((Nat.not_lt_of_ge hn) (hdprod ▸ hlt))

/-- A positive convolution power has the inclusive product support bound. -/
theorem pow_eq_zero_of_le {f : ArithmeticFunction R} {U : ℕ}
    (hf : ∀ n, n ≤ U → f n = 0) {J n : ℕ} (hJ : 0 < J) (hn : n ≤ U ^ J) :
    (f ^ J) n = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hJ)
  have h : ∀ k n, n ≤ U ^ (k + 1) → (f ^ (k + 1)) n = 0 := by
    intro k
    induction k with
    | zero => simpa using hf
    | succ k ih =>
      intro n hn
      rw [pow_succ]
      apply mul_eq_zero_of_le ih hf
      simpa [pow_succ] using hn
  exact h k n hn

/-- Convolution by any arithmetic function preserves an initial interval of zeros. -/
theorem mul_eq_zero_of_right {f g : ArithmeticFunction R} {N n : ℕ}
    (hg : ∀ d, d ≤ N → g d = 0) (hn : n ≤ N) : (f * g) n = 0 := by
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro d hd
  rw [hg _ ((Nat.divisor_le (Nat.snd_mem_divisors_of_mem_antidiagonal hd)).trans hn),
    mul_zero]

theorem defect_pow_eq_zero {U J n : ℕ} (hJ : 0 < J) (hn : n ≤ U ^ J) :
    (defect (R := R) U ^ J) n = 0 :=
  pow_eq_zero_of_le (fun _ h => defect_eq_zero h) hJ hn

theorem moebius_mul_defect_pow_eq_zero {U J n : ℕ}
    (hJ : 0 < J) (hn : n ≤ U ^ J) :
    ((moebius : ArithmeticFunction R) * defect (R := R) U ^ J) n = 0 :=
  mul_eq_zero_of_right (fun _ h => defect_pow_eq_zero hJ h) hn

/-- The universal finite polynomial identity behind the truncation argument. -/
theorem binomial_inverse_identity {S : Type*} [CommRing S]
    (m z q : S) (hq : q * z = 1) (J : ℕ) :
    q - q * (1 - m * z) ^ J =
      ∑ j ∈ Finset.range J,
        ((-1 : ℤ) ^ j * (J.choose (j + 1) : ℤ)) • (m ^ (j + 1) * z ^ j) := by
  have hbin : (1 - m * z) ^ J =
      (∑ j ∈ Finset.range J, (-(m * z)) ^ (j + 1) * (J.choose (j + 1) : S)) + 1 := by
    rw [show 1 - m * z = -(m * z) + 1 by ring, add_pow, Finset.sum_range_succ']
    simp
  have hsub : q - q * (1 - m * z) ^ J =
      -(q * ∑ j ∈ Finset.range J,
        (-(m * z)) ^ (j + 1) * (J.choose (j + 1) : S)) := by
    rw [hbin]
    ring
  rw [hsub, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have hqpow : q * (m * z) ^ (j + 1) = m ^ (j + 1) * z ^ j := by
    rw [mul_pow, pow_succ z]
    calc
      q * (m ^ (j + 1) * (z ^ j * z)) = (q * z) * (m ^ (j + 1) * z ^ j) := by ring
      _ = m ^ (j + 1) * z ^ j := by rw [hq, one_mul]
  rw [neg_pow, pow_succ (-1 : S)]
  simp only [zsmul_eq_mul, Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one,
    Int.cast_natCast]
  calc
    -(q * ((-1) ^ j * -1 * (m * z) ^ (j + 1) * (J.choose (j + 1) : S))) =
        (-1) ^ j * (J.choose (j + 1) : S) * (q * (m * z) ^ (j + 1)) := by ring
    _ = _ := by rw [hqpow]

/-- Evaluation as an additive homomorphism, used to evaluate finite sums and integer scalars. -/
def eval (n : ℕ) : ArithmeticFunction R →+ R where
  toFun f := f n
  map_zero' := rfl
  map_add' _ _ := rfl

/-- Exact finite HB identity for every positive J, at every n <= U^J.

The summation index j here is one less than the conventional level: it runs from 0 to J-1.
Thus the summand is (-1)^j binom(J,j+1) m_U^(j+1) * zeta^j.
The coefficient casts are canonical integer casts into R.
-/
theorem finite_moebius_identity {U J n : ℕ} (hJ : 0 < J) (hn : n ≤ U ^ J) :
    (moebius n : R) =
      ∑ j ∈ Finset.range J,
        (((-1 : ℤ) ^ j * (J.choose (j + 1) : ℤ) : ℤ) : R) *
          (truncated (R := R) U ^ (j + 1) * (zeta : ArithmeticFunction R) ^ j) n := by
  have h := congrArg (eval (R := R) n)
    (binomial_inverse_identity (truncated (R := R) U)
      (zeta : ArithmeticFunction R) (moebius : ArithmeticFunction R)
      coe_moebius_mul_coe_zeta J)
  simp only [map_sub, map_sum, map_zsmul] at h
  change (moebius n : R) -
      ((moebius : ArithmeticFunction R) *
        (1 - truncated (R := R) U * (zeta : ArithmeticFunction R)) ^ J) n =
      ∑ j ∈ Finset.range J,
        ((-1 : ℤ) ^ j * (J.choose (j + 1) : ℤ)) •
          (truncated (R := R) U ^ (j + 1) * (zeta : ArithmeticFunction R) ^ j) n at h
  have hz := moebius_mul_defect_pow_eq_zero (R := R) hJ hn
  change ((moebius : ArithmeticFunction R) *
    (1 - truncated (R := R) U * (zeta : ArithmeticFunction R)) ^ J) n = 0 at hz
  simpa only [hz, sub_zero, zsmul_eq_mul] using h

/-- The four-level decomposition with exact coefficient vector (4,-6,4,-1). -/
theorem finite_moebius_identity_four {U n : ℕ} (hn : n ≤ U ^ 4) :
    (moebius n : R) =
      4 * truncated (R := R) U n -
      6 * (truncated (R := R) U ^ 2 * (zeta : ArithmeticFunction R)) n +
      4 * (truncated (R := R) U ^ 3 * (zeta : ArithmeticFunction R) ^ 2) n -
      (truncated (R := R) U ^ 4 * (zeta : ArithmeticFunction R) ^ 3) n := by
  have h := finite_moebius_identity (R := R) (J := 4) (by decide) hn
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
    pow_zero, pow_one, mul_one, Int.reducePow, Int.reduceMul, Int.cast_ofNat,
    Int.cast_neg, Int.cast_one, Int.cast_zero, zero_add, add_zero] at h
  convert h using 1; ring

/-- The inclusive endpoint is a direct specialization, with no strict-inequality loss. -/
theorem finite_moebius_identity_endpoint (U J : ℕ) (hJ : 0 < J) :
    (moebius (U ^ J) : R) =
      ∑ j ∈ Finset.range J,
        (((-1 : ℤ) ^ j * (J.choose (j + 1) : ℤ) : ℤ) : R) *
          (truncated (R := R) U ^ (j + 1) * (zeta : ArithmeticFunction R) ^ j) (U ^ J) :=
  finite_moebius_identity hJ le_rfl

/-- n=1 is included for every U>=1 and positive J. -/
theorem finite_moebius_identity_one {U J : ℕ} (hU : 1 ≤ U) (hJ : 0 < J) :
    (1 : R) =
      ∑ j ∈ Finset.range J,
        (((-1 : ℤ) ^ j * (J.choose (j + 1) : ℤ) : ℤ) : R) *
          (truncated (R := R) U ^ (j + 1) * (zeta : ArithmeticFunction R) ^ j) 1 := by
  simpa using (finite_moebius_identity (R := R) (n := 1) hJ (one_le_pow₀ hU))

end ZhangLS.Spec.FiniteMobius
