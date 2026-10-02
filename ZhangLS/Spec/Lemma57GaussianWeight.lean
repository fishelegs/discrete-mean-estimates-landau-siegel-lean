import ZhangLS.Spec.Lemma57Arithmetic
import ZhangLS.Spec.ReciprocalDivisorEulerFactorization
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# Zhang's Gaussian weight in Lemma 5.7

In Section 4 of Zhang's paper, with `L = log D`, the smoothing function is

  g(x) = (1 / sqrt(pi)) * ∫_{-∞}^{L^15 log x} exp(-t^2) dt.

For the finite arithmetic extraction in Lemma 5.7 it is enough, and technically
cleaner, to use the equivalent normalization at zero

  g(x) = 1/2 + (1 / sqrt(pi)) * ∫_0^{L^15 log x} exp(-t^2) dt.

The equality of the two formulas follows from the Gaussian half-line integral.
The key point needed in Lemma 5.7 is immediate from this form: if `x ≥ 1`, then
`g(x) ≥ 1/2`.  Since `n ∣ D` implies `D^4 / n ≥ 1`, the divisor-side smoothing
constant can be taken to be the explicit absolute constant `1/2`.
-/

namespace ZhangLS.Spec

open scoped BigOperators Interval

/-- The upper endpoint `L^15 log x` in Zhang's formula, where `L = log D`. -/
noncomputable def zhangGaussianEndpoint (D : ℕ) (x : ℝ) : ℝ :=
  (Real.log (D : ℝ)) ^ 15 * Real.log x

/-- Zhang's Gaussian smoothing function, written in its finite-integral form
normalized at the origin. -/
noncomputable def zhangGaussianWeight (D : ℕ) (x : ℝ) : ℝ :=
  (1 : ℝ) / 2 + (Real.sqrt Real.pi)⁻¹ *
    ∫ t : ℝ in (0 : ℝ)..zhangGaussianEndpoint D x, Real.exp (-(t ^ 2))

/-- On the range `x ≥ 1`, Zhang's Gaussian endpoint is nonnegative. -/
theorem zhangGaussianEndpoint_nonneg
    {D : ℕ} {x : ℝ} (hD : 1 < D) (hx : 1 ≤ x) :
    0 ≤ zhangGaussianEndpoint D x := by
  unfold zhangGaussianEndpoint
  have hlogD : 0 ≤ Real.log (D : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast (Nat.le_of_lt hD)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  exact mul_nonneg (pow_nonneg hlogD _) hlogx

/-- The Gaussian weight is at least one half for every `x ≥ 1`. -/
theorem zhangGaussianWeight_half_le
    {D : ℕ} {x : ℝ} (hD : 1 < D) (hx : 1 ≤ x) :
    (1 : ℝ) / 2 ≤ zhangGaussianWeight D x := by
  unfold zhangGaussianWeight
  have hend : 0 ≤ zhangGaussianEndpoint D x :=
    zhangGaussianEndpoint_nonneg hD hx
  have hint :
      0 ≤ ∫ t : ℝ in (0 : ℝ)..zhangGaussianEndpoint D x, Real.exp (-(t ^ 2)) := by
    refine intervalIntegral.integral_nonneg_of_forall hend ?_
    intro t
    exact (Real.exp_pos _).le
  have hsqrt : 0 ≤ (Real.sqrt Real.pi)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have htail :
      0 ≤ (Real.sqrt Real.pi)⁻¹ *
        ∫ t : ℝ in (0 : ℝ)..zhangGaussianEndpoint D x, Real.exp (-(t ^ 2)) :=
    mul_nonneg hsqrt hint
  linarith

/-- A divisor `n` of a nontrivial modulus satisfies `D^4 / n ≥ 1`. -/
theorem one_le_lemma57WeightArgument_of_mem_divisors
    {D n : ℕ} (hD : 1 < D) (hn : n ∈ Nat.divisors D) :
    (1 : ℝ) ≤ lemma57WeightArgument D n := by
  have hD0 : D ≠ 0 := (Nat.zero_lt_of_lt hD).ne'
  have hnD : n ∣ D := (Nat.mem_divisors.mp hn).1
  have hn0 : n ≠ 0 := ne_zero_of_dvd_ne_zero hD0 hnD
  have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn0
  have hnleNat : n ≤ D := Nat.le_of_dvd (Nat.pos_of_ne_zero hD0) hnD
  have hnle : (n : ℝ) ≤ (D : ℝ) := by exact_mod_cast hnleNat
  have hDone : (1 : ℝ) ≤ D := by exact_mod_cast (Nat.le_of_lt hD)
  have hcube : (1 : ℝ) ≤ (D : ℝ) ^ 3 := one_le_pow₀ hDone
  have hDnonneg : (0 : ℝ) ≤ D := by positivity
  have hnle4 : (n : ℝ) ≤ (D : ℝ) ^ 4 := by
    calc
      (n : ℝ) ≤ (D : ℝ) := hnle
      _ = (D : ℝ) * 1 := by ring
      _ ≤ (D : ℝ) * ((D : ℝ) ^ 3) := mul_le_mul_of_nonneg_left hcube hDnonneg
      _ = (D : ℝ) ^ 4 := by ring
  unfold lemma57WeightArgument
  exact (le_div_iff₀ hnpos).2 (by simpa using hnle4)

/-- The exact weight input required by the arithmetic extraction: the explicit
absolute constant is `c_g = 1/2`. -/
theorem zhangGaussianWeightLowerBound_half :
    Lemma57WeightLowerBound zhangGaussianWeight ((1 : ℝ) / 2) := by
  constructor
  · norm_num
  · intro D n hD hn
    exact zhangGaussianWeight_half_le hD
      (one_le_lemma57WeightArgument_of_mem_divisors hD hn)

/-- Combining the explicit Gaussian constant `1/2` with the unconditional
reciprocal-divisor constant `1/4` gives the divisor-side constant `1/8`. -/
theorem lemma57_gaussian_divisor_arithmetic_scale
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (1 : ℝ) / 8 * lemma57Scale D ≤
      lemma57DivisorSubsum χ (zhangGaussianWeight D) := by
  have h := lemma57_divisor_arithmetic_scale
    zhangGaussianWeight ((1 : ℝ) / 2) ((1 : ℝ) / 4)
    zhangGaussianWeightLowerBound_half
    reciprocalDivisorLowerBound_quarter_proved χ hD
  norm_num at h ⊢
  simpa using h

end ZhangLS.Spec
