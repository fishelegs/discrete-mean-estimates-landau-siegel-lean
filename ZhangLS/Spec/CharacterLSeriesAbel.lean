import ZhangLS.Spec.CharacterPeriodSum
import Mathlib.NumberTheory.LSeries.SumCoeff

/-!
# Abel summation for a primitive character

The complete-period cancellation theorem yields a uniform bound on the
coefficient sums required by mathlib's Abel-summation identity. This module
applies that identity to the actual Dirichlet L-function in its initial
half-plane of absolute convergence.
-/

namespace ZhangLS.Spec

open Finset Complex MeasureTheory Asymptotics
open scoped Real

/-- The standard coefficient sums used in Abel summation have norm at most
the character modulus. -/
theorem RealPrimitiveCharacter.norm_sum_Icc_evalNat_le_modulus
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, χ.evalNat n‖ ≤ (D : ℝ) := by
  letI : Fact (1 < D) := ⟨hD⟩
  have hzero : χ.evalNat 0 = 0 := by
    simp [RealPrimitiveCharacter.evalNat, χ.chi.map_zero]
  have hsum : (∑ n ∈ Icc 1 N, χ.evalNat n) =
      ∑ n ∈ range (N + 1), χ.evalNat n := by
    rw [Nat.range_succ_eq_Icc_zero, Icc_eq_cons_Ioc (Nat.zero_le N),
      sum_cons, hzero, zero_add]
    rw [← Icc_add_one_left_eq_Ioc]
    simp
  rw [hsum]
  exact χ.norm_sum_evalNat_le_modulus hD (N + 1)

/-- Complete-period cancellation supplies the O(1) input for Abel
summation, with an explicit bound D. -/
theorem RealPrimitiveCharacter.sum_Icc_evalNat_isBigO_one
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (fun N : ℕ => ∑ n ∈ Icc 1 N, χ.evalNat n) =O[Filter.atTop]
      (fun _N : ℕ => (1 : ℝ)) := by
  exact isBigO_one_nat_atTop_iff.mpr
    ⟨(D : ℝ), fun N => χ.norm_sum_Icc_evalNat_le_modulus hD N⟩

/-- Abel summation gives an integral representation for the actual
Dirichlet L-function where its Dirichlet series converges absolutely.
Extending the identity to the larger right half-plane requires another
analytic argument. -/
theorem dirichletLFunction_eq_abelIntegral
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : 1 < s.re) :
    dirichletLFunction χ s =
      s * ∫ t in Set.Ioi (1 : ℝ),
        (∑ n ∈ Icc 1 ⌊t⌋₊, χ.evalNat n) * (t : ℂ) ^ (-(s + 1)) := by
  rw [dirichletLFunction_eq_series χ hs]
  have hsum : LSeriesSummable (fun n => χ.evalNat n) s := by
    simpa [RealPrimitiveCharacter.evalNat, dirichletCoeffs] using
      dirichletLSeries_summable_of_one_lt_re χ hs
  have hO :
      (fun n : ℕ => ∑ k ∈ Icc 1 n, χ.evalNat k) =O[Filter.atTop]
        (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
    simpa using χ.sum_Icc_evalNat_isBigO_one hD
  simpa [dirichletLSeries, dirichletCoeffs, RealPrimitiveCharacter.evalNat] using
    (LSeries_eq_mul_integral (fun n => χ.evalNat n) (r := 0)
      (by norm_num) (by linarith) hsum hO)

end ZhangLS.Spec
