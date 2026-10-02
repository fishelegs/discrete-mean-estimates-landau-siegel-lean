import ZhangLS.Spec.DirichletLSeries
import Mathlib.NumberTheory.DirichletCharacter.Bounds

/-!
# Cancellation and bounds for a primitive character on one period

These are unconditional arithmetic inputs for later Dirichlet-L estimates.
They do not assert the still-missing critical-line quadratic growth bound.
-/

namespace ZhangLS.Spec

open Finset

/-- A real primitive character of modulus greater than one has zero mean
over a complete residue system. -/
theorem RealPrimitiveCharacter.sum_one_period_eq_zero
    {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    ∑ a : ZMod D, χ.chi a = 0 := by
  exact χ.chi.sum_eq_zero_of_ne_one (χ.nontrivial_of_one_lt_modulus hD)

/-- The norm of every value of a Dirichlet character is at most one. -/
theorem RealPrimitiveCharacter.evalNat_norm_le_one
    {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    ‖χ.evalNat n‖ ≤ 1 := by
  simpa [RealPrimitiveCharacter.evalNat] using χ.chi.norm_le_one (n : ZMod D)

/-- The natural-number evaluations cancel on the first complete period. -/
theorem RealPrimitiveCharacter.sum_evalNat_one_period_eq_zero
    {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    ∑ n ∈ range D, χ.evalNat n = 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ n : Fin D, χ.evalNat n = ∑ a : ZMod D, χ.chi a := by
      apply Fintype.sum_equiv (ZMod.finEquiv D).toEquiv
      intro n
      cases D with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ d =>
          change χ.chi ((n.val : ℕ) : ZMod (d + 1)) = χ.chi n
          exact congrArg χ.chi (Fin.cast_val_eq_self n)
    _ = 0 := χ.sum_one_period_eq_zero hD

/-- A complete period cancels regardless of where it starts, provided the
starting point is a multiple of the modulus. -/
theorem RealPrimitiveCharacter.sum_evalNat_block_eq_zero
    {D : ℕ} [NeZero D] (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (k : ℕ) :
    ∑ n ∈ range D, χ.evalNat (k * D + n) = 0 := by
  have hterm : ∀ n : ℕ, χ.evalNat (k * D + n) = χ.evalNat n := by
    intro n
    simp [RealPrimitiveCharacter.evalNat, Nat.cast_add, Nat.cast_mul]
  simp_rw [hterm]
  exact χ.sum_evalNat_one_period_eq_zero hD

/-- The partial sums of a nontrivial primitive character are bounded by its
modulus, uniformly in the length of the sum. -/
theorem RealPrimitiveCharacter.norm_sum_evalNat_le_modulus
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (N : ℕ) :
    ‖∑ n ∈ range N, χ.evalNat n‖ ≤ (D : ℝ) := by
  letI : NeZero D := ⟨Nat.ne_of_gt (Nat.zero_lt_of_lt hD)⟩
  have hfull : ∀ k : ℕ, ∑ n ∈ range (k * D), χ.evalNat n = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, ih,
          χ.sum_evalNat_block_eq_zero hD k]
        simp
  have hrem (r : ℕ) : ‖∑ n ∈ range r, χ.evalNat n‖ ≤ (r : ℝ) := by
    calc
      ‖∑ n ∈ range r, χ.evalNat n‖ ≤
          ∑ n ∈ range r, ‖χ.evalNat n‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range r, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        exact χ.evalNat_norm_le_one n
      _ = r := by simp
  have hsplit : N = (N / D) * D + N % D := by
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div N D).symm
  rw [hsplit, Finset.sum_range_add, hfull, zero_add]
  have hshift : ∀ n : ℕ,
      χ.evalNat ((N / D) * D + n) = χ.evalNat n := by
    intro n
    simp [RealPrimitiveCharacter.evalNat, Nat.cast_add, Nat.cast_mul]
  simp_rw [hshift]
  exact (hrem (N % D)).trans (by exact_mod_cast (Nat.mod_lt N χ.modulus_pos).le)

end ZhangLS.Spec
