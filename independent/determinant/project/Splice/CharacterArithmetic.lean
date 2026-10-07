import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

/-!
# Genuine character arithmetic for the elementary first-moment adapter

This file uses actual Mathlib Dirichlet characters. It does not assume a
prime-mass inequality or any analytic estimate. `nu` is the real part of the
actual arithmetic convolution `DirichletCharacter.zetaMul`.
-/

namespace Splice

open Finset
open scoped BigOperators ComplexOrder

variable {D : ℕ}

noncomputable def nu (χ : DirichletCharacter ℂ D) (n : ℕ) : ℝ :=
  (χ.zetaMul n).re

/-- Exactly the prime mass used by the unchanged determinant source. -/
noncomputable def goodPrimeMass (D : ℕ) (χ : DirichletCharacter ℂ D) : ℝ :=
  ∑ p ∈ (Nat.primesLE ⌊(D : ℝ) ^ 32⌋₊).filter
    (fun p => 86713344 < p ∧ ¬ p ∣ 2 * D ∧ χ p = -1), Real.log p / (p : ℝ)

/-- The actual analytic continuation, never the ungrouped `LSeries` tsum at 1. -/
noncomputable def LOne [NeZero D] (χ : DirichletCharacter ℂ D) : ℝ :=
  (χ.LFunction 1).re

theorem real_character_sq (χ : DirichletCharacter ℂ D)
    (hreal : ∀ a : ZMod D, (χ a).im = 0) : χ ^ 2 = 1 := by
  have hinv : χ⁻¹ = χ := by
    rw [← MulChar.star_eq_inv]
    apply MulChar.ext'
    intro a
    exact Complex.conj_eq_iff_im.mpr (hreal a)
  calc
    χ ^ 2 = χ⁻¹ * χ := by rw [pow_two, hinv]
    _ = 1 := inv_mul_cancel χ

theorem nu_nonneg (χ : DirichletCharacter ℂ D)
    (hreal : ∀ a : ZMod D, (χ a).im = 0) (n : ℕ) : 0 ≤ nu χ n := by
  exact (Complex.nonneg_iff.mp (DirichletCharacter.zetaMul_nonneg (real_character_sq χ hreal) n)).1

theorem nu_eq_sum_divisors (χ : DirichletCharacter ℂ D) (n : ℕ) :
    nu χ n = ∑ d ∈ n.divisors, (χ d).re := by
  unfold nu DirichletCharacter.zetaMul
  rw [ArithmeticFunction.coe_zeta_mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hd0 : d ≠ 0 := by
    intro h
    subst d
    simpa using hd
  simp [toArithmeticFunction, hd0]

theorem nu_prime (χ : DirichletCharacter ℂ D) {p : ℕ} (hp : p.Prime) :
    nu χ p = 1 + (χ p).re := by
  rw [nu_eq_sum_divisors]
  have h := Nat.sum_divisors_prime_pow (f := fun d => (χ d).re) hp (k := 1)
  simpa [Finset.sum_range_succ] using h

theorem nu_split_prime (χ : DirichletCharacter ℂ D) {p : ℕ}
    (hp : p.Prime) (hsplit : χ p = 1) : nu χ p = 2 := by
  rw [nu_prime χ hp, hsplit]
  norm_num

theorem nu_inert_prime (χ : DirichletCharacter ℂ D) {p : ℕ}
    (hp : p.Prime) (hinert : χ p = -1) : nu χ p = 0 := by
  rw [nu_prime χ hp, hinert]
  norm_num

theorem character_sum_range_period [NeZero D] (χ : DirichletCharacter ℂ D)
    (hne : χ ≠ 1) : ∑ k ∈ Finset.range D, χ k = 0 := by
  calc
    ∑ k ∈ Finset.range D, χ k = ∑ a : ZMod D, χ a := by
      apply Finset.sum_bij (fun (k : ℕ) _ => (k : ZMod D))
      · intro k hk
        simp
      · intro a ha b hb hab
        have := congrArg ZMod.val hab
        simpa [ZMod.val_natCast_of_lt (Finset.mem_range.mp ha),
          ZMod.val_natCast_of_lt (Finset.mem_range.mp hb)] using this
      · intro a ha
        exact ⟨a.val, Finset.mem_range.mpr a.val_lt, ZMod.natCast_zmod_val a⟩
      · intro k hk
        rfl
    _ = 0 := χ.sum_eq_zero_of_ne_one hne

theorem character_sum_range_add_period [NeZero D] (χ : DirichletCharacter ℂ D)
    (hne : χ ≠ 1) (n : ℕ) :
    ∑ k ∈ Finset.range (D + n), χ k = ∑ k ∈ Finset.range n, χ k := by
  rw [Finset.sum_range_add, character_sum_range_period χ hne, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  simp

theorem character_sum_range_norm_le [NeZero D] (χ : DirichletCharacter ℂ D)
    (hne : χ ≠ 1) (n : ℕ) : ‖∑ k ∈ Finset.range n, χ k‖ ≤ (D : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n < D
    · calc
        ‖∑ k ∈ Finset.range n, χ k‖ ≤ ∑ k ∈ Finset.range n, ‖χ k‖ := norm_sum_le _ _
        _ ≤ ∑ k ∈ Finset.range n, (1 : ℝ) := by
          exact Finset.sum_le_sum fun k hk => χ.norm_le_one _
        _ = (n : ℝ) := by simp
        _ ≤ (D : ℝ) := by exact_mod_cast hn.le
    · have hDn : D ≤ n := Nat.le_of_not_gt hn
      have hD : 0 < D := Nat.pos_of_ne_zero (NeZero.ne D)
      have hsmall : n - D < n := by omega
      calc
        ‖∑ k ∈ Finset.range n, χ k‖ = ‖∑ k ∈ Finset.range (n - D), χ k‖ := by
          conv_lhs => rw [← Nat.add_sub_of_le hDn]
          rw [character_sum_range_add_period χ hne]
        _ ≤ (D : ℝ) := ih (n - D) hsmall

theorem character_sum_Icc_norm_le [NeZero D] (χ : DirichletCharacter ℂ D)
    (hne : χ ≠ 1) (n : ℕ) : ‖∑ k ∈ Finset.Icc 1 n, χ k‖ ≤ (D : ℝ) := by
  have hD : D ≠ 1 := by
    intro h
    subst D
    exact hne (DirichletCharacter.level_one χ)
  have hz : χ (0 : ZMod D) = 0 := χ.map_zero' hD
  have hsum : ∑ k ∈ Finset.Icc 1 n, χ k = ∑ k ∈ Finset.range (n + 1), χ k := by
    apply Finset.sum_subset
    · intro k hk
      simp only [Finset.mem_Icc, Finset.mem_range] at hk ⊢
      omega
    · intro k hk hnot
      have hk0 : k = 0 := by
        simp only [Finset.mem_Icc, Finset.mem_range] at hk hnot
        omega
      simpa [hk0] using hz
  rw [hsum]
  exact character_sum_range_norm_le χ hne (n + 1)

theorem character_sum_Icc_abs_le [NeZero D] (χ : DirichletCharacter ℂ D)
    (hne : χ ≠ 1) (n : ℕ) : |∑ k ∈ Finset.Icc 1 n, (χ k).re| ≤ (D : ℝ) := by
  rw [← Complex.re_sum]
  exact (Complex.abs_re_le_norm _).trans (character_sum_Icc_norm_le χ hne n)

/-- A safeguard documenting why the unconditional tsum is the wrong endpoint. -/
theorem raw_LSeries_one_eq_zero [NeZero D] (χ : DirichletCharacter ℂ D) :
    LSeries (fun n => χ n) 1 = 0 := by
  exact LSeries.eq_zero_of_not_LSeriesSummable _ _
    (χ.not_LSeriesSummable_at_one (NeZero.ne D))

end Splice

#print axioms Splice.nu_nonneg
#print axioms Splice.character_sum_Icc_norm_le
#print axioms Splice.raw_LSeries_one_eq_zero
