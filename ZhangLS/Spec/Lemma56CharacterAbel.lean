import ZhangLS.Spec.Lemma56TwistClassification
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.NumberTheory.LSeries.SumCoeff

/-! # Actual bounded sums and Abel identity for arbitrary nonprincipal characters

Neither primitivity nor real-valuedness is needed. The modulus is positive,
and actual nonprincipal character values supply complete-period cancellation.
-/

namespace ZhangLS.Spec
open Finset Complex MeasureTheory Asymptotics
open scoped Real
set_option maxHeartbeats 1000000

lemma lemma56_character_sum_one_period_eq_zero {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) : ∑ a : ZMod r, θ a = 0 :=
  θ.sum_eq_zero_of_ne_one hθ

lemma lemma56_character_sum_nat_one_period_eq_zero {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) :
    ∑ n ∈ range r, θ (n : ZMod r) = 0 := by
  rw [← Fin.sum_univ_eq_sum_range]
  calc
    ∑ n : Fin r, θ (n : ZMod r) = ∑ a : ZMod r, θ a := by
      apply Fintype.sum_equiv (ZMod.finEquiv r).toEquiv
      intro n
      cases r with
      | zero => exact (NeZero.ne 0 rfl).elim
      | succ d =>
          exact congrArg θ (Fin.cast_val_eq_self n)
    _ = 0 := lemma56_character_sum_one_period_eq_zero θ hθ

lemma lemma56_character_sum_block_eq_zero {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (k : ℕ) :
    ∑ n ∈ range r, θ ((k * r + n : ℕ) : ZMod r) = 0 := by
  have he : ∀ n : ℕ, θ ((k * r + n : ℕ) : ZMod r) = θ (n : ZMod r) := by
    intro n
    simp [Nat.cast_add, Nat.cast_mul]
  simp_rw [he]
  exact lemma56_character_sum_nat_one_period_eq_zero θ hθ

lemma lemma56_character_norm_sum_range_le_modulus {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ range N, θ (n : ZMod r)‖ ≤ (r : ℝ) := by
  have hfull : ∀ k : ℕ, ∑ n ∈ range (k * r), θ (n : ZMod r) = 0 := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [Nat.succ_mul, Finset.sum_range_add, ih, lemma56_character_sum_block_eq_zero θ hθ k]
        simp
  have hrem (b : ℕ) : ‖∑ n ∈ range b, θ (n : ZMod r)‖ ≤ (b : ℝ) := by
    calc
      _ ≤ ∑ n ∈ range b, ‖θ (n : ZMod r)‖ := norm_sum_le _ _
      _ ≤ ∑ _n ∈ range b, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        exact θ.norm_le_one _
      _ = b := by simp
  have hsplit : N = (N / r) * r + N % r := by
    simpa [Nat.mul_comm, Nat.add_comm] using (Nat.mod_add_div N r).symm
  rw [hsplit, Finset.sum_range_add, hfull, zero_add]
  have hshift : ∀ n : ℕ,
      θ (((N / r) * r + n : ℕ) : ZMod r) = θ (n : ZMod r) := by
    intro n
    simp [Nat.cast_add, Nat.cast_mul]
  simp_rw [hshift]
  exact (hrem (N % r)).trans (by exact_mod_cast (Nat.mod_lt N (Nat.pos_of_ne_zero (NeZero.ne r))).le)

lemma lemma56_character_norm_sum_Icc_le_modulus {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Icc 1 N, θ (n : ZMod r)‖ ≤ (r : ℝ) := by
  have hr : r ≠ 1 := fun h => hθ (DirichletCharacter.level_one' θ h)
  have hzero : θ ((0 : ℕ) : ZMod r) = 0 := by
    simpa using DirichletCharacter.map_zero' θ hr
  have hsum : (∑ n ∈ Icc 1 N, θ (n : ZMod r)) =
      ∑ n ∈ range (N + 1), θ (n : ZMod r) := by
    rw [Nat.range_succ_eq_Icc_zero, Icc_eq_cons_Ioc (Nat.zero_le N), sum_cons, hzero, zero_add]
    rw [← Icc_add_one_left_eq_Ioc]
    simp
  rw [hsum]
  exact lemma56_character_norm_sum_range_le_modulus θ hθ (N + 1)

lemma lemma56_character_sum_Icc_isBigO_one {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) :
    (fun N : ℕ => ∑ n ∈ Icc 1 N, θ (n : ZMod r)) =O[Filter.atTop]
      (fun _N : ℕ => (1 : ℝ)) :=
  isBigO_one_nat_atTop_iff.mpr ⟨(r : ℝ), fun N => lemma56_character_norm_sum_Icc_le_modulus θ hθ N⟩

noncomputable def lemma56AbelIntegral {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (s : ℂ) : ℂ :=
  ∫ t : ℝ in Set.Ioi 1, (∑ n ∈ Icc 1 ⌊t⌋₊, θ (n : ZMod r)) * (t : ℂ) ^ (-(s + 1))

lemma lemma56_actual_LFunction_eq_abelIntegral {r : ℕ} [NeZero r]
    (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) {s : ℂ} (hs : 1 < s.re) :
    DirichletCharacter.LFunction θ s = s * lemma56AbelIntegral θ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries θ hs]
  have hsum : LSeriesSummable (fun n => θ (n : ZMod r)) s :=
    DirichletCharacter.LSeriesSummable_of_one_lt_re θ hs
  have hO : (fun n : ℕ => ∑ k ∈ Icc 1 n, θ (k : ZMod r)) =O[Filter.atTop]
      (fun n : ℕ => (n : ℝ) ^ (0 : ℝ)) := by
    simpa using lemma56_character_sum_Icc_isBigO_one θ hθ
  exact LSeries_eq_mul_integral (fun n => θ (n : ZMod r)) (r := 0)
    (by norm_num) (by linarith) hsum hO

end ZhangLS.Spec
