import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Real.Basic

/-! Positive finite conductor reindexing k,r|k to h=k/r,r. Every divisor
and endpoint is retained; unused target pairs only add nonnegative terms. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

theorem divisorConductor_sum_le (X : ℕ) (F : ℕ → ℕ → ℝ)
    (hF : ∀h r : ℕ, 0≤F h r) :
    (∑k∈Icc 1 X, ∑r∈k.divisors, if 1<r then F (k/r) r else 0)≤
      ∑h∈Icc 1 X, ∑r∈Icc 2 X, F h r := by
  let S : Finset (Σ _k : ℕ, ℕ) := (Icc 1 X).sigma (fun k => k.divisors.filter (fun r => 1<r))
  let f : (Σ _k : ℕ, ℕ) → ℕ×ℕ := fun i => (i.1/i.2,i.2)
  have hmem (i : Σ _k : ℕ, ℕ) (hi : i∈S) :
      i.1∈Icc 1 X ∧ i.2∣i.1 ∧ 1<i.2 := by
    have hh := mem_sigma.mp hi
    have hr := mem_filter.mp hh.2
    exact ⟨hh.1,(Nat.mem_divisors.mp hr.1).1,hr.2⟩
  have hinj : ∀i∈S, ∀j∈S, f i=f j → i=j := by
    intro i hi j hj he
    have h1 := congrArg Prod.fst he
    have h2 := congrArg Prod.snd he
    dsimp [f] at h1 h2
    have he1 : i.1=j.1 := by
      rw [←Nat.div_mul_cancel (hmem i hi).2.1,←Nat.div_mul_cancel (hmem j hj).2.1,h1,h2]
    exact Sigma.ext he1 (by cases i; cases j; dsimp at *; subst_vars; rfl)
  have hsub : S.image f⊆(Icc 1 X).product (Icc 2 X) := by
    intro j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hj
    have hm := hmem i hi
    have hk0 : 0<i.1 := (mem_Icc.mp hm.1).1
    have hr0 : 0<i.2 := by omega
    have hrle := Nat.le_of_dvd hk0 hm.2.1
    have hq0 := Nat.div_pos hrle hr0
    have hkX := (mem_Icc.mp hm.1).2
    exact mem_product.mpr ⟨mem_Icc.mpr ⟨hq0,(Nat.div_le_self _ _).trans hkX⟩,
      mem_Icc.mpr ⟨hm.2.2,hrle.trans hkX⟩⟩
  calc
    _=∑i∈S, F (f i).1 (f i).2 := by
      dsimp [S,f]
      rw [sum_sigma]
      apply sum_congr rfl
      intro k hk
      rw [sum_filter]
    _=∑j∈S.image f,F j.1 j.2 := by rw [sum_image hinj]
    _≤∑j∈(Icc 1 X).product (Icc 2 X),F j.1 j.2 :=
      sum_le_sum_of_subset_of_nonneg hsub (fun j hj hnot => hF j.1 j.2)
    _=_ := sum_product _ _ _

end ZhangLS.Spec
