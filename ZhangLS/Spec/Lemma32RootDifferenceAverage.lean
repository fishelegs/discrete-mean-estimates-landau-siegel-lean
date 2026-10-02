import ZhangLS.Spec.Lemma32DivisorGcdAverage
import Mathlib.Data.Int.NatAbs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma32_nonnegative_root_difference_sum {H a : ℕ} (ha : a < H)
    (f : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k) :
    (∑ b ∈ range H, if b=a then 0 else f (((a : ℤ)-(b : ℤ)).natAbs)) ≤
      2 * ∑ k ∈ Ioc 0 H, f k := by
  have he (b : ℕ) : (if b=a then 0 else f (((a : ℤ)-(b : ℤ)).natAbs)) =
      (if b<a then f (a-b) else 0) + (if a<b then f (b-a) else 0) := by
    rcases lt_trichotomy b a with h | h | h
    · simp [h, h.ne, not_lt_of_ge h.le,
        Int.natAbs_natCast_sub_natCast_of_ge h.le]
    · subst b
      simp
    · simp [h, h.ne', not_lt_of_ge h.le,
        Int.natAbs_natCast_sub_natCast_of_le h.le]
  simp_rw [he]
  rw [sum_add_distrib, ← sum_filter, ← sum_filter]
  have hl : (∑ b ∈ (range H).filter (fun b => b<a), f (a-b)) ≤ ∑ k ∈ Ioc 0 H, f k := by
    have hinj : Set.InjOn (fun b => a-b) ((range H).filter (fun b => b<a)) := by
      intro b hb c hc heq
      have hb1 := Finset.mem_filter.mp hb
      have hc1 := Finset.mem_filter.mp hc
      simp only [mem_range] at hb1 hc1
      dsimp only at heq
      omega
    rw [← sum_image hinj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hk
      simp only [mem_filter, mem_range] at hb
      simp only [mem_Ioc]
      omega
    · intro k hk hnot
      exact hf k
  have hr : (∑ b ∈ (range H).filter (fun b => a<b), f (b-a)) ≤ ∑ k ∈ Ioc 0 H, f k := by
    have hinj : Set.InjOn (fun b => b-a) ((range H).filter (fun b => a<b)) := by
      intro b hb c hc heq
      have hb1 := Finset.mem_filter.mp hb
      have hc1 := Finset.mem_filter.mp hc
      simp only [mem_range] at hb1 hc1
      dsimp only at heq
      omega
    rw [← sum_image hinj]
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      obtain ⟨b, hb, rfl⟩ := mem_image.mp hk
      simp only [mem_filter, mem_range] at hb
      simp only [mem_Ioc]
      omega
    · intro k hk hnot
      exact hf k
  linarith

lemma lemma32_real_gcd_root_difference_sum {D H a : ℕ} (hD : 0 < D) (ha : a < H) :
    (∑ b ∈ range H, if b=a then (0 : ℝ) else (D.gcd (((a : ℤ)-(b : ℤ)).natAbs) : ℝ)) ≤
      2 * (H : ℝ) * D.divisors.card := by
  have h1 := lemma32_nonnegative_root_difference_sum ha
    (fun k => (D.gcd k : ℝ)) (fun k => Nat.cast_nonneg _)
  have h2 := lemma32_real_gcd_interval_sum_le_divisors hD H
  calc
    _ ≤ 2 * ∑ k ∈ Ioc 0 H, (D.gcd k : ℝ) := h1
    _ ≤ 2 * ((H : ℝ) * D.divisors.card) := mul_le_mul_of_nonneg_left h2 (by norm_num)
    _ = _ := by ring

end ZhangLS.Spec
