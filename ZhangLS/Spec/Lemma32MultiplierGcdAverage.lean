import ZhangLS.Spec.Lemma32SymmetricTriangleSum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Intervals
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma32_fin_positive_sum (A : ℕ) (f : ℕ → ℝ) :
    (∑ a : Fin A, f (a.val+1)) = ∑ a ∈ Ioc 0 A, f a := by
  rw [Fin.sum_univ_eq_sum_range (fun n => f (n+1)) A, Finset.range_eq_Ico, Finset.sum_Ico_add' f 0 A 1]
  have he : Ico (0+1) (A+1)=Ioc 0 A := by
    ext a
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  rw [he]

lemma lemma32_normalized_gcd_row {b : ℕ} (hb : 0 < b) :
    (∑ a ∈ Ioc 0 b, (a.gcd b : ℝ)/(b : ℝ)) ≤ (b.divisors.card : ℝ) := by
  have hg : (∑ a ∈ Ioc 0 b, (a.gcd b : ℝ)) ≤ (b : ℝ)*b.divisors.card := by
    simpa only [Nat.gcd_comm] using lemma32_real_gcd_interval_sum_le_divisors hb b
  rw [← Finset.sum_div]
  have hc := div_le_div_of_nonneg_right hg (Nat.cast_nonneg b : (0 : ℝ) ≤ (b : ℝ))
  have he : (b : ℝ)*(b.divisors.card : ℝ)/(b : ℝ)=(b.divisors.card : ℝ) := by
    exact mul_div_cancel_left₀ _ (Nat.cast_ne_zero.mpr hb.ne')
  rw [he] at hc
  exact hc

lemma lemma32_multiplier_normalized_gcd_sum (A : ℕ) :
    (∑ a ∈ Ioc 0 A, ∑ b ∈ Ioc 0 A, (a.gcd b : ℝ)/((max a b : ℕ) : ℝ)) ≤
      2*(A : ℝ)*(1+Real.log (A : ℝ)) := by
  have hsym (a b : ℕ) : (a.gcd b : ℝ)/((max a b : ℕ) : ℝ) = (b.gcd a : ℝ)/((max b a : ℕ) : ℝ) := by
    rw [Nat.gcd_comm, Nat.max_comm]
  have ht := lemma32_symmetric_triangle_sum_bound A
    (fun a b => (a.gcd b : ℝ)/((max a b : ℕ) : ℝ))
    (fun a b => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hsym
  have hu : (∑ b ∈ Ioc 0 A, ∑ a ∈ Ioc 0 b, (a.gcd b : ℝ)/((max a b : ℕ) : ℝ)) ≤
      ∑ b ∈ Ioc 0 A, (b.divisors.card : ℝ) := by
    apply Finset.sum_le_sum
    intro b hb
    have he : (∑ a ∈ Ioc 0 b, (a.gcd b : ℝ)/((max a b : ℕ) : ℝ)) =
        ∑ a ∈ Ioc 0 b, (a.gcd b : ℝ)/(b : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [max_eq_right (Finset.mem_Ioc.mp ha).2]
    rw [he]
    exact lemma32_normalized_gcd_row (Finset.mem_Ioc.mp hb).1
  have hs := hu.trans (lemma32_divisor_summatory_log_bound A)
  calc
    _ ≤ _ := ht
    _ ≤ 2*((A : ℝ)*(1+Real.log (A : ℝ))) := mul_le_mul_of_nonneg_left hs (by norm_num)
    _ = _ := by ring

lemma lemma32_fin_multiplier_normalized_gcd_sum (A : ℕ) :
    (∑ a : Fin A, ∑ b : Fin A,
      ((a.val+1).gcd (b.val+1) : ℝ)/((max (a.val+1) (b.val+1) : ℕ) : ℝ)) ≤
      2*(A : ℝ)*(1+Real.log (A : ℝ)) := by
  calc
    _ = ∑ a : Fin A, ∑ b ∈ Ioc 0 A,
        ((a.val+1).gcd b : ℝ)/((max (a.val+1) b : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro a ha
      exact lemma32_fin_positive_sum A
        (fun b => ((a.val+1).gcd b : ℝ)/((max (a.val+1) b : ℕ) : ℝ))
    _ = ∑ a ∈ Ioc 0 A, ∑ b ∈ Ioc 0 A,
        (a.gcd b : ℝ)/((max a b : ℕ) : ℝ) :=
      lemma32_fin_positive_sum A
        (fun a => ∑ b ∈ Ioc 0 A, (a.gcd b : ℝ)/((max a b : ℕ) : ℝ))
    _ ≤ _ := lemma32_multiplier_normalized_gcd_sum A

end ZhangLS.Spec
