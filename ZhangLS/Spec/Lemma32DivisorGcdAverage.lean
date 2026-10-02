import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.NormNum
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma32_gcd_totient_divisor_sum {D : ℕ} (hD : 0 < D) (k : ℕ) :
    D.gcd k = ∑ d ∈ D.divisors, if d ∣ k then d.totient else 0 := by
  have hg : D.gcd k ≠ 0 := (Nat.gcd_pos_of_pos_left k hD).ne'
  have he : D.divisors.filter (fun d => d ∣ k) = (D.gcd k).divisors := by
    ext d
    simp [Nat.mem_divisors, Nat.dvd_gcd_iff, hD.ne', hg, and_assoc]
  rw [← Nat.sum_totient (D.gcd k), ← he, Finset.sum_filter]

lemma lemma32_gcd_interval_sum_le_divisors {D : ℕ} (hD : 0 < D) (H : ℕ) :
    (∑ k ∈ Finset.Ioc 0 H, D.gcd k) ≤ H * D.divisors.card := by
  simp_rw [lemma32_gcd_totient_divisor_sum hD]
  rw [Finset.sum_comm]
  calc
    _ = ∑ d ∈ D.divisors, (H/d)*d.totient := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ ∑ _d ∈ D.divisors, H := by
      apply Finset.sum_le_sum
      intro d hd
      exact (Nat.mul_le_mul_left (H/d) (Nat.totient_le d)).trans (Nat.div_mul_le_self H d)
    _ = H * D.divisors.card := by
      simp only [Finset.sum_const, nsmul_eq_mul, Nat.cast_id, Nat.mul_comm]

lemma lemma32_real_gcd_interval_sum_le_divisors {D : ℕ} (hD : 0 < D) (H : ℕ) :
    (∑ k ∈ Finset.Ioc 0 H, (D.gcd k : ℝ)) ≤ (H : ℝ) * D.divisors.card := by
  exact_mod_cast lemma32_gcd_interval_sum_le_divisors hD H

end ZhangLS.Spec
