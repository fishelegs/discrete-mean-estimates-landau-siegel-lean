import ZhangLS.Spec.Lemma83LocalAgreement
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 500000

lemma lemma83_local_h2_norm_bound (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖lemma83LocalH2 a b n‖ ≤ (n+1:ℝ) := by
  unfold lemma83LocalH2 lemma83AddConvolution
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ ij ∈ antidiagonal n, (1:ℝ) := by
      apply sum_le_sum
      intro ij hij
      rw [norm_mul,norm_pow,norm_pow]
      exact mul_le_one₀ (pow_le_one₀ (norm_nonneg a) ha) (pow_nonneg (norm_nonneg b) _)
        (pow_le_one₀ (norm_nonneg b) hb)
    _ = _ := by simp

lemma lemma83_local_h3_norm_bound (a b c : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    ‖lemma83LocalH3 a b c n‖ ≤ (n+1:ℝ)^2 := by
  unfold lemma83LocalH3 lemma83AddConvolution
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ ij ∈ antidiagonal n, (n+1:ℝ) := by
      apply sum_le_sum
      intro ij hij
      rw [norm_mul,norm_pow]
      have hi : ij.1 ≤ n := by have := mem_antidiagonal.mp hij; omega
      calc
        _ ≤ (ij.1+1:ℝ)*1 := mul_le_mul
          (lemma83_local_h2_norm_bound a b ha hb _) (pow_le_one₀ (norm_nonneg c) hc)
          (pow_nonneg (norm_nonneg c) _) (by positivity)
        _ ≤ _ := by
          have hir : (ij.1:ℝ) ≤ n := by exact_mod_cast hi
          linarith
    _ = _ := by simp; ring

lemma lemma83_local_kappa_norm_polynomial (a b c : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    ‖lemma83LocalKappa a b c n‖ ≤ 2*(n+1:ℝ)^2 := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [lemma83_local_kappa_succ]
    have h1 := lemma83_local_h3_norm_bound a b c ha hb hc (n+1)
    have h0 := lemma83_local_h3_norm_bound a b c ha hb hc n
    have ht := norm_sub_le (lemma83LocalH3 a b c (n+1)) (lemma83LocalH3 a b c n)
    push_cast at *
    nlinarith [Nat.cast_nonneg (α := ℝ) n]

lemma lemma83_quadratic_geometric_bound (n : ℕ) :
    (n+1:ℝ)^2*(3/4:ℝ)^n ≤ 112 := by
  have hs : HasSum (fun k : ℕ => (k+1:ℂ)^2*(3/4:ℂ)^k) 112 := by
    convert lemma32_square_geometric_hasSum (3/4:ℂ) (by norm_num) using 1 <;> norm_num
  have hr : HasSum (fun k : ℕ => (k+1:ℝ)^2*(3/4:ℝ)^k) 112 := by
    apply Complex.hasSum_ofReal.mp
    convert hs using 1
    funext k
    push_cast
    rfl
  have ht := hr.summable.le_tsum n (fun k _ => by positivity)
  rwa [hr.tsum_eq] at ht

lemma lemma83_local_kappa_norm_exponential (a b c : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    ‖lemma83LocalKappa a b c n‖ ≤ 224*(4/3:ℝ)^n := by
  have hp := lemma83_local_kappa_norm_polynomial a b c ha hb hc n
  have hq := lemma83_quadratic_geometric_bound n
  have hpow : (3/4:ℝ)^n*(4/3:ℝ)^n = 1 := by rw [← mul_pow]; norm_num
  have hh := mul_le_mul_of_nonneg_right hq (pow_nonneg (by norm_num : (0:ℝ) ≤ 4/3) n)
  nlinarith

lemma lemma83_kappa_prime_power_norm_exponential (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ‖lemma83Kappa β (p^n)‖ ≤ 224*(4/3:ℝ)^n := by
  rw [lemma83_kappa_prime_power β hp]
  apply lemma83_local_kappa_norm_exponential <;>
    exact (lemma83_cpow_shift_norm hp.pos _ (hβ _)).le

end ZhangLS.Spec
