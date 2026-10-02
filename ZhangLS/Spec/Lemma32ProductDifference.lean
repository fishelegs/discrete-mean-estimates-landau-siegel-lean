import ZhangLS.Spec.Lemma32ProductBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_regular_finite_product_difference {D : ℕ} (χ : RealPrimitiveCharacter D)
    (σ : ℝ) (hσ : 1/2 < σ) (s : ℂ) (hs : σ ≤ s.re)
    (S T : Finset Nat.Primes) (hST : S ⊆ T) :
    ‖(∏ p ∈ T, lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s))-
      (∏ p ∈ S, lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s))‖ ≤
      lemma32RegularProductBound σ*
        (Real.exp (7659*∑ p ∈ T\S, (p.val : ℝ)^(-2*σ))-1) := by
  let f (p : Nat.Primes) : ℂ := lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s)
  have he : (∏ p ∈ T, f p)-(∏ p ∈ S, f p) =
      (∏ p ∈ S, f p)*((∏ p ∈ T\S, f p)-1) := by
    rw [← Finset.prod_sdiff hST]
    ring
  have ht := (T\S).norm_prod_one_add_sub_one_le (fun p => f p-1)
  simp only [add_sub_cancel] at ht
  have hsum : (∑ p ∈ T\S, ‖f p-1‖) ≤ 7659*∑ p ∈ T\S, (p.val : ℝ)^(-2*σ) := by
    calc
      _ ≤ ∑ p ∈ T\S, 7659*(p.val : ℝ)^(-2*σ) := Finset.sum_le_sum
        (fun p _ => lemma32_regular_prime_error_uniform χ σ hσ s hs p)
      _ = _ := (Finset.mul_sum _ _ _).symm
  have ht' := ht.trans (sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1)
  change ‖(∏ p ∈ T, f p)-(∏ p ∈ S, f p)‖ ≤ _
  rw [he,norm_mul]
  exact mul_le_mul (lemma32_regular_finite_product_bound χ σ hσ s hs S) ht'
    (norm_nonneg _) (lemma32_regular_product_bound_pos σ).le

end ZhangLS.Spec
