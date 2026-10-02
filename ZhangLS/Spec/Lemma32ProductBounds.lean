import ZhangLS.Spec.Lemma32ProductConvergence
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32RegularProductBound (σ : ℝ) : ℝ :=
  Real.exp (7659*∑' p : Nat.Primes, (p.val : ℝ)^(-2*σ))

lemma lemma32_regular_prime_error_uniform {D : ℕ} (χ : RealPrimitiveCharacter D)
    (σ : ℝ) (hσ : 1/2 < σ) (s : ℂ) (hs : σ ≤ s.re) (p : Nat.Primes) :
    ‖lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s)-1‖ ≤
      7659*(p.val : ℝ)^(-2*σ) := by
  have hm := lemma32_prime_monomial_norm_lt_one p.property.one_lt s (by linarith)
  have hb := lemma32_regular_local_norm_sub_one χ p.val (lemma32PrimeMonomial p.val s) hm.le
  rw [lemma32_prime_monomial_norm_square p.property.pos] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast p.property.one_lt.le) (by linarith))
    (by norm_num))

lemma lemma32_regular_finite_product_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (σ : ℝ) (hσ : 1/2 < σ) (s : ℂ) (hs : σ ≤ s.re) (S : Finset Nat.Primes) :
    ‖∏ p ∈ S, lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s)‖ ≤
      lemma32RegularProductBound σ := by
  let f (p : Nat.Primes) : ℂ := lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s)
  have hh := S.norm_prod_one_add_sub_one_le (fun p => f p-1)
  simp only [add_sub_cancel] at hh
  have hn : Summable (fun n : ℕ => (n : ℝ)^(-2*σ)) := Real.summable_nat_rpow.mpr (by linarith)
  have hp : Summable (fun p : Nat.Primes => (p.val : ℝ)^(-2*σ)) := hn.subtype _
  have hsum : (∑ p ∈ S, ‖f p-1‖) ≤ 7659*∑' p : Nat.Primes, (p.val : ℝ)^(-2*σ) := by
    calc
      _ ≤ ∑ p ∈ S, 7659*(p.val : ℝ)^(-2*σ) :=
        Finset.sum_le_sum (fun p _ => lemma32_regular_prime_error_uniform χ σ hσ s hs p)
      _ = 7659*∑ p ∈ S, (p.val : ℝ)^(-2*σ) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hp.sum_le_tsum S (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by norm_num)
  have hnorm := norm_le_norm_sub_add (∏ p ∈ S, f p) (1 : ℂ)
  norm_num only [norm_one] at hnorm
  calc
    _ ≤ Real.exp (∑ p ∈ S, ‖f p-1‖) := by dsimp [f] at *; linarith
    _ ≤ _ := Real.exp_le_exp.mpr hsum

lemma lemma32_regular_euler_product_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (σ : ℝ) (hσ : 1/2 < σ) (s : ℂ) (hs : σ ≤ s.re) :
    ‖lemma32RegularEulerProduct χ s‖ ≤ lemma32RegularProductBound σ := by
  have hm := lemma32_regular_euler_product_multipliable χ s (by linarith)
  have ht : Tendsto (fun S : Finset Nat.Primes =>
      ∏ p ∈ S, lemma32RegularLocalPolynomial χ p.val (lemma32PrimeMonomial p.val s))
      atTop (𝓝 (lemma32RegularEulerProduct χ s)) := hm.hasProd
  apply le_of_tendsto ht.norm
  filter_upwards with S
  exact lemma32_regular_finite_product_bound χ σ hσ s hs S

lemma lemma32_regular_product_bound_pos (σ : ℝ) : 0 < lemma32RegularProductBound σ :=
  Real.exp_pos _

end ZhangLS.Spec
