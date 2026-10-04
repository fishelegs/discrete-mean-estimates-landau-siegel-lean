import ZhangLS.Spec.Lemma83
import ZhangLS.Spec.Lemma83FiniteShiftLambda
import ZhangLS.Spec.Lemma84WeightedArithmetic
import Mathlib.Analysis.SpecialFunctions.Log.Summable

/-! Relative perturbation of the literal Section 8 Λ factors. All primes,
including 2, are retained; denominator positivity is proved from primality. -/
set_option autoImplicit false
namespace ZhangLS.Spec.FixedHLambdaReplacement
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

lemma prime_baseline_pos {p : ℕ} (hp : p.Prime) :
    0 < 1 - (p : ℝ)⁻¹ ∧ 1/4 ≤ (1 - (p : ℝ)⁻¹)^2 := by
  have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hi : (p:ℝ)⁻¹ ≤ 1/2 := by
    simpa using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2) h2
  constructor <;> nlinarith

lemma prime_baseline_ne_zero {p : ℕ} (hp : p.Prime) :
    (1 - (p : ℂ)⁻¹)^2 ≠ 0 := by
  have h := (prime_baseline_pos hp).1.ne'
  have he : (1 - (p:ℂ)⁻¹)^2 = (((1 - (p:ℝ)⁻¹)^2 : ℝ) : ℂ) := by simp
  rw [he]
  exact_mod_cast pow_ne_zero 2 h

/-- The actual factor, normalized by its exact zero-shift value. -/
noncomputable def normalizedFactor (β : Fin 3 → ℂ) (j : Fin 3) (p : ℕ) : ℂ :=
  lemma83LambdaFactor β p (1 - β j) / (1 - (p:ℂ)⁻¹)^2

lemma normalizedFactor_error (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) (b : ℝ) (hb : 0 ≤ b)
    (hsmall : ∀ i, ‖β i‖ ≤ b) (j : Fin 3) {p : ℕ} (hp : p.Prime) :
    ‖normalizedFactor β j p - 1‖ ≤ 128*b*Real.log p/(p:ℝ) := by
  have he : normalizedFactor β j p - 1 =
      (lemma83LambdaFactor β p (1-β j) - (1-(p:ℂ)⁻¹)^2) /
        (1-(p:ℂ)⁻¹)^2 := by
    dsimp [normalizedFactor]
    exact div_sub_one (prime_baseline_ne_zero hp)
  rw [he,norm_div]
  have hd : ‖(1-(p:ℂ)⁻¹)^2‖ = (1-(p:ℝ)⁻¹)^2 := by
    rw [show (1-(p:ℂ)⁻¹)^2 = (((1-(p:ℝ)⁻¹)^2:ℝ):ℂ) by simp,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  rw [hd]
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  calc
    _ ≤ (32*b*Real.log p/(p:ℝ))/(1-(p:ℝ)⁻¹)^2 :=
      div_le_div_of_nonneg_right (lemma83_lambda_prime_small_shift β hβ b hb hsmall j hp)
        (sq_nonneg _)
    _ ≤ (32*b*Real.log p/(p:ℝ))/(1/4) :=
      div_le_div₀ (by positivity) le_rfl (by norm_num) (prime_baseline_pos hp).2
    _ = _ := by ring

lemma totient_baseline_product {n : ℕ} (hn : 0 < n) :
    (((Nat.totient n:ℝ)/(n:ℝ))^2 : ℂ) =
      ∏ p ∈ n.primeFactors, (1-(p:ℂ)⁻¹)^2 := by
  have ht : (Nat.totient n:ℝ)/(n:ℝ) = ∏ p ∈ n.primeFactors, (1-(p:ℝ)⁻¹) := by
    rw [lemma84_totient_real_product]
    field_simp [show (n:ℝ) ≠ 0 by exact_mod_cast hn.ne']
  norm_cast
  rw [ht,Finset.prod_pow]
  simp

lemma totient_baseline_ne_zero {n : ℕ} (hn : 0 < n) :
    (((Nat.totient n:ℝ)/(n:ℝ))^2 : ℂ) ≠ 0 := by
  rw [totient_baseline_product hn]
  exact prod_ne_zero_iff.mpr (fun p hp => prime_baseline_ne_zero (Nat.prime_of_mem_primeFactors hp))

lemma normalized_product (β : Fin 3 → ℂ) (j : Fin 3) {n : ℕ} (hn : 0 < n) :
    lemma83Lambda β n (1-β j) / (((Nat.totient n:ℝ)/(n:ℝ))^2 : ℂ) =
      ∏ p ∈ n.primeFactors, normalizedFactor β j p := by
  rw [lemma83Lambda,totient_baseline_product hn,← Finset.prod_div_distrib]
  rfl

/-- No approximation assumption: the full actual product is controlled by the
proved reciprocal-prime logarithmic sum, with positive n including n=1. -/
theorem relative_error_exp (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re=0)
    (b : ℝ) (hb : 0≤b) (hsmall : ∀ i, ‖β i‖≤b) (j : Fin 3)
    {n : ℕ} (hn : 0<n) {B : ℝ} (hB : 1<B) (hnB : Real.log n≤B) :
    ‖lemma83Lambda β n (1-β j) / (((Nat.totient n:ℝ)/(n:ℝ))^2 : ℂ) - 1‖ ≤
      Real.exp (128*b*(1+Real.log B)^2)-1 := by
  rw [normalized_product β j hn]
  have hh := n.primeFactors.norm_prod_one_add_sub_one_le (fun p => normalizedFactor β j p-1)
  simp only [add_sub_cancel] at hh
  apply hh.trans
  apply sub_le_sub_right
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ ∑ p ∈ n.primeFactors, 128*b*Real.log p/(p:ℝ) :=
      sum_le_sum (fun p hp => normalizedFactor_error β hβ b hb hsmall j (Nat.prime_of_mem_primeFactors hp))
    _ = 128*b*∑ p ∈ n.primeFactors, Real.log p/(p:ℝ) := by rw [mul_sum]; congr 1; ext p; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma83_prime_log_sum_uniform_le n hn B hB hnB) (by positivity)

end ZhangLS.Spec.FixedHLambdaReplacement
