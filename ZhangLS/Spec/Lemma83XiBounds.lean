import ZhangLS.Spec.Lemma83KappaBounds
import ZhangLS.Spec.Lemma83XiMultiplicative
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 600000

lemma lemma83_kappa_tail_norm_bound (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    {p : ℕ} (hp : p.Prime) (e : ℕ) (t : ℂ) (ht : ‖t‖ ≤ 1/2) :
    ‖∑' k : ℕ, lemma83Kappa β (p^(e+k))*t^k‖ ≤ 672*(4/3:ℝ)^e := by
  have hg : HasSum (fun k : ℕ => (224*(4/3:ℝ)^e)*(2/3:ℝ)^k) (672*(4/3:ℝ)^e) := by
    convert (hasSum_geometric_of_norm_lt_one (by norm_num : ‖(2/3:ℝ)‖ < 1)).mul_left
      (224*(4/3:ℝ)^e) using 1 <;> ring
  have hb (k : ℕ) : ‖lemma83Kappa β (p^(e+k))*t^k‖ ≤
      (224*(4/3:ℝ)^e)*(2/3:ℝ)^k := by
    rw [norm_mul,norm_pow]
    calc
      _ ≤ (224*(4/3:ℝ)^(e+k))*(1/2:ℝ)^k := mul_le_mul
        (lemma83_kappa_prime_power_norm_exponential β hβ hp _)
        (pow_le_pow_left₀ (norm_nonneg _) ht _) (pow_nonneg (norm_nonneg _) _) (by positivity)
      _ = _ := by rw [pow_add,show (2/3:ℝ) = (4/3)*(1/2) by norm_num,mul_pow]; ring
  have hn : Summable (fun k : ℕ => ‖lemma83Kappa β (p^(e+k))*t^k‖) :=
    hg.summable.of_nonneg_of_le (fun k => norm_nonneg _) hb
  exact hn.of_norm.hasSum.norm_le_of_bounded hg hb

lemma lemma83_prime_reciprocal_norm_le_half {p : ℕ} (hp : p.Prime) :
    ‖(p:ℂ)⁻¹‖ ≤ 1/2 := by
  rw [norm_inv,Complex.norm_natCast]
  simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
    (show (2:ℝ) ≤ p by exact_mod_cast hp.two_le)

lemma lemma83_one_sub_norm_ge_half {t : ℂ} (ht : ‖t‖ ≤ 1/2) : 1/2 ≤ ‖1-t‖ := by
  have hh := norm_sub_norm_le (1:ℂ) t
  norm_num only [norm_one] at hh
  linarith

lemma lemma83_tail_parameter_norm_le_half (β : ℂ) (hβ : β.re = 0)
    {p : ℕ} (hp : p.Prime) : ‖(p:ℂ)^(-(1-β))‖ ≤ 1/2 := by
  rw [lemma83_cpow_tail_norm hp.pos β hβ]
  simpa only [norm_inv,Complex.norm_natCast] using lemma83_prime_reciprocal_norm_le_half hp

lemma lemma83_lambda_prime_norm_bound (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (j : Fin 3) {p : ℕ} (hp : p.Prime) :
    ‖lemma83LambdaFactor β p (1-β j)‖ ≤ 7 := by
  let t : ℂ := (p:ℂ)^(-(1-β j))
  have ht : ‖t‖ ≤ 1/2 := lemma83_tail_parameter_norm_le_half (β j) (hβ j) hp
  have hden := lemma83_one_sub_norm_ge_half ht
  have hb (i : Fin 3) : ‖1-(p:ℂ)^(-β i)*t‖ ≤ 3/2 := by
    have hh := norm_sub_le (1:ℂ) ((p:ℂ)^(-β i)*t)
    rw [norm_one,norm_mul,lemma83_cpow_shift_norm hp.pos (β i) (hβ i),one_mul] at hh
    linarith
  rw [lemma83_lambda_factor_inverse β hp.pos]
  change ‖(lemma83ActualKappaRational β p t)⁻¹‖ ≤ 7
  rw [lemma83ActualKappaRational,lemma83KappaRational,inv_div,norm_div,norm_mul,norm_mul]
  have hnum : ‖1-(p:ℂ)^(-β 0)*t‖*‖1-(p:ℂ)^(-β 1)*t‖*‖1-(p:ℂ)^(-β 2)*t‖ ≤ (3/2:ℝ)^3 := by
    calc
      _ ≤ (3/2:ℝ)*(3/2)*(3/2) := mul_le_mul
        (mul_le_mul (hb 0) (hb 1) (norm_nonneg _) (by norm_num)) (hb 2)
        (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  have hh := div_le_div₀ (by positivity) hnum (by norm_num : (0:ℝ)<1/2) hden
  norm_num at hh
  linarith

lemma lemma83_prime_mobius_weight_norm_bound (β : ℂ) (hβ : β.re = 0)
    {p : ℕ} (hp : p.Prime) : ‖(p:ℂ)^(1-β)/(p-1:ℕ)‖ ≤ 2 := by
  rw [lemma83_prime_mobius_weight β hp,norm_div,lemma83_cpow_shift_norm hp.pos β hβ]
  have hh := lemma83_one_sub_norm_ge_half (lemma83_prime_reciprocal_norm_le_half hp)
  have hd := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/2) hh
  norm_num at hd
  simpa only [one_div] using hd

lemma lemma83_modified_kappa_prime_norm_bound (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (j : Fin 3) {p : ℕ} (hp : p.Prime) (e m : ℕ) :
    ‖lemma83ModifiedKappa β (p^(e+1)) m (1-β j)‖ ≤ 672*(4/3:ℝ)^(e+1) := by
  by_cases hpm : p ∣ m
  · rw [lemma83_modified_kappa_prime_power_excluded β hp hpm]
    exact (lemma83_kappa_prime_power_norm_exponential β hβ hp _).trans
      (by nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 4/3) (e+1)])
  · rw [lemma83_modified_kappa_prime_power_unexcluded β hp hpm]
    exact lemma83_kappa_tail_norm_bound β hβ hp (e+1) _
      (lemma83_tail_parameter_norm_le_half (β j) (hβ j) hp)

lemma lemma83_xi_prime_power_norm_bound (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0)
    (j : Fin 3) {p : ℕ} (hp : p.Prime) (e d r : ℕ) :
    ‖lemma83Xi β j (p^(e+1)) d r‖ ≤ 10000*(4/3:ℝ)^(e+1) := by
  have hl : ‖lemma83ModifiedLambda β j (p^(e+1)) (d*r)‖ ≤ 7 := by
    rw [lemma83_modified_lambda_prime_power β j hp]
    split_ifs
    · norm_num
    · exact lemma83_lambda_prime_norm_bound β hβ j hp
  have hk := lemma83_modified_kappa_prime_norm_bound β hβ j hp e (d*r)
  have hcorr : ‖if p.Coprime r then lemma83Kappa β (p^e) *
      (p:ℂ)^(1-β j)/(p-1:ℕ) else 0‖ ≤ 448*(4/3:ℝ)^(e+1) := by
    split_ifs
    · rw [mul_div_assoc,norm_mul]
      have hh := mul_le_mul (lemma83_kappa_prime_power_norm_exponential β hβ hp e)
        (lemma83_prime_mobius_weight_norm_bound (β j) (hβ j) hp) (norm_nonneg _) (by positivity)
      rw [pow_succ]
      nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 4/3) e]
    · simp only [norm_zero]
      positivity
  rw [lemma83_xi_prime_power β j hp,norm_mul]
  have hsum := (norm_sub_le (lemma83ModifiedKappa β (p^(e+1)) (d*r) (1-β j))
    (if p.Coprime r then lemma83Kappa β (p^e)*(p:ℂ)^(1-β j)/(p-1:ℕ) else 0)).trans
      (add_le_add hk hcorr)
  have hh := mul_le_mul hl hsum (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 7)
  nlinarith [pow_nonneg (by norm_num : (0:ℝ) ≤ 4/3) (e+1)]

end ZhangLS.Spec
