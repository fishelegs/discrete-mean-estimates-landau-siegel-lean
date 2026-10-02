import ZhangLS.Spec.Lemma161LocalSeries
import ZhangLS.Spec.Lemma152LocalNorm
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

lemma lemma161_lambda_norm_le {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hp : p.Prime) :
    ‖lemma161LambdaFactor χ β p 1‖ ≤ 5 := by
  have hu : ‖(p:ℂ)⁻¹‖ ≤ 1/2 := by
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ p by exact_mod_cast hp.two_le)
  have ht : ‖χ.evalNat p*(p:ℂ)⁻¹‖ ≤ 1/2 :=
    (by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)).trans hu)
  have hn : ‖1-(p:ℂ)^(-β)*(χ.evalNat p*(p:ℂ)⁻¹)‖ ≤ 3/2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_one,norm_mul,lemma83_cpow_shift_norm hp.pos β hβ,one_mul]
    linarith
  have hd : 1/2 ≤ ‖1-χ.evalNat p*(p:ℂ)⁻¹‖ := by
    have h := norm_sub_norm_le (1:ℂ) (χ.evalNat p*(p:ℂ)⁻¹)
    rw [norm_one] at h
    linarith
  rw [lemma161_lambda_factor_rational χ β hp.pos,norm_div]
  apply (div_le_div₀ (by positivity) hn
    (by norm_num : (0:ℝ)<1/2) hd).trans
  norm_num

lemma lemma161_coefficient_prime_norm_le {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hp : p.Prime) (e : ℕ) :
    ‖lemma161Coefficient χ β 1 1 (p^(e+1))‖ ≤ 64*((e:ℝ)+2) := by
  have hn : ‖(p:ℂ)^(-β)‖ ≤ 1 := (lemma83_cpow_shift_norm hp.pos β hβ).le
  have hu : ‖(p:ℂ)⁻¹‖ ≤ 1/2 := by
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ p by exact_mod_cast hp.two_le)
  have ht : ‖χ.evalNat p*(p:ℂ)⁻¹‖ ≤ 1/2 :=
    (by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)).trans hu)
  have hd : 1/2 ≤ ‖1-(p:ℂ)⁻¹‖ := by
    have h := norm_sub_norm_le (1:ℂ) (p:ℂ)⁻¹
    rw [norm_one] at h
    linarith
  have hA : ‖χ.evalNat p/(1-(p:ℂ)⁻¹)‖ ≤ 2 := by
    rw [norm_div]
    calc
      _ ≤ 1/(1/2:ℝ) := div_le_div₀ (by norm_num) (χ.evalNat_norm_le_one p) (by norm_num) hd
      _ = 2 := by norm_num
  have hk := lemma152_local_kappa_norm_le _ 0 hn (by simp) e
  have htail := lemma152_local_kappa_tail_norm_le _ 0 _ hn (by simp) ht (e+1)
  rw [lemma161_coefficient_prime_power χ β hp,lemma161_mobius_weight χ hp]
  simp only [lemma161_kappa_prime_power β hp,zpow_neg_one]
  rw [norm_mul]
  apply (mul_le_mul (lemma161_lambda_norm_le χ β hβ hp) (norm_sub_le _ _) (norm_nonneg _) (by norm_num)).trans
  rw [norm_mul]
  have hmul := mul_le_mul hA hk (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
  push_cast at htail
  nlinarith

/-- Uniform absolute convergence of each true local coefficient series. -/
lemma lemma161_coefficient_local_norm_series {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hp : p.Prime)
    (x : ℂ) (hx : ‖x‖ ≤ 1/2) :
    Summable (fun e : ℕ => ‖lemma161Coefficient χ β 1 1 (p^e)*x^e‖) ∧
      (∑' e : ℕ, ‖lemma161Coefficient χ β 1 1 (p^e)*x^e‖) ≤ 1+384*‖x‖ := by
  have hm := (lemma152_kappa_tail_majorant_hasSum 1).mul_left (32*‖x‖)
  have hm' : HasSum (fun e : ℕ => 64*((e:ℝ)+2)*‖x‖*(1/2:ℝ)^e) (384*‖x‖) := by
    convert hm using 1
    · funext e; norm_num; ring
    · norm_num; ring
  have hb (e : ℕ) : ‖lemma161Coefficient χ β 1 1 (p^(e+1))*x^(e+1)‖ ≤
      64*((e:ℝ)+2)*‖x‖*(1/2:ℝ)^e := by
    rw [norm_mul,norm_pow,pow_succ]
    calc
      _ ≤ (64*((e:ℝ)+2))*((1/2:ℝ)^e*‖x‖) :=
        mul_le_mul (lemma161_coefficient_prime_norm_le χ β hβ hp e)
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hx e) (norm_nonneg x))
          (by positivity) (by positivity)
      _ = _ := by ring
  have htail := hm'.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hs : Summable (fun e : ℕ => ‖lemma161Coefficient χ β 1 1 (p^e)*x^e‖) :=
    (summable_nat_add_iff 1).mp htail
  refine ⟨hs,?_⟩
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero,lemma161_coefficient_one,one_mul,norm_one]
  apply add_le_add le_rfl
  rw [← hm'.tsum_eq]
  exact htail.tsum_le_tsum hb hm'.summable

end ZhangLS.Spec
