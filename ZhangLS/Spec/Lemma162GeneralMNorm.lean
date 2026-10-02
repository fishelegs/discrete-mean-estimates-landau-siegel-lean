import ZhangLS.Spec.Lemma162ActualMLocal
import ZhangLS.Spec.Lemma161LocalNorm
import ZhangLS.Spec.Lemma161CoefficientMultiplicative
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

/-- Uniform prime-power norm bound for the original M₂(d,l) coefficients,
including every divisibility pattern. -/
lemma lemma162_general_m_prime_norm_le {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hp : p.Prime) (d l e : ℕ) :
    ‖lemma161Coefficient χ β d l (p^(e+1))‖ ≤ 64*((e:ℝ)+2) := by
  have hn : ‖(p:ℂ)^(-β)‖ ≤ 1 := (lemma83_cpow_shift_norm hp.pos β hβ).le
  have hu : ‖(p:ℂ)⁻¹‖ ≤ 1/2 := by
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ p by exact_mod_cast hp.two_le)
  have ht : ‖χ.evalNat p*(p:ℂ)⁻¹‖ ≤ 1/2 := by
    rw [norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)).trans hu
  have hd : 1/2 ≤ ‖1-(p:ℂ)⁻¹‖ := by
    have h := norm_sub_norm_le (1:ℂ) (p:ℂ)⁻¹
    rw [norm_one] at h
    linarith
  have hA : ‖χ.evalNat p/(1-(p:ℂ)⁻¹)‖ ≤ 2 := by
    rw [norm_div]
    exact (div_le_div₀ (by norm_num) (χ.evalNat_norm_le_one p) (by norm_num : (0:ℝ)<1/2) hd).trans (by norm_num)
  have hk := lemma152_local_kappa_norm_le _ 0 hn (by simp) e
  have hmod : ‖lemma161ModifiedKappa χ β (p^(e+1)) d 1‖ ≤ 8*((e:ℝ)+2) := by
    by_cases hpd : p ∣ d
    · rw [lemma161_modified_kappa_prime_power_excluded χ β hp hpd,
        lemma161_kappa_prime_power β hp]
      have hh := lemma152_local_kappa_norm_le _ 0 hn (by simp) (e+1)
      push_cast at hh
      nlinarith only [hh,Nat.cast_nonneg (α := ℝ) e]
    · rw [lemma161_modified_kappa_prime_power_unexcluded χ β hp hpd]
      simp_rw [lemma161_kappa_prime_power β hp,Complex.cpow_neg_one]
      have hh := lemma152_local_kappa_tail_norm_le _ 0 _ hn (by simp) ht (e+1)
      simpa only [Nat.cast_add,Nat.cast_one,add_assoc,one_add_one_eq_two] using hh
  have hlambda : ‖lemma161ModifiedLambda χ β (p^(e+1)) d‖ ≤ 5 := by
    rw [lemma161_modified_lambda_prime_power χ β hp]
    split_ifs
    · norm_num
    · exact lemma161_lambda_norm_le χ β hβ hp
  have hcorr : ‖if p.Coprime l then χ.evalNat p/(1-(p:ℂ)⁻¹)*lemma161Kappa β (p^e) else 0‖ ≤
      4*((e:ℝ)+1) := by
    split_ifs
    · rw [norm_mul,lemma161_kappa_prime_power β hp]
      have hh := mul_le_mul hA hk (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
      linarith
    · simp
      positivity
  rw [lemma161Coefficient,norm_mul,lemma161_xi_prime_power χ β hp,
    lemma161_mobius_weight χ hp]
  apply (mul_le_mul hlambda (norm_sub_le _ _) (norm_nonneg _) (by norm_num : (0:ℝ)≤5)).trans
  nlinarith only [hmod,hcorr,Nat.cast_nonneg (α := ℝ) e]

/-- Uniform absolute convergence of each true local coefficient series. -/
lemma lemma162_general_m_local_norm_series {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hp : p.Prime)
    (d l : ℕ) (x : ℂ) (hx : ‖x‖ ≤ 1/2) :
    Summable (fun e : ℕ => ‖lemma161Coefficient χ β d l (p^e)*x^e‖) ∧
      (∑' e : ℕ, ‖lemma161Coefficient χ β d l (p^e)*x^e‖) ≤ 1+384*‖x‖ := by
  have hm := (lemma152_kappa_tail_majorant_hasSum 1).mul_left (32*‖x‖)
  have hm' : HasSum (fun e : ℕ => 64*((e:ℝ)+2)*‖x‖*(1/2:ℝ)^e) (384*‖x‖) := by
    convert hm using 1
    · funext e; norm_num; ring
    · norm_num; ring
  have hb (e : ℕ) : ‖lemma161Coefficient χ β d l (p^(e+1))*x^(e+1)‖ ≤
      64*((e:ℝ)+2)*‖x‖*(1/2:ℝ)^e := by
    rw [norm_mul,norm_pow,pow_succ]
    calc
      _ ≤ (64*((e:ℝ)+2))*((1/2:ℝ)^e*‖x‖) :=
        mul_le_mul (lemma162_general_m_prime_norm_le χ β hβ hp d l e)
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hx e) (norm_nonneg x))
          (by positivity) (by positivity)
      _ = _ := by ring
  have htail := hm'.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hs : Summable (fun e : ℕ => ‖lemma161Coefficient χ β d l (p^e)*x^e‖) :=
    (summable_nat_add_iff 1).mp htail
  refine ⟨hs,?_⟩
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero,lemma161_coefficient_one,one_mul,norm_one]
  apply add_le_add le_rfl
  rw [← hm'.tsum_eq]
  exact htail.tsum_le_tsum hb hm'.summable

end ZhangLS.Spec
