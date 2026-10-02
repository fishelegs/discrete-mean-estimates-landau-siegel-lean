import ZhangLS.Spec.Lemma152LocalSeries
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

lemma lemma152_h2_norm_le (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖lemma83LocalH2 a b n‖ ≤ (n:ℝ)+1 := by
  unfold lemma83LocalH2 lemma83AddConvolution
  calc
    _ ≤ ∑ ij ∈ antidiagonal n, ‖a^ij.1*b^ij.2‖ := norm_sum_le _ _
    _ ≤ ∑ ij ∈ antidiagonal n, (1:ℝ) := by
      apply sum_le_sum
      intro ij hij
      rw [norm_mul,norm_pow,norm_pow]
      simpa only [one_mul] using mul_le_mul (pow_le_one₀ (norm_nonneg a) ha)
        (pow_le_one₀ (norm_nonneg b) hb) (pow_nonneg (norm_nonneg b) _) (by norm_num : (0:ℝ)≤1)
    _ = _ := by simp

lemma lemma152_local_kappa_norm_le (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (n : ℕ) :
    ‖lemma152LocalKappa a b n‖ ≤ 2*((n:ℝ)+1) := by
  cases n with
  | zero => norm_num
  | succ n =>
    rw [lemma152_local_kappa_succ]
    apply (norm_sub_le _ _).trans
    have h0 := lemma152_h2_norm_le a b ha hb n
    have h1 := lemma152_h2_norm_le a b ha hb (n+1)
    push_cast at *
    linarith

lemma lemma152_kappa_tail_majorant_hasSum (r : ℕ) :
    HasSum (fun k : ℕ => 2*((r:ℝ)+k+1)*(1/2:ℝ)^k) (4*r+8) := by
  have hg : HasSum (fun k : ℕ => (1/2:ℝ)^k) 2 := by
    convert hasSum_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1) using 1 <;> norm_num
  have hk : HasSum (fun k : ℕ => (k:ℝ)*(1/2:ℝ)^k) 2 := by
    convert hasSum_coe_mul_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1) using 1 <;> norm_num
  convert (hg.mul_left (2*((r:ℝ)+1))).add (hk.mul_left 2) using 1
  · funext k; ring
  · ring

lemma lemma152_local_kappa_tail_norm_le (a b t : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (ht : ‖t‖ ≤ 1/2) (r : ℕ) :
    ‖∑' k : ℕ, lemma152LocalKappa a b (r+k)*t^k‖ ≤ 8*((r:ℝ)+1) := by
  have hm := lemma152_kappa_tail_majorant_hasSum r
  have hbnd (k : ℕ) : ‖lemma152LocalKappa a b (r+k)*t^k‖ ≤
      2*((r:ℝ)+k+1)*(1/2:ℝ)^k := by
    rw [norm_mul,norm_pow]
    have hc := lemma152_local_kappa_norm_le a b ha hb (r+k)
    push_cast at hc
    exact mul_le_mul hc (pow_le_pow_left₀ (norm_nonneg t) ht k) (by positivity) (by positivity)
  have hs := hm.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hbnd
  calc
    _ ≤ ∑' k : ℕ, ‖lemma152LocalKappa a b (r+k)*t^k‖ := norm_tsum_le_tsum_norm hs
    _ ≤ 4*r+8 := by rw [← hm.tsum_eq]; exact hs.tsum_le_tsum hbnd hm.summable
    _ ≤ _ := by linarith [Nat.cast_nonneg (α := ℝ) r]

lemma lemma152_lambda_norm_le {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime) :
    ‖lemma152LambdaFactor χ β p 1‖ ≤ 5 := by
  have hu : ‖(p:ℂ)⁻¹‖ ≤ 1/2 := by
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ p by exact_mod_cast hp.two_le)
  have ht : ‖χ.evalNat p*(p:ℂ)⁻¹‖ ≤ 1/2 :=
    (by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)).trans hu)
  have hn (i : Fin 2) : ‖1-(p:ℂ)^(-β i)*(χ.evalNat p*(p:ℂ)⁻¹)‖ ≤ 3/2 := by
    apply (norm_sub_le _ _).trans
    rw [norm_one,norm_mul,lemma83_cpow_shift_norm hp.pos (β i) (hβ i),one_mul]
    linarith
  have hd : 1/2 ≤ ‖1-χ.evalNat p*(p:ℂ)⁻¹‖ := by
    have h := norm_sub_norm_le (1:ℂ) (χ.evalNat p*(p:ℂ)⁻¹)
    rw [norm_one] at h
    linarith
  rw [lemma152_lambda_factor_rational χ β hp.pos,norm_div,norm_mul]
  apply (div_le_div₀ (by positivity) (mul_le_mul (hn 0) (hn 1) (norm_nonneg _) (by norm_num))
    (by norm_num : (0:ℝ)<1/2) hd).trans
  norm_num

lemma lemma152_coefficient_prime_norm_le {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime) (e : ℕ) :
    ‖lemma152Coefficient χ β 1 1 (p^(e+1))‖ ≤ 64*((e:ℝ)+2) := by
  have hn (i : Fin 2) : ‖(p:ℂ)^(-β i)‖ ≤ 1 := (lemma83_cpow_shift_norm hp.pos (β i) (hβ i)).le
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
  have hk := lemma152_local_kappa_norm_le _ _ (hn 0) (hn 1) e
  have htail := lemma152_local_kappa_tail_norm_le _ _ _ (hn 0) (hn 1) ht (e+1)
  rw [lemma152_coefficient_prime_power χ β hp,lemma152_mobius_weight χ hp]
  simp only [lemma152_kappa_prime_power β hp,zpow_neg_one]
  rw [norm_mul]
  apply (mul_le_mul (lemma152_lambda_norm_le χ β hβ hp) (norm_sub_le _ _) (norm_nonneg _) (by norm_num)).trans
  rw [norm_mul]
  have hmul := mul_le_mul hA hk (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
  push_cast at htail
  nlinarith

/-- Uniform absolute convergence of each true local coefficient series. -/
lemma lemma152_coefficient_local_norm_series {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime)
    (x : ℂ) (hx : ‖x‖ ≤ 1/2) :
    Summable (fun e : ℕ => ‖lemma152Coefficient χ β 1 1 (p^e)*x^e‖) ∧
      (∑' e : ℕ, ‖lemma152Coefficient χ β 1 1 (p^e)*x^e‖) ≤ 1+384*‖x‖ := by
  have hm := (lemma152_kappa_tail_majorant_hasSum 1).mul_left (32*‖x‖)
  have hm' : HasSum (fun e : ℕ => 64*((e:ℝ)+2)*‖x‖*(1/2:ℝ)^e) (384*‖x‖) := by
    convert hm using 1
    · funext e; norm_num; ring
    · norm_num; ring
  have hb (e : ℕ) : ‖lemma152Coefficient χ β 1 1 (p^(e+1))*x^(e+1)‖ ≤
      64*((e:ℝ)+2)*‖x‖*(1/2:ℝ)^e := by
    rw [norm_mul,norm_pow,pow_succ]
    calc
      _ ≤ (64*((e:ℝ)+2))*((1/2:ℝ)^e*‖x‖) :=
        mul_le_mul (lemma152_coefficient_prime_norm_le χ β hβ hp e)
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg x) hx e) (norm_nonneg x))
          (by positivity) (by positivity)
      _ = _ := by ring
  have htail := hm'.summable.of_nonneg_of_le (fun _ => norm_nonneg _) hb
  have hs : Summable (fun e : ℕ => ‖lemma152Coefficient χ β 1 1 (p^e)*x^e‖) :=
    (summable_nat_add_iff 1).mp htail
  refine ⟨hs,?_⟩
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero,lemma152_coefficient_one,one_mul,norm_one]
  apply add_le_add le_rfl
  rw [← hm'.tsum_eq]
  exact htail.tsum_le_tsum hb hm'.summable

end ZhangLS.Spec
