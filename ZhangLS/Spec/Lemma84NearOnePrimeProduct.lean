import ZhangLS.Spec.Lemma84ArithmeticCircle
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Real
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma84_prime_rpow_sum_large (n : ℕ) (hn : 0 < n)
    (y σ : ℝ) (hy : 1 < y) (hσ : 0 ≤ σ) :
    (∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y), (p:ℝ)^(-σ)) ≤
      Real.log n/(y^σ*Real.log 2) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hyp : 0 < y^σ := Real.rpow_pos_of_pos (by linarith) _
  calc
    _ ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y),
        Real.log (p:ℝ)/(y^σ*Real.log 2) := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hprime := Nat.prime_of_mem_primeFactors hp'.1
      have hlog : Real.log 2 ≤ Real.log (p:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hprime.two_le)
      have hpy : y ≤ (p:ℝ) := (lt_of_not_ge hp'.2).le
      calc
        _ ≤ y^(-σ) := Real.rpow_le_rpow_of_nonpos (by linarith : 0 < y) hpy (by linarith)
        _ ≤ Real.log (p:ℝ)/(y^σ*Real.log 2) := by
          rw [Real.rpow_neg (by linarith : 0 ≤ y), inv_eq_one_div]
          apply (div_le_div_iff₀ hyp (mul_pos hyp hlog2)).mpr
          nlinarith only [mul_le_mul_of_nonneg_right hlog hyp.le]
    _ = (∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y), Real.log (p:ℝ))/(y^σ*Real.log 2) := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right (lemma83_prime_subset_log_le n hn _ (Finset.filter_subset _ _))
      (mul_nonneg hyp.le hlog2.le)

lemma lemma84_near_one_prime_product (n : ℕ) (hn : 0 < n)
    (y σ C : ℝ) (K : ℕ) (hy : 1 < y) (hσ : 0 ≤ σ) (hC : 0 ≤ C)
    (hK : 9*C ≤ (K:ℝ)) (hny : Real.log n ≤ y^σ)
    (hlocal : ∀ p ∈ n.primeFactors, (p:ℝ) ≤ y → (p:ℝ)^(1-σ) ≤ 3) :
    (∏ p ∈ n.primeFactors, (1+C*(p:ℝ)^(-σ))) ≤
      Real.exp (C/Real.log 2)*(1+Real.log y)^K := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hyp : 0 < y^σ := Real.rpow_pos_of_pos (by linarith) _
  have hsmall : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y), (1+C*(p:ℝ)^(-σ))) ≤
      (1+Real.log y)^K := by
    apply le_trans _ (lemma83_small_prime_product_le (n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y))
      (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
      y (3*C) K hy (by positivity) (by nlinarith only [hK]) (fun p hp => (Finset.mem_filter.mp hp).2))
    apply Finset.prod_le_prod (fun p hp => by positivity)
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    have hpp : 0 < (p:ℝ) := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp'.1).pos
    have he : (p:ℝ)^(-σ) = (p:ℝ)⁻¹*(p:ℝ)^(1-σ) := by
      rw [← Real.rpow_neg_one,← Real.rpow_add hpp]
      congr 1
      ring
    rw [he]
    have hh := mul_le_mul_of_nonneg_left (hlocal p hp'.1 hp'.2)
      (mul_nonneg hC (inv_nonneg.mpr hpp.le))
    simp only [div_eq_mul_inv]
    nlinarith only [hh]
  have hlarge : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y), (1+C*(p:ℝ)^(-σ))) ≤
      Real.exp (C/Real.log 2) := by
    calc
      _ ≤ ∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y), Real.exp (C*(p:ℝ)^(-σ)) := by
        apply Finset.prod_le_prod (fun p hp => by positivity)
        intro p hp
        have hh := Real.add_one_le_exp (C*(p:ℝ)^(-σ))
        linarith only [hh]
      _ = Real.exp (C*∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y), (p:ℝ)^(-σ)) := by
        simp only [←Real.exp_sum,Finset.mul_sum]
      _ ≤ _ := by
        apply Real.exp_le_exp.mpr
        have hs := mul_le_mul_of_nonneg_left (lemma84_prime_rpow_sum_large n hn y σ hy hσ) hC
        have hq : Real.log n/(y^σ*Real.log 2) ≤ 1/Real.log 2 := by
          apply (div_le_div_iff₀ (mul_pos hyp hlog2) hlog2).mpr
          nlinarith only [mul_le_mul_of_nonneg_right hny hlog2.le]
        have hh := hs.trans (mul_le_mul_of_nonneg_left hq hC)
        simpa only [mul_one_div] using hh
  rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p : ℕ => (p:ℝ) ≤ y)]
  have hh := mul_le_mul hsmall hlarge (Finset.prod_nonneg (fun p hp => by positivity))
    (pow_nonneg (by have hh := Real.log_nonneg hy.le; linarith) _)
  simpa only [mul_comm] using hh

/-- Uniform arithmetic growth on the actual near-one contour strip. -/
lemma lemma84_paper_near_one_prime_product (n : ℕ) (hn : 0 < n)
    (L σ C : ℝ) (K : ℕ) (hL : 2 ≤ L) (hlog : 20*Real.log L ≤ L)
    (hσ : 1-1/L ≤ σ) (hC : 0 ≤ C) (hK : 9*C ≤ (K:ℝ))
    (hnL : Real.log n ≤ L^9) :
    (∏ p ∈ n.primeFactors, (1+C*(p:ℝ)^(-σ))) ≤
      Real.exp (C/Real.log 2)*(1+20*Real.log L)^K := by
  have hLp : 0 < L := by linarith
  have hL1 : 1 < L := by linarith
  have hinv : 1/L ≤ (1:ℝ)/2 := one_div_le_one_div_of_le (by norm_num) hL
  have hσhalf : 1/2 ≤ σ := by linarith only [hσ,hinv]
  have hy : 1 < L^20 := one_lt_pow₀ hL1 (by norm_num)
  have hny : Real.log n ≤ (L^20)^σ := by
    apply hnL.trans
    calc
      _ ≤ L^10 := pow_le_pow_right₀ hL1.le (by norm_num)
      _ = L^(10:ℝ) := (Real.rpow_natCast L 10).symm
      _ ≤ L^(20*σ) := Real.rpow_le_rpow_of_exponent_le hL1.le (by linarith only [hσhalf])
      _ = _ := Real.rpow_natCast_mul hLp.le 20 σ
  have hh := lemma84_near_one_prime_product n hn (L^20) σ C K hy (by linarith only [hσhalf]) hC hK hny (by
    intro p hp hpy
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hpp : 0 < (p:ℝ) := by exact_mod_cast hpr.pos
    calc
      _ ≤ (p:ℝ)^(1/L) := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hpr.one_lt.le) (by linarith only [hσ])
      _ ≤ (L^20)^(1/L) := Real.rpow_le_rpow hpp.le hpy (by positivity)
      _ = Real.exp (20*Real.log L/L) := by rw [Real.rpow_def_of_pos (pow_pos hLp 20),Real.log_pow]; norm_num; congr 1 <;> ring
      _ ≤ Real.exp 1 := Real.exp_le_exp.mpr ((div_le_one hLp).mpr hlog)
      _ ≤ 3 := Real.exp_one_lt_three.le)
  simpa only [Real.log_pow,Nat.cast_ofNat] using hh

end ZhangLS.Spec
