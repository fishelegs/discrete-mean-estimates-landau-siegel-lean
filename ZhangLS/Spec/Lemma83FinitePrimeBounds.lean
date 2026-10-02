import ZhangLS.Spec.Lemma32RamificationPowerSaving
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.Harmonic.Bounds

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ZhangLS.Spec
open Finset Real Set
open scoped Classical

/-- Elementary upper bound for the positive, genuinely convergent p-series. -/
lemma lemma83_rpow_tsum_le (δ : ℝ) (hδ : 0 < δ) :
    (∑' m : ℕ, (m : ℝ)^(-(1+δ))) ≤ 1 + δ⁻¹ := by
  have hs : Summable (fun m : ℕ => (m : ℝ)^(-(1+δ))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have ht : Summable (fun m : ℕ => ((m+1+1 : ℕ) : ℝ)^(-(1+δ))) := by
    simpa [Nat.add_assoc] using (summable_nat_add_iff 2).mpr hs
  have hb : (∑' m : ℕ, ((m+1+1 : ℕ) : ℝ)^(-(1+δ))) ≤ δ⁻¹ := by
    apply ht.tsum_le_of_sum_range_le
    intro N
    have hanti : AntitoneOn (fun x : ℝ => x^(-(1+δ))) (Set.Icc 1 (1+N)) := by
      intro a ha b hb hab
      exact Real.rpow_le_rpow_of_nonpos (by linarith [ha.1]) hab (by linarith)
    have hi := hanti.sum_le_integral (a := N)
    have hint : (∫ x : ℝ in 1..1+N, x^(-(1+δ))) =
        ((1+(N:ℝ))^(-δ) - 1)/(-δ) := by
      rw [integral_rpow (Or.inr ⟨by linarith, by
        rw [Set.uIcc_of_le (by linarith [Nat.cast_nonneg (α := ℝ) N] : (1:ℝ) ≤ 1+N)]
        simp only [Set.mem_Icc, not_and_or]
        left; norm_num⟩)]
      congr 1 <;> simp
    rw [hint] at hi
    have he : ((1+(N:ℝ))^(-δ) - 1)/(-δ) ≤ δ⁻¹ := by
      rw [div_neg, ← neg_div, neg_sub, inv_eq_one_div]
      exact div_le_div_of_nonneg_right (by linarith [Real.rpow_nonneg (show 0 ≤ 1+(N:ℝ) by positivity) (-δ)]) hδ.le
    refine le_trans ?_ (hi.trans he)
    apply Finset.sum_le_sum
    intro m hm
    have hh : (((m+1+1 : ℕ) : ℝ)) = 1 + ↑(m+1) := by push_cast; ring
    rw [hh]
  rw [hs.tsum_eq_zero_add]
  have hs1 : Summable (fun m : ℕ => ((m+1 : ℕ) : ℝ)^(-(1+δ))) :=
    (summable_nat_add_iff 1).mpr hs
  rw [hs1.tsum_eq_zero_add]
  simp only [Nat.cast_zero, Nat.cast_one, Real.zero_rpow (by linarith : -(1+δ) ≠ 0), Real.one_rpow, zero_add]
  linarith [hb]

/-- A finite positive Euler product is bounded by its full convergent series. -/
lemma lemma83_finite_euler_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (δ : ℝ) (hδ : 0 < δ) :
    (∏ p ∈ S, (1-(p:ℝ)^(-(1+δ)))⁻¹) ≤ 1 + δ⁻¹ := by
  let f : ℕ →* ℝ :=
    { toFun := fun m => (m:ℝ)^(-(1+δ))
      map_one' := by simp
      map_mul' := by intro a b; simp [Real.mul_rpow (Nat.cast_nonneg a) (Nat.cast_nonneg b)] }
  have hs : Summable f := Real.summable_nat_rpow.mpr (by linarith)
  have he := EulerProduct.prod_filter_prime_geometric_eq_tsum_factoredNumbers hs S
  have hf : S.filter Nat.Prime = S := Finset.filter_eq_self.mpr hS
  rw [hf] at he
  calc
    _ = ∑' m : Nat.factoredNumbers S, f m := he
    _ ≤ ∑' m : ℕ, f m := Summable.tsum_subtype_le _ _ (fun m => Real.rpow_nonneg (Nat.cast_nonneg _) _) hs
    _ ≤ _ := lemma83_rpow_tsum_le δ hδ

/-- Elementary Rankin comparison at one prime. -/
lemma lemma83_rankin_factor_le {p C δ : ℝ} {K : ℕ}
    (hp : 1 < p) (hC : 0 ≤ C) (hδ : 0 < δ)
    (hpδ : p^δ ≤ 3) (hK : 3*C ≤ (K:ℝ)) :
    1 + C/p ≤ ((1-p^(-(1+δ)))⁻¹)^K := by
  have ha : 0 ≤ p^(-(1+δ)) := Real.rpow_nonneg (by linarith : 0 ≤ p) _
  have ha1 : p^(-(1+δ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hp (by linarith)
  have hid : p^(-(1+δ))*p^δ = p⁻¹ := by
    rw [← Real.rpow_add (by linarith : 0 < p)]
    rw [show -(1+δ)+δ = -1 by ring, Real.rpow_neg_one]
  have hmul : C/p ≤ (K:ℝ)*p^(-(1+δ)) := by
    calc
      C/p = C*(p^(-(1+δ))*p^δ) := by rw [hid,div_eq_mul_inv]
      _ ≤ C*(p^(-(1+δ))*3) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hpδ ha) hC
      _ = (3*C)*p^(-(1+δ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hK ha
  have hbase : 1+p^(-(1+δ)) ≤ (1-p^(-(1+δ)))⁻¹ := by
    rw [inv_eq_one_div, le_div_iff₀ (by linarith : 0 < 1-p^(-(1+δ)))]
    nlinarith [sq_nonneg (p^(-(1+δ)))]
  apply le_trans (show 1+C/p ≤ 1+(K:ℝ)*p^(-(1+δ)) by linarith)
  exact ((one_add_mul_le_pow (by linarith : -2 ≤ p^(-(1+δ))) K).trans
      (pow_le_pow_left₀ (by positivity) hbase K))

/-- Prime products below a cutoff have a polylogarithmic upper bound. -/
lemma lemma83_small_prime_product_le (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) (y C : ℝ) (K : ℕ)
    (hy : 1 < y) (hC : 0 ≤ C) (hK : 3*C ≤ (K:ℝ))
    (hcut : ∀ p ∈ S, (p:ℝ) ≤ y) :
    (∏ p ∈ S, (1+C/(p:ℝ))) ≤ (1+Real.log y)^K := by
  have hlog : 0 < Real.log y := Real.log_pos hy
  have hδ : 0 < (Real.log y)⁻¹ := inv_pos.mpr hlog
  have hpδ (p : ℕ) (hp : p ∈ S) : (p:ℝ)^((Real.log y)⁻¹) ≤ 3 := by
    have hp0 : 0 < (p:ℝ) := Nat.cast_pos.mpr (hS p hp).pos
    calc
      _ ≤ y^((Real.log y)⁻¹) := Real.rpow_le_rpow hp0.le (hcut p hp) hδ.le
      _ = Real.exp 1 := by rw [Real.rpow_def_of_pos (by linarith : 0 < y), mul_inv_cancel₀ hlog.ne']
      _ ≤ 3 := Real.exp_one_lt_three.le
  calc
    _ ≤ ∏ p ∈ S, ((1-(p:ℝ)^(-(1+(Real.log y)⁻¹)))⁻¹)^K := by
      apply Finset.prod_le_prod
      · intro p hp; exact add_nonneg (by norm_num) (div_nonneg hC (Nat.cast_nonneg p))
      · intro p hp
        exact lemma83_rankin_factor_le (by exact_mod_cast (hS p hp).one_lt) hC hδ (hpδ p hp) hK
    _ = (∏ p ∈ S, (1-(p:ℝ)^(-(1+(Real.log y)⁻¹)))⁻¹)^K := Finset.prod_pow _ _ _
    _ ≤ (1+((Real.log y)⁻¹)⁻¹)^K := by
      apply pow_le_pow_left₀ _ (lemma83_finite_euler_le S hS _ hδ)
      apply Finset.prod_nonneg
      intro p hp
      apply inv_nonneg.mpr
      have hlt := Real.rpow_lt_one_of_one_lt_of_neg
        (show 1 < (p:ℝ) by exact_mod_cast (hS p hp).one_lt)
        (show -(1+(Real.log y)⁻¹) < 0 by linarith)
      linarith
    _ = _ := by rw [inv_inv]

lemma lemma83_prime_subset_log_le (n : ℕ) (hn : 0 < n) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) :
    (∑ p ∈ S, Real.log (p:ℝ)) ≤ Real.log n := by
  apply le_trans _ (lemma32_prime_factors_log_sum_bound n hn)
  apply Finset.sum_le_sum_of_subset_of_nonneg hS
  intro p hp hnot
  exact Real.log_nonneg (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt.le)

/-- Large prime divisors have small logarithm-weighted reciprocal sum. -/
lemma lemma83_large_prime_log_sum_le (n : ℕ) (hn : 0 < n)
    (y : ℝ) (hy : 0 < y) :
    (∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y), Real.log (p:ℝ)/(p:ℝ)) ≤
      Real.log n / y := by
  calc
    _ ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y), Real.log (p:ℝ)/y := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpr := Nat.prime_of_mem_primeFactors hp'.1
      exact div_le_div_of_nonneg_left
        (Real.log_nonneg (by exact_mod_cast hpr.one_lt.le)) hy (le_of_not_ge hp'.2)
    _ = (∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y), Real.log (p:ℝ))/y := by rw [Finset.sum_div]
    _ ≤ _ := div_le_div_of_nonneg_right
      (lemma83_prime_subset_log_le n hn _ (Finset.filter_subset _ _)) hy.le

/-- The reciprocal sum over large prime divisors uses only the product of those primes. -/
lemma lemma83_large_prime_inv_sum_le (n : ℕ) (hn : 0 < n)
    (y : ℝ) (hy : 0 < y) :
    (∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y), (p:ℝ)⁻¹) ≤
      Real.log n / (y * Real.log 2) := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y),
        (Real.log (p:ℝ)/(p:ℝ))/Real.log 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1
      have hp0 : 0 < (p:ℝ) := Nat.cast_pos.mpr hpr.pos
      have hl : Real.log 2 ≤ Real.log (p:ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hpr.two_le)
      rw [le_div_iff₀ h2, div_eq_mul_inv]
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hl (inv_nonneg.mpr hp0.le)
    _ = (∑ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y),
        Real.log (p:ℝ)/(p:ℝ))/Real.log 2 := by rw [Finset.sum_div]
    _ ≤ (Real.log n/y)/Real.log 2 := div_le_div_of_nonneg_right
      (lemma83_large_prime_log_sum_le n hn y hy) h2.le
    _ = _ := by ring

/-- Logarithm-weighted reciprocal sums below a cutoff are controlled by the harmonic sum. -/
lemma lemma83_small_prime_log_sum_le (n : ℕ) (y : ℝ) (hy : 1 ≤ y) :
    (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y), Real.log (p:ℝ)/(p:ℝ)) ≤
      Real.log y * (1+Real.log y) := by
  have hlog : 0 ≤ Real.log y := Real.log_nonneg hy
  have hinv : (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y), (p:ℝ)⁻¹) ≤
      (harmonic (Nat.floor y) : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpr := Nat.prime_of_mem_primeFactors hp'.1
      exact Finset.mem_Icc.mpr ⟨hpr.pos, Nat.le_floor hp'.2⟩
    · intro p hp hpnot
      positivity
  calc
    _ ≤ ∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y), Real.log y * (p:ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpr := Nat.prime_of_mem_primeFactors hp'.1
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_right
        (Real.log_le_log (Nat.cast_pos.mpr hpr.pos) hp'.2) (by positivity)
    _ = Real.log y * (∑ p ∈ n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y), (p:ℝ)⁻¹) := by rw [Finset.mul_sum]
    _ ≤ Real.log y * (harmonic (Nat.floor y) : ℝ) := mul_le_mul_of_nonneg_left hinv hlog
    _ ≤ _ := mul_le_mul_of_nonneg_left (harmonic_floor_le_one_add_log y hy) hlog

/-- Fully elementary squared-log-log bound once `log n > 1`. -/
lemma lemma83_prime_log_sum_le_loglog (n : ℕ) (hn : 0 < n)
    (hlogn : 1 < Real.log n) :
    (∑ p ∈ n.primeFactors, Real.log (p:ℝ)/(p:ℝ)) ≤ (1+Real.log (Real.log n))^2 := by
  rw [← Finset.sum_filter_add_sum_filter_not n.primeFactors (fun p : ℕ => (p:ℝ) ≤ Real.log n)]
  have hsmall := lemma83_small_prime_log_sum_le n (Real.log n) hlogn.le
  have hlarge := lemma83_large_prime_log_sum_le n hn (Real.log n) (by linarith)
  rw [div_self (by linarith : Real.log n ≠ 0)] at hlarge
  have hll : 0 ≤ Real.log (Real.log n) := Real.log_nonneg hlogn.le
  nlinarith

lemma lemma83_one_add_product_le_exp_sum (S : Finset ℕ) (C : ℝ) (hC : 0 ≤ C) :
    (∏ p ∈ S, (1+C/(p:ℝ))) ≤ Real.exp (C * ∑ p ∈ S, (p:ℝ)⁻¹) := by
  calc
    _ ≤ ∏ p ∈ S, Real.exp (C/(p:ℝ)) := by
      apply Finset.prod_le_prod
      · intro p hp; positivity
      · intro p hp
        have := Real.add_one_le_exp (C/(p:ℝ))
        linarith
    _ = _ := by simp only [← Real.exp_sum, Finset.mul_sum, div_eq_mul_inv]

/-- Uniform finite-prime-product estimate with an arbitrary splitting cutoff. -/
lemma lemma83_prime_product_le_cutoff (n : ℕ) (hn : 0 < n)
    (y C : ℝ) (K : ℕ) (hy : 1 < y) (hC : 0 ≤ C) (hK : 3*C ≤ (K:ℝ)) :
    (∏ p ∈ n.primeFactors, (1+C/(p:ℝ))) ≤
      (1+Real.log y)^K * Real.exp (C * Real.log n / (y*Real.log 2)) := by
  have hs := lemma83_small_prime_product_le
    (n.primeFactors.filter (fun p : ℕ => (p:ℝ) ≤ y))
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    y C K hy hC hK (fun p hp => (Finset.mem_filter.mp hp).2)
  have hl : (∏ p ∈ n.primeFactors.filter (fun p : ℕ => ¬(p:ℝ) ≤ y), (1+C/(p:ℝ))) ≤
      Real.exp (C * Real.log n / (y*Real.log 2)) := by
    apply (lemma83_one_add_product_le_exp_sum _ C hC).trans
    apply Real.exp_le_exp.mpr
    have hh := mul_le_mul_of_nonneg_left
      (lemma83_large_prime_inv_sum_le n hn y (by linarith)) hC
    simpa only [mul_div_assoc] using hh
  rw [← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p : ℕ => (p:ℝ) ≤ y)]
  exact mul_le_mul hs hl (Finset.prod_nonneg (fun p hp => by positivity))
    (pow_nonneg (by have := Real.log_nonneg hy.le; linarith) _)

/-- The desired poly-log-log product bound for `log n > 1`. -/
lemma lemma83_prime_product_le_loglog (n : ℕ) (hn : 0 < n)
    (C : ℝ) (K : ℕ) (hlogn : 1 < Real.log n) (hC : 0 ≤ C)
    (hK : 3*C ≤ (K:ℝ)) :
    (∏ p ∈ n.primeFactors, (1+C/(p:ℝ))) ≤
      Real.exp (C/Real.log 2) * (1+Real.log (Real.log n))^K := by
  have h := lemma83_prime_product_le_cutoff n hn (Real.log n) C K hlogn hC hK
  have he : C*Real.log n / (Real.log n * Real.log 2) = C/Real.log 2 := by
    field_simp [show Real.log n ≠ 0 by linarith]
  simpa only [he, mul_comm] using h

/-- A polynomial bound uniform for every positive integer below `exp y`. -/
lemma lemma83_prime_product_uniform_le (n : ℕ) (hn : 0 < n)
    (y C : ℝ) (K : ℕ) (hy : 1 < y) (hny : Real.log n ≤ y)
    (hC : 0 ≤ C) (hK : 3*C ≤ (K:ℝ)) :
    (∏ p ∈ n.primeFactors, (1+C/(p:ℝ))) ≤
      Real.exp (C/Real.log 2) * (1+Real.log y)^K := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hy0 : 0 < y := by linarith
  apply (lemma83_prime_product_le_cutoff n hn y C K hy hC hK).trans
  rw [mul_comm (Real.exp (C/Real.log 2))]
  apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by have := Real.log_nonneg hy.le; linarith) _)
  apply Real.exp_le_exp.mpr
  calc
    C * Real.log n / (y * Real.log 2) ≤ C * y / (y * Real.log 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hny hC) (mul_nonneg hy0.le h2.le)
    _ = C/Real.log 2 := by field_simp

/-- Squared-logarithmic cutoff bound, uniform also for `n = 1` and small `n`. -/
lemma lemma83_prime_log_sum_uniform_le (n : ℕ) (hn : 0 < n)
    (y : ℝ) (hy : 1 < y) (hny : Real.log n ≤ y) :
    (∑ p ∈ n.primeFactors, Real.log (p:ℝ)/(p:ℝ)) ≤ (1+Real.log y)^2 := by
  rw [← Finset.sum_filter_add_sum_filter_not n.primeFactors (fun p : ℕ => (p:ℝ) ≤ y)]
  have hsmall := lemma83_small_prime_log_sum_le n y hy.le
  have hlarge := lemma83_large_prime_log_sum_le n hn y (by linarith)
  have hratio : Real.log n/y ≤ 1 := (div_le_one (by linarith : 0 < y)).mpr hny
  have hl : 0 ≤ Real.log y := Real.log_nonneg hy.le
  nlinarith

lemma lemma83_loglog_two_base_pos : 0 < 1 + Real.log (Real.log 2) := by
  have hlo : (1:ℝ)/2 ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hhi : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0:ℝ) < 2) (by norm_num : (2:ℝ) ≠ 1)
    norm_num at h
    exact h
  have hh : -Real.log 2 ≤ Real.log (Real.log 2) := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 2⁻¹) (by simpa only [one_div] using hlo)
    simpa only [Real.log_inv] using h
  linarith

lemma lemma83_log_nat_gt_one {n : ℕ} (hn : 3 ≤ n) : 1 < Real.log n := by
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have he : Real.exp 1 < (n:ℝ) := Real.exp_one_lt_three.trans_le (by exact_mod_cast hn)
  rwa [← Real.exp_log hn0, Real.exp_lt_exp] at he

/-- Uniform poly-log-log control for every `n ≥ 2`, including the small endpoint. -/
lemma lemma83_prime_product_loglog_exists (C : ℝ) (hC : 0 ≤ C) (K : ℕ)
    (hK : 3*C ≤ (K:ℝ)) :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 2 ≤ n →
      (∏ p ∈ n.primeFactors, (1+C/(p:ℝ))) ≤ A * (1+Real.log (Real.log n))^K := by
  let b := 1+Real.log (Real.log 2)
  have hb : 0 < b := lemma83_loglog_two_base_pos
  let A := Real.exp (C/Real.log 2) + (1+C/2)/b^K
  have hA : Real.exp (C/Real.log 2) ≤ A := by dsimp [A]; exact le_add_of_nonneg_right (by positivity)
  refine ⟨A, (Real.exp_pos _).trans_le hA, ?_⟩
  intro n hn
  by_cases hn2 : n = 2
  · subst n
    simp only [Nat.prime_two.primeFactors, Finset.prod_singleton, Nat.cast_ofNat]
    change 1+C/2 ≤ A*b^K
    dsimp [A]
    rw [add_mul, div_mul_cancel₀ _ (pow_pos hb K).ne']
    have := mul_nonneg (Real.exp_pos (C/Real.log 2)).le (pow_pos hb K).le
    linarith
  · have hn3 : 3 ≤ n := by omega
    have hln := lemma83_log_nat_gt_one hn3
    apply (lemma83_prime_product_le_loglog n (by omega) C K hln hC hK).trans
    exact mul_le_mul_of_nonneg_right hA (pow_nonneg (by have := Real.log_nonneg hln.le; linarith) K)

/-- Uniform squared-log-log control for every `n ≥ 2`. -/
lemma lemma83_prime_log_sum_loglog_exists :
    ∃ A : ℝ, 0 < A ∧ ∀ n : ℕ, 2 ≤ n →
      (∑ p ∈ n.primeFactors, Real.log (p:ℝ)/(p:ℝ)) ≤ A * (1+Real.log (Real.log n))^2 := by
  let b := 1+Real.log (Real.log 2)
  have hb : 0 < b := lemma83_loglog_two_base_pos
  let A := 1 + (Real.log 2/2)/b^2
  have hA : 1 ≤ A := by dsimp [A]; have := Real.log_pos (by norm_num : (1:ℝ) < 2); exact le_add_of_nonneg_right (by positivity)
  refine ⟨A, by linarith, ?_⟩
  intro n hn
  by_cases hn2 : n = 2
  · subst n
    simp only [Nat.prime_two.primeFactors, Finset.sum_singleton, Nat.cast_ofNat]
    change Real.log 2/2 ≤ A*b^2
    dsimp [A]
    rw [add_mul, div_mul_cancel₀ _ (pow_pos hb 2).ne']
    nlinarith [sq_nonneg b]
  · have hn3 : 3 ≤ n := by omega
    apply (lemma83_prime_log_sum_le_loglog n (by omega) (lemma83_log_nat_gt_one hn3)).trans
    have := mul_le_mul_of_nonneg_right hA (sq_nonneg (1+Real.log (Real.log n)))
    simpa only [one_mul] using this

end ZhangLS.Spec
