import ZhangLS.Spec.Lemma171Residue

/-! # Uniform bounds for the actual Lemma 17.1 correction

Global polynomial-in-D bounds support the eventual contour shift. The stronger
local-sector bound is absolute and will control residue derivatives by Cauchy.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex Filter Topology
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma171_zeta_correction_finite_bound (σ : ℝ) (hσ : 1/2 < σ)
    (s : ℂ) (hs : σ ≤ s.re) (S : Finset Nat.Primes) :
    ‖∏ p ∈ S, (1-lemma32PrimeMonomial p.val s^2)‖ ≤ lemma32RegularProductBound σ := by
  let f (p : Nat.Primes) : ℂ := 1-lemma32PrimeMonomial p.val s^2
  have hh := S.norm_prod_one_add_sub_one_le (fun p => f p-1)
  simp only [add_sub_cancel] at hh
  have hn : Summable (fun n : ℕ => (n : ℝ)^(-2*σ)) := Real.summable_nat_rpow.mpr (by linarith)
  have hp : Summable (fun p : Nat.Primes => (p.val : ℝ)^(-2*σ)) := hn.subtype _
  have hlocal (p : Nat.Primes) : ‖f p-1‖ ≤ 7659*(p.val : ℝ)^(-2*σ) := by
    have he : ‖f p-1‖ = ‖lemma32PrimeMonomial p.val s‖^2 := by
      simp only [f,sub_sub_cancel_left,norm_neg,norm_pow]
    rw [he,lemma32_prime_monomial_norm_square p.property.pos]
    have hb := Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast p.property.one_lt.le : (1 : ℝ) ≤ p.val) (by linarith : -2*s.re ≤ -2*σ)
    have hnon := Real.rpow_nonneg (Nat.cast_nonneg p.val) (-2*σ)
    linarith
  have hsum : (∑ p ∈ S, ‖f p-1‖) ≤ 7659*∑' p : Nat.Primes, (p.val : ℝ)^(-2*σ) := by
    calc
      _ ≤ ∑ p ∈ S, 7659*(p.val : ℝ)^(-2*σ) := Finset.sum_le_sum (fun p _ => hlocal p)
      _ = 7659*∑ p ∈ S, (p.val : ℝ)^(-2*σ) := (Finset.mul_sum _ _ _).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hp.sum_le_tsum S (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)) (by norm_num)
  have hnorm := norm_le_norm_sub_add (∏ p ∈ S, f p) (1 : ℂ)
  norm_num only [norm_one] at hnorm
  calc
    _ ≤ Real.exp (∑ p ∈ S, ‖f p-1‖) := by dsimp [f] at *; linarith
    _ ≤ _ := Real.exp_le_exp.mpr hsum

lemma lemma171_zeta_inverse_uniform_bound (σ : ℝ) (hσ : 1/2 < σ)
    (s : ℂ) (hs : σ ≤ s.re) :
    ‖(riemannZeta (2*s))⁻¹‖ ≤ lemma32RegularProductBound σ := by
  have ht := lemma171_zeta_correction_hasProd s (hσ.trans_le hs)
  apply le_of_tendsto ht.norm
  filter_upwards with S
  simpa only [norm_prod] using lemma171_zeta_correction_finite_bound σ hσ s hs S

lemma lemma171_ramified_sector_factor_bound {p : ℕ} (_hp : p.Prime) (s : ℂ)
    (hphase : |s.im*Real.log (p : ℝ)| ≤ 1) :
    ‖(1+lemma32PrimeMonomial p s)⁻¹‖ ≤ 1 := by
  have hc := lemma32_cos_lower_of_abs_le_one _ hphase
  have hz : 0 ≤ (lemma32PrimeMonomial p s).re := by
    rw [lemma32_prime_monomial_re]
    exact mul_nonneg (Real.exp_pos _).le (by linarith)
  have hn : 1 ≤ ‖1+lemma32PrimeMonomial p s‖ := by
    have hh := Complex.re_le_norm (1+lemma32PrimeMonomial p s)
    simp only [Complex.add_re,Complex.one_re] at hh
    linarith
  rw [norm_inv]
  exact inv_le_one_of_one_le₀ hn

lemma lemma171_ramification_sector_bound (D : ℕ) (s : ℂ)
    (hphase : |s.im| *lemma23PaperL D ≤ 1) :
    ‖lemma171RamificationFactor D s‖ ≤ 1 := by
  unfold lemma171RamificationFactor
  calc
    _ ≤ ∏ p ∈ D.primeFactors, ‖(1+lemma32PrimeMonomial p s)⁻¹‖ := Finset.norm_prod_le _ _
    _ ≤ 1 := by
      apply Finset.prod_le_one (fun _ _ => norm_nonneg _)
      intro p hp
      have hpr := Nat.prime_of_mem_primeFactors hp
      have hpl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hpr.one_lt.le)
      have hdl : Real.log (p : ℝ) ≤ lemma23PaperL D := by
        unfold lemma23PaperL
        exact Real.log_le_log (Nat.cast_pos.mpr hpr.pos) (Nat.cast_le.mpr (Nat.le_of_mem_primeFactors hp))
      apply lemma171_ramified_sector_factor_bound hpr
      calc
        _ = |s.im| *Real.log (p : ℝ) := by rw [abs_mul,abs_of_nonneg hpl]
        _ ≤ |s.im| *lemma23PaperL D := mul_le_mul_of_nonneg_left hdl (abs_nonneg _)
        _ ≤ 1 := hphase

lemma lemma171_correction_sector_bound (D : ℕ) (σ : ℝ) (hσ : 1/2 < σ)
    (s : ℂ) (hs : σ ≤ s.re) (hphase : |s.im| *lemma23PaperL D ≤ 1) :
    ‖lemma171AnalyticCorrection D s‖ ≤ lemma32RegularProductBound σ := by
  unfold lemma171AnalyticCorrection
  rw [norm_mul]
  calc
    _ ≤ lemma32RegularProductBound σ*1 := mul_le_mul
      (lemma171_zeta_inverse_uniform_bound σ hσ s hs)
      (lemma171_ramification_sector_bound D s hphase) (norm_nonneg _)
      (lemma32_regular_product_bound_pos σ).le
    _ = _ := mul_one _

lemma lemma171_monomial_norm_le_three_quarters {p : ℕ} (hp : p.Prime)
    (s : ℂ) (hs : 1/2 ≤ s.re) : ‖lemma32PrimeMonomial p s‖ ≤ 3/4 := by
  have hsq : ‖lemma32PrimeMonomial p s‖^2 ≤ 1/2 := by
    rw [lemma32_prime_monomial_norm_square hp.pos]
    calc
      _ ≤ (p : ℝ)^(-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le
        (Nat.one_le_cast.mpr hp.one_lt.le) (by linarith)
      _ = (p : ℝ)⁻¹ := Real.rpow_neg_one _
      _ ≤ 1/2 := by
        simpa only [one_div] using (inv_anti₀ (by norm_num : (0 : ℝ) < 2) (Nat.cast_le.mpr hp.two_le))
  nlinarith [norm_nonneg (lemma32PrimeMonomial p s)]

lemma lemma171_ramification_global_bound (D : ℕ) (hD : 0 < D)
    (s : ℂ) (hs : 1/2 ≤ s.re) :
    ‖lemma171RamificationFactor D s‖ ≤ (D : ℝ)^2 := by
  have hpD : (∏ p ∈ D.primeFactors, p) ≤ D := Nat.le_of_dvd hD (Nat.prod_primeFactors_dvd D)
  have hlocal (p : ℕ) (hp : p ∈ D.primeFactors) :
      ‖(1+lemma32PrimeMonomial p s)⁻¹‖ ≤ (p : ℝ)^2 := by
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hm := lemma171_monomial_norm_le_three_quarters hpr s hs
    have hl : 1/4 ≤ ‖1+lemma32PrimeMonomial p s‖ := by
      have hh := norm_sub_norm_le (1 : ℂ) (-lemma32PrimeMonomial p s)
      simp only [norm_one,norm_neg,sub_neg_eq_add] at hh
      linarith
    rw [norm_inv]
    calc
      _ ≤ (1/4 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hl
      _ ≤ (p : ℝ)^2 := by have hp2 : (2 : ℝ) ≤ p := Nat.cast_le.mpr hpr.two_le; norm_num; nlinarith
  unfold lemma171RamificationFactor
  calc
    _ ≤ ∏ p ∈ D.primeFactors, ‖(1+lemma32PrimeMonomial p s)⁻¹‖ := Finset.norm_prod_le _ _
    _ ≤ ∏ p ∈ D.primeFactors, (p : ℝ)^2 :=
      Finset.prod_le_prod (fun p hp => norm_nonneg _) hlocal
    _ = (∏ p ∈ D.primeFactors, (p : ℝ))^2 := by rw [Finset.prod_pow]
    _ ≤ _ := by
      gcongr
      simpa only [Nat.cast_prod] using
        (show (((∏ p ∈ D.primeFactors, p) : ℕ) : ℝ) ≤ (D : ℝ) from Nat.cast_le.mpr hpD)

lemma lemma171_correction_global_bound (D : ℕ) (hD : 0 < D)
    (s : ℂ) (hs : 3/4 ≤ s.re) :
    ‖lemma171AnalyticCorrection D s‖ ≤ lemma32RegularProductBound (3/4)*(D : ℝ)^2 := by
  unfold lemma171AnalyticCorrection
  rw [norm_mul]
  exact mul_le_mul (lemma171_zeta_inverse_uniform_bound (3/4) (by norm_num) s hs)
    (lemma171_ramification_global_bound D hD s (by linarith)) (norm_nonneg _)
    (lemma32_regular_product_bound_pos _).le

end ZhangLS.Spec
