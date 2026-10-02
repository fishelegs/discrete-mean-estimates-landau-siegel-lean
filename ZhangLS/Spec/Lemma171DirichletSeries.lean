import ZhangLS.Spec.Lemma171EulerFactors
import ZhangLS.Spec.Lemma32ActualSeriesIdentity

/-!
# Lemma 17.1: absolute convergence and the actual global Euler identity

The series converges absolutely for Re s>1. The exact analytic correction is
ζ(2s)⁻¹ times the finite ramification product. The actual contour shift is proved in `Lemma171ContourInfinite.lean`.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma171_coefficient_le_tau_four {D : ℕ} (χ : RealPrimitiveCharacter D) (n : ℕ) :
    lemma171Coefficient χ n ≤ (lemma34Tau 4 n : ℝ) := by
  have hn := lemma23NuArithmeticFunction_norm_le_card_divisors χ n
  rw [← lemma32_tau_two_eq_card_divisors n] at hn
  calc
    _ ≤ (lemma34Tau 2 n : ℝ)^2 := pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ _ := by exact_mod_cast lemma32_tau2_square_le_tau4 n

/-- The actual ν² Dirichlet series, used only in its proven convergence region below. -/
noncomputable def lemma171DirichletSeries {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) : ℂ :=
  LSeries (fun n => (lemma171Coefficient χ n : ℂ)) s

lemma lemma171_lseries_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (fun n => (lemma171Coefficient χ n : ℂ)) s := by
  have ht := lemma32_tau_lseries_summable 3 s hs
  rw [LSeriesSummable,← summable_norm_iff] at ht ⊢
  apply ht.of_nonneg_of_le (fun n => norm_nonneg _)
  intro n
  apply LSeries.norm_term_le
  simp only [Complex.norm_real,Real.norm_eq_abs,
    abs_of_nonneg (lemma171_coefficient_nonneg χ n),Complex.norm_natCast]
  exact lemma171_coefficient_le_tau_four χ n

lemma lemma171_term_one {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) :
    LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) s 1 = 1 := by
  simp [LSeries.term,lemma171_coefficient_one]

lemma lemma171_term_mul {D m n : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ)
    (h : m.Coprime n) :
    LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) s (m*n) =
      LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) s m*
        LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) s n := by
  by_cases hm : m = 0
  · subst m; simp
  by_cases hn : n = 0
  · subst n; simp
  rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn),LSeries.term_of_ne_zero hm,
    LSeries.term_of_ne_zero hn,lemma171_coefficient_mul χ h,
    Complex.ofReal_mul,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  exact mul_div_mul_comm _ _ _ _

lemma lemma171_euler_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ,
      LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) s (p.val^e))
      (lemma171DirichletSeries χ s) := by
  exact EulerProduct.eulerProduct_hasProd (lemma171_term_one χ s)
    (fun {m n} h => lemma171_term_mul χ s h)
    (lemma171_lseries_summable χ s hs).norm (LSeries.term_zero _ s)

lemma lemma171_prime_power_term {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : 0 < p) (s : ℂ) (e : ℕ) :
    LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) s (p^e) =
      (lemma171Coefficient χ (p^e) : ℂ)*lemma32PrimeMonomial p s^e := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero e hp.ne'),Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul p e s,Complex.cpow_nat_mul,
    div_eq_mul_inv,← inv_pow,← Complex.cpow_neg,← lemma32_prime_monomial_eq_cpow hp s]

/-- A finite ramification factor; its denominators are nonzero for Re s > 0. -/
noncomputable def lemma171RamificationFactor (D : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ D.primeFactors, (1+lemma32PrimeMonomial p s)⁻¹

/-- This correction is analytic in Re s > 1/2; the continuation claim is proved below,
not inferred from a quotient of totalized functions. -/
noncomputable def lemma171AnalyticCorrection (D : ℕ) (s : ℂ) : ℂ :=
  (riemannZeta (2*s))⁻¹ * lemma171RamificationFactor D s

lemma lemma171_ramification_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) :
    HasProd (fun p : Nat.Primes => if p.val ∣ D then (1+lemma32PrimeMonomial p.val s)⁻¹ else 1)
      (lemma171RamificationFactor D s) := by
  have hh : HasProd
      (fun p : Nat.Primes => if p.val ∣ D then (1+lemma32PrimeMonomial p.val s)⁻¹ else 1)
      (∏ p ∈ D.primeFactors.subtype Nat.Prime,
        (if p.val ∣ D then (1+lemma32PrimeMonomial p.val s)⁻¹ else 1)) := by
    apply hasProd_prod_of_ne_finset_one
    intro p hp
    have hn : ¬ p.val ∣ D := by
      intro hd
      apply hp
      exact Finset.mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨p.property,hd,χ.modulus_ne_zero⟩)
    rw [if_neg hn]
  have he : (∏ p ∈ D.primeFactors.subtype Nat.Prime,
        (if p.val ∣ D then (1+lemma32PrimeMonomial p.val s)⁻¹ else 1)) =
      lemma171RamificationFactor D s := by
    calc
      _ = ∏ p ∈ D.primeFactors.subtype Nat.Prime, (1+lemma32PrimeMonomial p.val s)⁻¹ := by
        apply Finset.prod_congr rfl
        intro p hp
        have hd : p.val ∣ D := (Nat.mem_primeFactors.mp (Finset.mem_subtype.mp hp)).2.1
        rw [if_pos hd]
      _ = _ := by
        unfold lemma171RamificationFactor
        exact Finset.prod_subtype_of_mem (fun p : ℕ => (1+lemma32PrimeMonomial p s)⁻¹)
          (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rwa [he] at hh

lemma lemma171_monomial_two_mul (p : ℕ) (s : ℂ) :
    lemma32PrimeMonomial p (2*s) = lemma32PrimeMonomial p s ^ 2 := by
  unfold lemma32PrimeMonomial
  rw [pow_two,← Complex.exp_add]
  congr 1
  ring

lemma lemma171_zeta_correction_hasProd (s : ℂ) (hs : 1/2 < s.re) :
    HasProd (fun p : Nat.Primes => 1-lemma32PrimeMonomial p.val s^2)
      (riemannZeta (2*s))⁻¹ := by
  have h2 : 1 < (2*s).re := by simp only [Complex.mul_re]; norm_num; linarith
  have hz := lemma32_actual_zeta_monomial_euler_hasProd (2*s) h2
  have ht := hz.inv₀ (riemannZeta_ne_zero_of_one_lt_re h2)
  simpa [lemma171_monomial_two_mul] using ht

lemma lemma171_one_add_monomial_ne_zero {p : ℕ} (hp : p.Prime)
    (s : ℂ) (hs : 0 < s.re) : 1+lemma32PrimeMonomial p s ≠ 0 := by
  have hn := lemma32_prime_monomial_norm_lt_one hp.one_lt s hs
  intro h
  have he : lemma32PrimeMonomial p s = -1 := by linear_combination h
  rw [he,norm_neg,norm_one] at hn
  linarith

lemma lemma171_local_correction_factorization {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (s : ℂ) (hs : 0 < s.re) :
    lemma171LocalCorrection χ p (lemma32PrimeMonomial p s) =
      (1-lemma32PrimeMonomial p s^2)*
        (if p ∣ D then (1+lemma32PrimeMonomial p s)⁻¹ else 1) := by
  rw [lemma171_local_correction χ hp _ (lemma32_prime_monomial_norm_lt_one hp.one_lt s hs)]
  split_ifs with h
  · have hn := lemma171_one_add_monomial_ne_zero hp s hs
    field_simp
    ring
  · simp

lemma lemma171_local_corrections_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1/2 < s.re) :
    HasProd (fun p : Nat.Primes => lemma171LocalCorrection χ p.val (lemma32PrimeMonomial p.val s))
      (lemma171AnalyticCorrection D s) := by
  have hh := (lemma171_zeta_correction_hasProd s hs).mul (lemma171_ramification_hasProd χ s)
  exact hh.congr_fun (fun p =>
    (lemma171_local_correction_factorization χ p.property s (by linarith)))


/-- Exact ν² Dirichlet-series identity in the genuine absolute-convergence region. -/
lemma lemma171_dirichlet_series_identity {D : ℕ} (χ : RealPrimitiveCharacter D)
    (s : ℂ) (hs : 1 < s.re) :
    lemma171DirichletSeries χ s =
      lemma171AnalyticCorrection D s * (riemannZeta s * dirichletLFunction χ s)^2 := by
  have hc := lemma171_local_corrections_hasProd χ s (by linarith)
  have hz := (lemma32_actual_zeta_monomial_euler_hasProd s hs).pow 2
  have hl := (lemma32_actual_L_monomial_euler_hasProd χ s hs).pow 2
  have hp := hc.mul (hz.mul hl)
  have hb : HasProd (fun p : Nat.Primes => ∑' e : ℕ,
      LSeries.term (fun n => (lemma171Coefficient χ n : ℂ)) s (p.val^e))
      (lemma171AnalyticCorrection D s*(riemannZeta s^2*dirichletLFunction χ s^2)) := by
    apply hp.congr_fun
    intro p
    have hn := lemma32_prime_monomial_norm_lt_one p.property.one_lt s (by linarith)
    have h1 : 1-lemma32PrimeMonomial p.val s ≠ 0 := by
      intro h
      have ht : lemma32PrimeMonomial p.val s = 1 := (sub_eq_zero.mp h).symm
      rw [ht,norm_one] at hn
      linarith
    have hcn : ‖χ.evalNat p.val*lemma32PrimeMonomial p.val s‖ < 1 := by
      rw [norm_mul]
      calc
        _ ≤ 1*‖lemma32PrimeMonomial p.val s‖ :=
          mul_le_mul_of_nonneg_right (χ.evalNat_norm_le_one p.val) (norm_nonneg _)
        _ < 1 := by simpa using hn
    have h2 : 1-χ.evalNat p.val*lemma32PrimeMonomial p.val s ≠ 0 := by
      intro h
      have ht : χ.evalNat p.val*lemma32PrimeMonomial p.val s = 1 := (sub_eq_zero.mp h).symm
      rw [ht,norm_one] at hcn
      linarith
    simp_rw [lemma171_prime_power_term χ p.property.pos s]
    unfold lemma171LocalCorrection
    have h2' : 1-lemma32PrimeMonomial p.val s*χ.evalNat p.val ≠ 0 := by
      simpa only [mul_comm] using h2
    field_simp [h1,h2,h2']
  have he := (lemma171_euler_hasProd χ s hs).unique hb
  simpa only [mul_pow] using he


end ZhangLS.Spec
