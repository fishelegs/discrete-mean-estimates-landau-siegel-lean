import ZhangLS.Spec.Lemma161CoefficientMultiplicative
import ZhangLS.Spec.Lemma162GeneralMNorm
import ZhangLS.Spec.Lemma161DirichletSeries
import ZhangLS.Spec.Lemma83ConverseEuler
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma162_general_m_term_mul {D m n : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (hβ : β.re = 0) (s : ℂ) (h : m.Coprime n) :
    LSeries.term (lemma161Coefficient χ β d l) s (m*n) =
      LSeries.term (lemma161Coefficient χ β d l) s m *
        LSeries.term (lemma161Coefficient χ β d l) s n := by
  by_cases hm : m = 0
  · subst m; simp
  by_cases hn : n = 0
  · subst n; simp
  have hcoeff := (lemma161_coefficient_multiplicative χ β hβ d l).map_mul_of_coprime h
  change lemma161Coefficient χ β d l (m*n) =
    lemma161Coefficient χ β d l m * lemma161Coefficient χ β d l n at hcoeff
  rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn),LSeries.term_of_ne_zero hm,
    LSeries.term_of_ne_zero hn,hcoeff,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  exact mul_div_mul_comm _ _ _ _

lemma lemma162_general_m_prime_power_term {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (hp : 0 < p) (s : ℂ) (e : ℕ) :
    LSeries.term (lemma161Coefficient χ β d l) s (p^e) =
      lemma161Coefficient χ β d l (p^e)*lemma32PrimeMonomial p s^e := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero e hp.ne'),Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul p e s,Complex.cpow_nat_mul,
    div_eq_mul_inv,← inv_pow,← Complex.cpow_neg,← lemma32_prime_monomial_eq_cpow hp s]

/-- The original Section16 Dirichlet series is absolutely convergent for Re s>1. -/
lemma lemma162_general_m_lseries_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (hβ : β.re = 0) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (lemma161Coefficient χ β d l) s := by
  apply summable_norm_iff.mp
  apply EulerProduct.summable_norm_of_prime_power_tsum_le
    (LSeries.term (lemma161Coefficient χ β d l) s) (by simp)
    (by simp [LSeries.term]) (fun h => lemma162_general_m_term_mul χ β d l hβ s h)
    (fun hp => by
      simpa only [lemma162_general_m_prime_power_term χ β d l hp.pos s] using
        (lemma162_general_m_local_norm_series χ β hβ hp d l
          (lemma32PrimeMonomial _ s) (lemma152_monomial_norm_half hp s hs.le)).1)
    (fun p => 384*(p:ℝ)^(-s.re)) (fun p => by positivity)
    (((Real.summable_nat_rpow.mpr (by linarith : -s.re < -1)).subtype Nat.Prime).mul_left 384)
  intro p hp
  simpa only [lemma162_general_m_prime_power_term χ β d l hp.pos s,lemma83_prime_monomial_norm_rpow hp.pos] using
    (lemma162_general_m_local_norm_series χ β hβ hp d l
      (lemma32PrimeMonomial p s) (lemma152_monomial_norm_half hp s hs.le)).2

lemma lemma162_general_m_dirichlet_series_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (hβ : β.re = 0) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ,
      lemma161Coefficient χ β d l (p.val^e)*lemma32PrimeMonomial p.val s^e)
      (lemma161DirichletSeries χ β d l s) := by
  have hh := EulerProduct.eulerProduct_hasProd
    (f := LSeries.term (lemma161Coefficient χ β d l) s)
    (by simp [LSeries.term]) (fun {m n} h => lemma162_general_m_term_mul χ β d l hβ s h)
    (lemma162_general_m_lseries_summable χ β d l hβ s hs).norm (LSeries.term_zero _ s)
  change HasProd _ (∑' n : ℕ, LSeries.term (lemma161Coefficient χ β d l) s n)
  apply hh.congr_fun
  intro p
  apply tsum_congr
  intro e
  exact (lemma162_general_m_prime_power_term χ β d l p.property.pos s e).symm

end ZhangLS.Spec
