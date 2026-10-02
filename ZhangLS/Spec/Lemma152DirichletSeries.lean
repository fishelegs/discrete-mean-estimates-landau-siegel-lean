import ZhangLS.Spec.Lemma152CoefficientMultiplicative
import ZhangLS.Spec.Lemma152LocalNorm
import ZhangLS.Spec.Lemma83ConverseEuler
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma152_term_mul {D m n : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (s : ℂ) (h : m.Coprime n) :
    LSeries.term (lemma152Coefficient χ β 1 1) s (m*n) =
      LSeries.term (lemma152Coefficient χ β 1 1) s m *
        LSeries.term (lemma152Coefficient χ β 1 1) s n := by
  by_cases hm : m = 0
  · subst m; simp
  by_cases hn : n = 0
  · subst n; simp
  have hcoeff := (lemma152_coefficient_multiplicative χ β hβ 1 1).map_mul_of_coprime h
  change lemma152Coefficient χ β 1 1 (m*n) =
    lemma152Coefficient χ β 1 1 m * lemma152Coefficient χ β 1 1 n at hcoeff
  rw [LSeries.term_of_ne_zero (mul_ne_zero hm hn),LSeries.term_of_ne_zero hm,
    LSeries.term_of_ne_zero hn,hcoeff,Nat.cast_mul,Complex.natCast_mul_natCast_cpow]
  exact mul_div_mul_comm _ _ _ _

lemma lemma152_prime_power_term {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hp : 0 < p) (s : ℂ) (e : ℕ) :
    LSeries.term (lemma152Coefficient χ β 1 1) s (p^e) =
      lemma152Coefficient χ β 1 1 (p^e)*lemma32PrimeMonomial p s^e := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero e hp.ne'),Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul p e s,Complex.cpow_nat_mul,
    div_eq_mul_inv,← inv_pow,← Complex.cpow_neg,← lemma32_prime_monomial_eq_cpow hp s]

lemma lemma152_monomial_norm_half {p : ℕ} (hp : p.Prime) (s : ℂ) (hs : 1 ≤ s.re) :
    ‖lemma32PrimeMonomial p s‖ ≤ 1/2 := by
  rw [lemma83_prime_monomial_norm_rpow hp.pos]
  calc
    (p:ℝ)^(-s.re) ≤ (p:ℝ)^(-1:ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_lt.le) (by linarith)
    _ = (p:ℝ)⁻¹ := Real.rpow_neg_one _
    _ ≤ 1/2 := by
      simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
        (show (2:ℝ) ≤ p by exact_mod_cast hp.two_le)

/-- The original Section15 Dirichlet series is absolutely convergent for Re s>1. -/
lemma lemma152_lseries_summable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (lemma152Coefficient χ β 1 1) s := by
  apply summable_norm_iff.mp
  apply EulerProduct.summable_norm_of_prime_power_tsum_le
    (LSeries.term (lemma152Coefficient χ β 1 1) s) (by simp)
    (by simp [LSeries.term]) (fun h => lemma152_term_mul χ β hβ s h)
    (fun hp => by
      simpa only [lemma152_prime_power_term χ β hp.pos s] using
        (lemma152_coefficient_local_norm_series χ β hβ hp
          (lemma32PrimeMonomial _ s) (lemma152_monomial_norm_half hp s hs.le)).1)
    (fun p => 384*(p:ℝ)^(-s.re)) (fun p => by positivity)
    (((Real.summable_nat_rpow.mpr (by linarith : -s.re < -1)).subtype Nat.Prime).mul_left 384)
  intro p hp
  simpa only [lemma152_prime_power_term χ β hp.pos s,lemma83_prime_monomial_norm_rpow hp.pos] using
    (lemma152_coefficient_local_norm_series χ β hβ hp
      (lemma32PrimeMonomial p s) (lemma152_monomial_norm_half hp s hs.le)).2

lemma lemma152_dirichlet_series_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (s : ℂ) (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => ∑' e : ℕ,
      lemma152Coefficient χ β 1 1 (p.val^e)*lemma32PrimeMonomial p.val s^e)
      (lemma152DirichletSeries χ β 1 1 s) := by
  have hh := EulerProduct.eulerProduct_hasProd
    (f := LSeries.term (lemma152Coefficient χ β 1 1) s)
    (by simp [LSeries.term]) (fun {m n} h => lemma152_term_mul χ β hβ s h)
    (lemma152_lseries_summable χ β hβ s hs).norm (LSeries.term_zero _ s)
  change HasProd _ (∑' n : ℕ, LSeries.term (lemma152Coefficient χ β 1 1) s n)
  apply hh.congr_fun
  intro p
  apply tsum_congr
  intro e
  exact (lemma152_prime_power_term χ β p.property.pos s e).symm

end ZhangLS.Spec
