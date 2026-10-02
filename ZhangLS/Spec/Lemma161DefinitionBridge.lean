import ZhangLS.Spec.Lemma161ActualContinuation
import ZhangLS.Spec.Lemma161NormalizedProduct
import Mathlib.NumberTheory.LSeries.Dirichlet

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

lemma lemma161_power_term_shift (β s : ℂ) (n : ℕ) :
    LSeries.term (lemma83PowerCoefficient β) s n = LSeries.term (fun _ => 1) (s+β) n := by
  by_cases hn : n = 0
  · simp [hn]
  have hn' : (n:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  simp only [LSeries.term_of_ne_zero hn,lemma83PowerCoefficient,ArithmeticFunction.coe_mk,if_neg hn]
  rw [div_eq_mul_inv,← Complex.cpow_neg,← Complex.cpow_add _ _ hn']
  rw [one_div,← Complex.cpow_neg]
  congr 1
  ring

lemma lemma161_power_hasSum (β s : ℂ) (hs : 1 < (s+β).re) :
    LSeriesHasSum (lemma83PowerCoefficient β) s (riemannZeta (s+β)) := by
  have hh := LSeriesHasSum_one hs
  change HasSum _ _ at hh ⊢
  exact hh.congr_fun (lemma161_power_term_shift β s)

/-- The arithmetic κ₂ definition satisfies the paper's literal zeta quotient. -/
lemma lemma161_kappa_defining_series (β : ℂ) (hβ : β.re = 0)
    (s : ℂ) (hs : 1 < s.re) :
    LSeriesSummable (lemma161Kappa β) s ∧
      LSeries (lemma161Kappa β) s = riemannZeta (s+β)/riemannZeta s := by
  have hp := lemma161_power_hasSum β s (by simpa [hβ] using hs)
  have hμ : LSeriesSummable (ArithmeticFunction.moebius : ArithmeticFunction ℂ) s :=
    ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs
  have hk := ArithmeticFunction.LSeriesHasSum_mul hμ.LSeriesHasSum hp
  refine ⟨hk.LSeriesSummable,?_⟩
  unfold lemma161Kappa
  rw [ArithmeticFunction.LSeries_mul' hμ hp.LSeriesSummable,hp.LSeries_eq]
  have hμz := ArithmeticFunction.LSeries_zeta_mul_Lseries_moebius hs
  rw [ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs] at hμz
  have hμz' : riemannZeta s * LSeries (ArithmeticFunction.moebius : ArithmeticFunction ℂ) s = 1 := by
    simpa only [ArithmeticFunction.intCoe_apply] using hμz
  apply (eq_div_iff (riemannZeta_ne_zero_of_one_lt_re hs)).mpr
  calc
    _ = (riemannZeta s * LSeries (ArithmeticFunction.moebius : ArithmeticFunction ℂ) s)*riemannZeta (s+β) := by ring
    _ = _ := by rw [hμz',one_mul]

lemma lemma161_original_local_series {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (q : Nat.Primes) (s : ℂ) (hs : 0 < s.re) :
    (∑' n : ℕ, lemma161Coefficient χ β 1 1 (q.val^n)*lemma32PrimeMonomial q.val s^n) =
      1 + lemma161LambdaFactor χ β q.val 1 *
        ∑' n : ℕ, lemma161Xi χ β (q.val^(n+1)) 1 1*lemma32PrimeMonomial q.val s^(n+1) := by
  have hx := lemma32_prime_monomial_norm_lt_one q.property.one_lt s hs
  have hsum := (lemma161_coefficient_prime_hasSum χ β hβ q.property _ hx).summable
  rw [hsum.tsum_eq_zero_add]
  simp only [pow_zero,lemma161_coefficient_one,one_mul]
  congr 1
  rw [← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold lemma161Coefficient
  rw [lemma161_modified_lambda_prime_power χ β q.property,if_neg q.property.not_dvd_one]
  ring

/-- The literal Section16 Euler factor, not just its canceled rational model. -/
noncomputable def lemma161OriginalEulerFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  (1-(q.val:ℂ)^(-s-β))/((1-(q.val:ℂ)^(-s))*(1-χ.evalNat q.val*(q.val:ℂ)^(-s))) *
    (1+lemma161LambdaFactor χ β q.val 1 *
      ∑' n : ℕ, lemma161Xi χ β (q.val^(n+1)) 1 1*((q.val:ℂ)^(-s))^(n+1))

lemma lemma161_original_factor_agreement {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (q : Nat.Primes) (s : ℂ) (hs : 0 < s.re) :
    lemma161OriginalEulerFactor χ β q s = lemma161PrimeFactor χ β q s := by
  have hx := lemma32_prime_monomial_norm_lt_one q.property.one_lt s hs
  have hc := lemma161_actual_local_correction χ β hβ q.property _ hx
  rw [lemma161_original_local_series χ β hβ q s hs] at hc
  have hm : (q.val:ℂ)^(-s-β) = (q.val:ℂ)^(-β)*lemma32PrimeMonomial q.val s := by
    rw [show -s-β = -β + -s by ring,Complex.cpow_add _ _ (Nat.cast_ne_zero.mpr q.property.ne_zero),
      lemma32_prime_monomial_eq_cpow q.property.pos]
  unfold lemma161OriginalEulerFactor lemma161PrimeFactor
  rw [hm,lemma32_prime_monomial_eq_cpow q.property.pos β]
  simpa only [lemma32_prime_monomial_eq_cpow q.property.pos s] using hc

/-- Exact χ(2)=1 Euler normalization, with q=2 omitted and a prefactor 2.
In particular this is not a ratio through the vanishing q=2 center factor. -/
lemma lemma161_star_exceptional_original {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hχ : χ.evalNat 2 = 1)
    (s : ℂ) (hs : 9/10 < s.re) :
    lemma161Star χ β s =
      2 * ∏' q : {q : Nat.Primes // 2 < q.val}, lemma161OriginalEulerFactor χ β q.val s := by
  rw [lemma161Star,if_pos hχ,lemma161_restricted_product_eq_subtype]
  congr 1
  exact tprod_congr (fun q => (lemma161_original_factor_agreement χ β hβ q.val s (by linarith)).symm)

end ZhangLS.Spec
