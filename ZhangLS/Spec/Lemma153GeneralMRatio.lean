import ZhangLS.Spec.Lemma153GeneralMContinuation
import ZhangLS.Spec.Lemma153FiniteProductRatio
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma153_general_m_local_ratio {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (d l : ℕ) (q : Nat.Primes)
    (s : ℂ) (hs : 9/10 ≤ s.re) (hM : lemma152EulerProduct χ β s ≠ 0) :
    lemma153GeneralMPrimeFactor χ β d l q s/lemma152PrimeFactor χ β q s =
      (∑' n : ℕ, lemma152Coefficient χ β d l (q.val^n)*lemma32PrimeMonomial q.val s^n) /
        (∑' n : ℕ, lemma152Coefficient χ β 1 1 (q.val^n)*lemma32PrimeMonomial q.val s^n) := by
  have hb := lemma153_general_m_local_agreement χ β hβ 1 1 q s hs
  rw [lemma153_general_m_baseline_prime] at hb
  have hg := lemma153_general_m_local_agreement χ β hβ d l q s hs
  have hR : lemma152LocalRemoval ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1))
      (χ.evalNat q.val) (lemma32PrimeMonomial q.val s) ≠ 0 := by
    intro hz
    have hq := lemma153_prime_factor_nonzero_of_product χ β s hM q
    rw [hz,zero_mul] at hb
    exact hq hb.symm
  rw [← hg,← hb]
  exact mul_div_mul_left _ _ hR

/-- The exact finite Euler-ratio identity (15.18), now derived from the true
M(d,l) continuation and absolutely convergent local coefficient series. -/
lemma lemma153_general_m_ratio {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) {d l : ℕ} (hd : d ≠ 0) (hl : l ≠ 0)
    (s : ℂ) (hs : 9/10 ≤ s.re) (hM : lemma152EulerProduct χ β s ≠ 0) :
    lemma153GeneralMEulerProduct χ β d l s / lemma153GeneralMEulerProduct χ β 1 1 s =
      ∏ q ∈ lemma153PrimeDivisorSet (d*l),
        (∑' n : ℕ, lemma152Coefficient χ β d l (q.val^n)*lemma32PrimeMonomial q.val s^n) /
          (∑' n : ℕ, lemma152Coefficient χ β 1 1 (q.val^n)*lemma32PrimeMonomial q.val s^n) := by
  rw [lemma153_general_m_baseline]
  have hbase := (lemma152_euler_product_multipliable χ β hβ s hs).hasProd
  have hgen := (lemma153_general_m_euler_multipliable χ β hβ hd hl s hs).hasProd
  rw [lemma153_finite_replacement_ratio (lemma153PrimeDivisorSet (d*l))
    (fun q => lemma152PrimeFactor χ β q s) (fun q => lemma153GeneralMPrimeFactor χ β d l q s)
    (lemma152EulerProduct χ β s) (lemma153GeneralMEulerProduct χ β d l s) hbase hgen hM (by
      intro q hq
      have hqd : ¬q.val ∣ d*l := by simpa only [lemma153_mem_prime_divisor_set (mul_ne_zero hd hl) q] using hq
      have hd' : ¬q.val ∣ d := fun h => hqd (h.trans (dvd_mul_right d l))
      have hl' : ¬q.val ∣ l := fun h => hqd (h.trans (dvd_mul_left l d))
      simp [lemma153GeneralMPrimeFactor,hd',hl'])]
  apply prod_congr rfl
  intro q hq
  exact lemma153_general_m_local_ratio χ β hβ d l q s hs hM

lemma lemma153_general_m_prime_power_ratio {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (q : Nat.Primes)
    (k l : ℕ) (hkl : k+l ≠ 0) (s : ℂ) (hs : 9/10 ≤ s.re)
    (hM : lemma152EulerProduct χ β s ≠ 0) :
    lemma153GeneralMEulerProduct χ β (q.val^k) (q.val^l) s /
        lemma153GeneralMEulerProduct χ β 1 1 s =
      (∑' n : ℕ, lemma152Coefficient χ β (q.val^k) (q.val^l) (q.val^n)*
        lemma32PrimeMonomial q.val s^n) /
        lemma153BaseClosed ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1)) (q.val:ℂ)⁻¹
          (χ.evalNat q.val) (lemma32PrimeMonomial q.val s) := by
  rw [lemma153_general_m_ratio χ β hβ (pow_ne_zero k q.property.ne_zero)
    (pow_ne_zero l q.property.ne_zero) s hs hM,← pow_add,
    lemma153_prime_divisor_set_power q (k+l) hkl,prod_singleton]
  rw [(lemma153_base_closed_hasSum χ β hβ q.property (lemma32PrimeMonomial q.val s)
    ((lemma152_monomial_norm_radius q s hs).trans_lt lemma83_regular_radius_lt_one)).tsum_eq]

end ZhangLS.Spec
