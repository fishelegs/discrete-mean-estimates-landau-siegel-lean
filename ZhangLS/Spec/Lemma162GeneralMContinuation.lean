import ZhangLS.Spec.Lemma162GeneralMEuler
import ZhangLS.Spec.Lemma152ActualContinuation

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma162_general_m_local_product_agreement {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (d l : ℕ) (q : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    lemma162GeneralMPrimeFactor χ β d l q s * (1-lemma32PrimeMonomial q.val (s+β))⁻¹ =
      (∑' n : ℕ, lemma161Coefficient χ β d l (q.val^n)*lemma32PrimeMonomial q.val s^n) *
        ((1-lemma32PrimeMonomial q.val s)⁻¹ *
          (1-χ.evalNat q.val*lemma32PrimeMonomial q.val s)⁻¹) := by
  let a := (q.val:ℂ)^(-β)
  let x := lemma32PrimeMonomial q.val s
  have hx : ‖x‖ < 1 := (lemma161_monomial_norm_half q.property s hs.le).trans_lt (by norm_num)
  have hvx : ‖χ.evalNat q.val*x‖ < 1 := lt_of_le_of_lt
    (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hx
  have hax : 1-a*x ≠ 0 := lemma83_one_sub_ne_zero (by
    simpa [a,norm_mul,lemma83_cpow_shift_norm q.property.pos _ hβ] using hx)
  have hxn := lemma83_one_sub_ne_zero hx
  have hvxn := lemma83_one_sub_ne_zero hvx
  have hc := lemma162_general_m_local_agreement χ β hβ d l q s (by linarith)
  have hm : lemma32PrimeMonomial q.val (s+β) = a*x := by
    rw [lemma152_monomial_add,lemma32_prime_monomial_eq_cpow q.property.pos β]
    simp [a,x,mul_comm]
  rw [hm,← hc]
  change ((1-a*x)/((1-x)*(1-χ.evalNat q.val*x)) *
      (∑' n : ℕ, lemma161Coefficient χ β d l (q.val^n)*x^n)) * (1-a*x)⁻¹ =
        (∑' n : ℕ, lemma161Coefficient χ β d l (q.val^n)*x^n) * ((1-x)⁻¹*(1-χ.evalNat q.val*x)⁻¹)
  have hvxn' : 1-x*χ.evalNat q.val ≠ 0 := by simpa [mul_comm] using hvxn
  repeat' field_simp [hax,hxn,hvxn,hvxn',mul_comm]

/-- The genuinely convergent original Dirichlet series gives the constructed
holomorphic M₂ on its overlap, without taking Euler factorization as an axiom. -/
lemma lemma162_general_m_actual_continuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) {d l : ℕ} (hd : d ≠ 0) (hl : l ≠ 0) :
    Lemma161Continuation χ β d l (lemma162GeneralMEulerProduct χ β d l) := by
  refine ⟨lemma162_general_m_analyticOnNhd χ β hβ hd hl,?_⟩
  intro s hs
  refine ⟨lemma162_general_m_lseries_summable χ β d l hβ s hs,?_⟩
  have hsβ : 1 < (s+β).re := by simpa [hβ] using hs
  have hm := (lemma162_general_m_euler_multipliable χ β hβ hd hl s (by linarith)).hasProd
  have hzβ := lemma32_actual_zeta_monomial_euler_hasProd (s+β) hsβ
  have hz := lemma32_actual_zeta_monomial_euler_hasProd s hs
  have hl := lemma32_actual_L_monomial_euler_hasProd χ s hs
  have hc := lemma162_general_m_dirichlet_series_hasProd χ β d l hβ s hs
  have he := ((hm.mul hzβ).congr_fun
    (fun q => (lemma162_general_m_local_product_agreement χ β hβ d l q s hs).symm)).unique (hc.mul (hz.mul hl))
  change lemma162GeneralMEulerProduct χ β d l s*riemannZeta (s+β) =
      lemma161DirichletSeries χ β d l s*(riemannZeta s*dirichletLFunction χ s) at he
  rw [he]
  ring

@[simp] lemma lemma162_general_m_baseline_prime {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (q : Nat.Primes) (s : ℂ) :
    lemma162GeneralMPrimeFactor χ β 1 1 q s = lemma161PrimeFactor χ β q s := by
  simp [lemma162GeneralMPrimeFactor,q.property.not_dvd_one]

@[simp] lemma lemma162_general_m_baseline {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (s : ℂ) :
    lemma162GeneralMEulerProduct χ β 1 1 s = lemma161EulerProduct χ β s := by
  unfold lemma162GeneralMEulerProduct lemma161EulerProduct
  apply tprod_congr
  intro q
  exact lemma162_general_m_baseline_prime χ β q s

end ZhangLS.Spec
