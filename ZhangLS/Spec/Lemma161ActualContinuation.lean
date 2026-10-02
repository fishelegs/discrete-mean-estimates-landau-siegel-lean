import ZhangLS.Spec.Lemma161DirichletSeries
import ZhangLS.Spec.Lemma161EulerProduct
import ZhangLS.Spec.Lemma152ActualContinuation

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma161_local_product_agreement {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (q : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    lemma161PrimeFactor χ β q s * (1-lemma32PrimeMonomial q.val (s+β))⁻¹ =
      (∑' n : ℕ, lemma161Coefficient χ β 1 1 (q.val^n)*lemma32PrimeMonomial q.val s^n) *
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
  have hc := lemma161_actual_local_correction χ β hβ q.property x hx
  have hm : lemma32PrimeMonomial q.val (s+β) = a*x := by
    rw [lemma152_monomial_add,lemma32_prime_monomial_eq_cpow q.property.pos β]
    simp [a,x,mul_comm]
  rw [hm,lemma161PrimeFactor,lemma32_prime_monomial_eq_cpow q.property.pos β]
  change lemma152LocalCorrection a 0 (q.val:ℂ)⁻¹ (χ.evalNat q.val) x * (1-a*x)⁻¹ = _
  rw [← hc]
  change ((1-a*x)/((1-x)*(1-χ.evalNat q.val*x)) *
      (∑' n : ℕ, lemma161Coefficient χ β 1 1 (q.val^n)*x^n)) * (1-a*x)⁻¹ =
        (∑' n : ℕ, lemma161Coefficient χ β 1 1 (q.val^n)*x^n) * ((1-x)⁻¹*(1-χ.evalNat q.val*x)⁻¹)
  have hvxn' : 1-x*χ.evalNat q.val ≠ 0 := by simpa [mul_comm] using hvxn
  repeat' field_simp [hax,hxn,hvxn,hvxn',mul_comm]
  all_goals ring

/-- The genuinely convergent original Dirichlet series gives the constructed
holomorphic M₂ on its overlap, without taking Euler factorization as an axiom. -/
lemma lemma161_actual_continuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) :
    Lemma161Continuation χ β 1 1 (lemma161EulerProduct χ β) := by
  refine ⟨lemma161_euler_product_analyticOnNhd χ β hβ,?_⟩
  intro s hs
  refine ⟨lemma161_lseries_summable χ β hβ s hs,?_⟩
  have hsβ : 1 < (s+β).re := by simpa [hβ] using hs
  have hm := (lemma161_euler_product_multipliable χ β hβ s (by linarith)).hasProd
  have hzβ := lemma32_actual_zeta_monomial_euler_hasProd (s+β) hsβ
  have hz := lemma32_actual_zeta_monomial_euler_hasProd s hs
  have hl := lemma32_actual_L_monomial_euler_hasProd χ s hs
  have hc := lemma161_dirichlet_series_hasProd χ β hβ s hs
  have he := ((hm.mul hzβ).congr_fun
    (fun q => (lemma161_local_product_agreement χ β hβ q s hs).symm)).unique (hc.mul (hz.mul hl))
  change lemma161EulerProduct χ β s*riemannZeta (s+β) =
      lemma161DirichletSeries χ β 1 1 s*(riemannZeta s*dirichletLFunction χ s) at he
  rw [he]
  ring

end ZhangLS.Spec
