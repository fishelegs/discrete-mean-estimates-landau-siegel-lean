import ZhangLS.Spec.Lemma153GeneralMEuler
import ZhangLS.Spec.Lemma152ActualContinuation
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma153_general_m_local_product_agreement {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (d l : ℕ) (q : Nat.Primes)
    (s : ℂ) (hs : 1 < s.re) :
    lemma153GeneralMPrimeFactor χ β d l q s *
        (1-lemma32PrimeMonomial q.val (s+β 0))⁻¹ *
        (1-lemma32PrimeMonomial q.val (s+β 1))⁻¹ =
      (∑' n : ℕ, lemma152Coefficient χ β d l (q.val^n)*lemma32PrimeMonomial q.val s^n) *
        ((1-lemma32PrimeMonomial q.val s)⁻¹ *
          (1-χ.evalNat q.val*lemma32PrimeMonomial q.val s)⁻¹) := by
  let a := (q.val:ℂ)^(-β 0)
  let b := (q.val:ℂ)^(-β 1)
  let x := lemma32PrimeMonomial q.val s
  have hx : ‖x‖ < 1 := (lemma152_monomial_norm_half q.property s hs.le).trans_lt (by norm_num)
  have hvx : ‖χ.evalNat q.val*x‖ < 1 := lt_of_le_of_lt
    (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hx
  have hax : 1-a*x ≠ 0 := lemma83_one_sub_ne_zero (by
    simpa [a,norm_mul,lemma83_cpow_shift_norm q.property.pos _ (hβ 0)] using hx)
  have hbx : 1-b*x ≠ 0 := lemma83_one_sub_ne_zero (by
    simpa [b,norm_mul,lemma83_cpow_shift_norm q.property.pos _ (hβ 1)] using hx)
  have hxn := lemma83_one_sub_ne_zero hx
  have hvxn := lemma83_one_sub_ne_zero hvx
  have hc := lemma153_general_m_local_agreement χ β hβ d l q s (by linarith)
  have hm (i : Fin 2) : lemma32PrimeMonomial q.val (s+β i) =
      (q.val:ℂ)^(-β i)*x := by
    rw [lemma152_monomial_add,lemma32_prime_monomial_eq_cpow q.property.pos (β i)]
    simp [x,mul_comm]
  simp only [hm]
  rw [← hc]
  change (lemma152LocalRemoval a b (χ.evalNat q.val) x *
      (∑' n : ℕ, lemma152Coefficient χ β d l (q.val^n)*x^n)) * (1-a*x)⁻¹ * (1-b*x)⁻¹ =
        (∑' n : ℕ, lemma152Coefficient χ β d l (q.val^n)*x^n) * ((1-x)⁻¹*(1-χ.evalNat q.val*x)⁻¹)
  have hvxn' : 1-x*χ.evalNat q.val ≠ 0 := by simpa [mul_comm] using hvxn
  unfold lemma152LocalRemoval
  repeat' field_simp [hax,hbx,hxn,hvxn,hvxn',mul_comm]
  all_goals ring

/-- The general d,l product is the actual Section15 M₁ continuation. Equality
is proved from the original absolutely convergent Dirichlet series, never by
totalizing a zeta/L quotient on the continuation half-plane. -/
lemma lemma153_general_m_actual_continuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) {d l : ℕ} (hd : d ≠ 0) (hl : l ≠ 0) :
    Lemma152Continuation χ β d l (lemma153GeneralMEulerProduct χ β d l) := by
  refine ⟨lemma153_general_m_analyticOnNhd χ β hβ hd hl,?_⟩
  intro s hs
  refine ⟨lemma153_general_m_lseries_summable χ β d l hβ s hs,?_⟩
  have hs0 : 1 < (s+β 0).re := by simpa [hβ 0] using hs
  have hs1 : 1 < (s+β 1).re := by simpa [hβ 1] using hs
  have hm := (lemma153_general_m_euler_multipliable χ β hβ hd hl s (by linarith)).hasProd
  have hz0 := lemma32_actual_zeta_monomial_euler_hasProd (s+β 0) hs0
  have hz1 := lemma32_actual_zeta_monomial_euler_hasProd (s+β 1) hs1
  have hz := lemma32_actual_zeta_monomial_euler_hasProd s hs
  have hl := lemma32_actual_L_monomial_euler_hasProd χ s hs
  have hc := lemma153_general_m_dirichlet_series_hasProd χ β d l hβ s hs
  have hleft := (hm.mul hz0).mul hz1
  have hright := hc.mul (hz.mul hl)
  have heq := hleft.congr_fun (fun q => (lemma153_general_m_local_product_agreement χ β hβ d l q s hs).symm)
  have he := heq.unique hright
  change lemma153GeneralMEulerProduct χ β d l s*riemannZeta (s+β 0)*riemannZeta (s+β 1) =
      lemma152DirichletSeries χ β d l s*(riemannZeta s*dirichletLFunction χ s) at he
  rw [he]
  ring

@[simp] lemma lemma153_general_m_baseline_prime {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (q : Nat.Primes) (s : ℂ) :
    lemma153GeneralMPrimeFactor χ β 1 1 q s = lemma152PrimeFactor χ β q s := by
  simp [lemma153GeneralMPrimeFactor,q.property.not_dvd_one]

@[simp] lemma lemma153_general_m_baseline {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (s : ℂ) :
    lemma153GeneralMEulerProduct χ β 1 1 s = lemma152EulerProduct χ β s := by
  unfold lemma153GeneralMEulerProduct lemma152EulerProduct
  apply tprod_congr
  intro q
  exact lemma153_general_m_baseline_prime χ β q s

end ZhangLS.Spec
