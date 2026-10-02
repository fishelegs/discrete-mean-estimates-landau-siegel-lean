import ZhangLS.Spec.Lemma152DirichletSeries
import ZhangLS.Spec.Lemma152EulerProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma152_monomial_add (p : ℕ) (s t : ℂ) :
    lemma32PrimeMonomial p (s+t) = lemma32PrimeMonomial p s*lemma32PrimeMonomial p t := by
  unfold lemma32PrimeMonomial
  rw [← Complex.exp_add]
  congr 1
  ring

lemma lemma152_monomial_off_diagonal {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (s : ℂ) (hs : 1 < s.re) :
    lemma32PrimeMonomial p s ≠ χ.evalNat p*(p:ℂ)⁻¹ := by
  by_cases hv : χ.evalNat p = 0
  · rw [hv,zero_mul]
    exact Complex.exp_ne_zero _
  have hv1 : ‖χ.evalNat p‖ = 1 := by
    rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (p:ZMod D) with h | h | h
    · exact False.elim (hv h)
    · rw [show χ.evalNat p = 1 from h,norm_one]
    · rw [show χ.evalNat p = -1 from h,norm_neg,norm_one]
  have hnorm : ‖lemma32PrimeMonomial p s‖ < ‖χ.evalNat p*(p:ℂ)⁻¹‖ := by
    rw [norm_mul,hv1,one_mul,norm_inv,Complex.norm_natCast,
      lemma83_prime_monomial_norm_rpow hp.pos,← Real.rpow_neg_one]
    exact Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast hp.one_lt) (by linarith)
  exact fun h => (ne_of_lt hnorm) (congrArg norm h)

lemma lemma152_local_product_agreement {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (q : Nat.Primes)
    (s : ℂ) (hs : 1 < s.re) :
    lemma152PrimeFactor χ β q s *
        (1-lemma32PrimeMonomial q.val (s+β 0))⁻¹ *
        (1-lemma32PrimeMonomial q.val (s+β 1))⁻¹ =
      (∑' n : ℕ, lemma152Coefficient χ β 1 1 (q.val^n)*lemma32PrimeMonomial q.val s^n) *
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
  have hc := lemma152_actual_local_correction χ β hβ q.property x hx
    (lemma152_monomial_off_diagonal χ q.property s hs)
  have hm (i : Fin 2) : lemma32PrimeMonomial q.val (s+β i) =
      (q.val:ℂ)^(-β i)*x := by
    rw [lemma152_monomial_add,lemma32_prime_monomial_eq_cpow q.property.pos (β i)]
    simp [x,mul_comm]
  simp only [hm]
  rw [lemma152PrimeFactor,lemma32_prime_monomial_eq_cpow q.property.pos (β 0),
    lemma32_prime_monomial_eq_cpow q.property.pos (β 1)]
  change lemma152LocalCorrection a b (q.val:ℂ)⁻¹ (χ.evalNat q.val) x *
      (1-a*x)⁻¹*(1-b*x)⁻¹ = _
  rw [← hc]
  change (lemma152LocalRemoval a b (χ.evalNat q.val) x *
      (∑' n : ℕ, lemma152Coefficient χ β 1 1 (q.val^n)*x^n)) * (1-a*x)⁻¹ * (1-b*x)⁻¹ =
        (∑' n : ℕ, lemma152Coefficient χ β 1 1 (q.val^n)*x^n) * ((1-x)⁻¹*(1-χ.evalNat q.val*x)⁻¹)
  have hvxn' : 1-x*χ.evalNat q.val ≠ 0 := by simpa [mul_comm] using hvxn
  unfold lemma152LocalRemoval
  repeat' field_simp [hax,hbx,hxn,hvxn,hvxn',mul_comm]
  all_goals ring

/-- The product is the actual M₁ continuation, including at s=1 and shifted
zeta zeros. Its agreement is proved only where all input series converge. -/
lemma lemma152_actual_continuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) :
    Lemma152Continuation χ β 1 1 (lemma152EulerProduct χ β) := by
  refine ⟨lemma152_euler_product_analyticOnNhd χ β hβ,?_⟩
  intro s hs
  refine ⟨lemma152_lseries_summable χ β hβ s hs,?_⟩
  have hs0 : 1 < (s+β 0).re := by simpa [hβ 0] using hs
  have hs1 : 1 < (s+β 1).re := by simpa [hβ 1] using hs
  have hm := (lemma152_euler_product_multipliable χ β hβ s (by linarith)).hasProd
  have hz0 := lemma32_actual_zeta_monomial_euler_hasProd (s+β 0) hs0
  have hz1 := lemma32_actual_zeta_monomial_euler_hasProd (s+β 1) hs1
  have hz := lemma32_actual_zeta_monomial_euler_hasProd s hs
  have hl := lemma32_actual_L_monomial_euler_hasProd χ s hs
  have hc := lemma152_dirichlet_series_hasProd χ β hβ s hs
  have hleft := (hm.mul hz0).mul hz1
  have hright := hc.mul (hz.mul hl)
  have heq := hleft.congr_fun (fun q => (lemma152_local_product_agreement χ β hβ q s hs).symm)
  have he := heq.unique hright
  change lemma152EulerProduct χ β s*riemannZeta (s+β 0)*riemannZeta (s+β 1) =
      lemma152DirichletSeries χ β 1 1 s*(riemannZeta s*dirichletLFunction χ s) at he
  rw [he]
  ring

end ZhangLS.Spec
