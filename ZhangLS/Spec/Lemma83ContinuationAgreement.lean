import ZhangLS.Spec.Lemma83DirichletConvergence
import ZhangLS.Spec.Lemma83ExceptionalProduct
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 700000

noncomputable def lemma83AllPrimeFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (j : Fin 3) (d r : ℕ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  if q.val ∣ d*r then lemma83ExceptionalPrimeFactor χ (β j) r q.val s
  else lemma83RegularPrimeFactor χ β j q s

lemma lemma83_exceptional_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d r : ℕ) (hdr : d*r ≠ 0) (s : ℂ) :
    HasProd (fun q : Nat.Primes => if q.val ∣ d*r then
      lemma83ExceptionalPrimeFactor χ β r q.val s else 1)
      (lemma83ExceptionalEulerProduct χ β d r s) := by
  have hh : HasProd (fun q : Nat.Primes => if q.val ∣ d*r then
      lemma83ExceptionalPrimeFactor χ β r q.val s else 1)
      (∏ q ∈ (d*r).primeFactors.subtype Nat.Prime, if q.val ∣ d*r then
        lemma83ExceptionalPrimeFactor χ β r q.val s else 1) := by
    apply hasProd_prod_of_ne_finset_one
    intro q hq
    have hn : ¬q.val ∣ d*r := by
      intro h
      exact hq (mem_subtype.mpr (Nat.mem_primeFactors.mpr ⟨q.property,h,hdr⟩))
    rw [if_neg hn]
  have he : (∏ q ∈ (d*r).primeFactors.subtype Nat.Prime, if q.val ∣ d*r then
      lemma83ExceptionalPrimeFactor χ β r q.val s else 1) =
      lemma83ExceptionalEulerProduct χ β d r s := by
    calc
      _ = ∏ q ∈ (d*r).primeFactors.subtype Nat.Prime,
          lemma83ExceptionalPrimeFactor χ β r q.val s := by
        apply prod_congr rfl
        intro q hq
        rw [if_pos (Nat.dvd_of_mem_primeFactors (mem_subtype.mp hq))]
      _ = _ := by
        unfold lemma83ExceptionalEulerProduct
        exact Finset.prod_subtype_of_mem
          (fun q : ℕ => lemma83ExceptionalPrimeFactor χ β r q s)
          (fun q hq => Nat.prime_of_mem_primeFactors hq)
  rwa [he] at hh

lemma lemma83_all_factors_hasProd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ)
    (hdr : d*r ≠ 0) (s : ℂ) (hs : 9/10 ≤ s.re) :
    HasProd (fun q : Nat.Primes => lemma83AllPrimeFactor χ β j d r q s)
      (lemma83EulerCorrection χ β j d r s) := by
  have hh := (lemma83_regular_euler_product_multipliable χ β hβ j
    (fun q => ¬q.val ∣ d*r) s hs).hasProd.mul (lemma83_exceptional_hasProd χ (β j) d r hdr s)
  apply hh.congr_fun
  intro q
  simp only [lemma83RestrictedRegularFactor,lemma83AllPrimeFactor]
  split_ifs <;> simp_all

lemma lemma83_prime_monomial_add (p : ℕ) (s t : ℂ) :
    lemma32PrimeMonomial p (s+t) = lemma32PrimeMonomial p s * lemma32PrimeMonomial p t := by
  unfold lemma32PrimeMonomial
  rw [← Complex.exp_add]
  congr 1
  ring

lemma lemma83_character_monomial_lt_reciprocal {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    ‖χ.evalNat q.val*lemma32PrimeMonomial q.val s‖ < (q.val:ℝ)⁻¹ := by
  have hn : ‖χ.evalNat q.val*lemma32PrimeMonomial q.val s‖ ≤ (q.val:ℝ)^(-s.re) := by
    rw [norm_mul]
    calc
      _ ≤ 1*‖lemma32PrimeMonomial q.val s‖ :=
        mul_le_mul_of_nonneg_right (χ.evalNat_norm_le_one _) (norm_nonneg _)
      _ = _ := by rw [one_mul,lemma83_prime_monomial_norm_rpow q.property.pos]
  apply hn.trans_lt
  rw [← Real.rpow_neg_one]
  exact Real.rpow_lt_rpow_of_exponent_lt (by exact_mod_cast q.property.one_lt) (by linarith)

lemma lemma83_local_series_correction {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ)
    (q : Nat.Primes) (s : ℂ) (hs : 1 < s.re) :
    ((1-χ.evalNat q.val*lemma32PrimeMonomial q.val (s+β (j+1))) *
      (1-χ.evalNat q.val*lemma32PrimeMonomial q.val (s+β (j+2))) /
        (1-χ.evalNat q.val*lemma32PrimeMonomial q.val s)) *
      (∑' e : ℕ, LSeries.term (fun n => χ.evalNat n*lemma83Xi β j n d r) s (q.val^e)) =
      lemma83AllPrimeFactor χ β j d r q s := by
  let x := χ.evalNat q.val*lemma32PrimeMonomial q.val s
  have hx : ‖x‖ < 1 := (lemma83_character_monomial_half χ q s hs.le).trans_lt (by norm_num)
  have hxt : x ≠ (q.val:ℂ)^(-(1-β j)) := by
    intro he
    have hh := lemma83_character_monomial_lt_reciprocal χ q s hs
    change ‖x‖ < _ at hh
    rw [he,lemma83_cpow_tail_norm q.property.pos _ (hβ j)] at hh
    exact lt_irrefl _ hh
  have hremove : (1-χ.evalNat q.val*lemma32PrimeMonomial q.val (s+β (j+1))) *
      (1-χ.evalNat q.val*lemma32PrimeMonomial q.val (s+β (j+2))) /
        (1-χ.evalNat q.val*lemma32PrimeMonomial q.val s) =
      lemma83LocalRemoval ((q.val:ℂ)^(-β (j+1))) ((q.val:ℂ)^(-β (j+2))) x := by
    rw [lemma83_prime_monomial_add,lemma83_prime_monomial_add,
      lemma32_prime_monomial_eq_cpow q.property.pos (β (j+1)),
      lemma32_prime_monomial_eq_cpow q.property.pos (β (j+2))]
    dsimp [lemma83LocalRemoval,x]
    ring
  rw [hremove]
  simp only [lemma83_xi_prime_power_term χ β j d r q.property.pos]
  change _ * (∑' e : ℕ, lemma83Xi β j (q.val^e) d r*x^e) = _
  unfold lemma83AllPrimeFactor
  by_cases hq : q.val ∣ d*r
  · rw [if_pos hq]
    unfold lemma83ExceptionalPrimeFactor
    by_cases hqr : q.val ∣ r
    · rw [if_pos hqr,lemma32_prime_monomial_eq_cpow q.property.pos]
      exact lemma83_xi_r_correction β hβ j q.property d r hqr x hx
    · rw [if_neg hqr,lemma32_prime_monomial_eq_cpow q.property.pos]
      exact lemma83_xi_d_correction β hβ j q.property d r
        ((q.property.dvd_mul.mp hq).resolve_right hqr) hqr x hx
  · rw [if_neg hq]
    unfold lemma83RegularPrimeFactor
    simp only [lemma32_prime_monomial_eq_cpow q.property.pos]
    simpa only [x,lemma32_prime_monomial_eq_cpow q.property.pos] using
      lemma83_xi_regular_correction β hβ j q.property d r hq x hx hxt

lemma lemma83_local_cross_multiply (A B C X : ℂ)
    (hA : A ≠ 0) (hB : B ≠ 0) (hC : C ≠ 0) :
    X*A⁻¹ = ((B*C/A)*X)*(B⁻¹*C⁻¹) := by
  field_simp

/-- Agreement with the actual ξ/L expression in its convergence half-plane.
This identifies the constructed analytic continuation without totalized division. -/
lemma lemma83_continuation_agreement {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ)
    (hdr : d*r ≠ 0) (s : ℂ) (hs : 1 < s.re) :
    lemma83EulerCorrection χ β j d r s * dirichletLFunction χ (s+β (j+1)) *
      dirichletLFunction χ (s+β (j+2)) =
      dirichletLFunction χ s * lemma83XiDirichletSeries χ β j d r s := by
  have hshift (i : Fin 3) : 1 < (s+β i).re := by simpa [hβ i] using hs
  have hleft := (lemma83_xi_euler_hasProd χ β hβ j d r s hs).mul
    (lemma32_actual_L_monomial_euler_hasProd χ s hs)
  have hright := (lemma83_all_factors_hasProd χ β hβ j d r hdr s (by linarith)).mul
    ((lemma32_actual_L_monomial_euler_hasProd χ (s+β (j+1)) (hshift _)).mul
      (lemma32_actual_L_monomial_euler_hasProd χ (s+β (j+2)) (hshift _)))
  have he := hleft.unique (hright.congr_fun (fun q => by
    have hn (t : ℂ) (ht : 1 < t.re) : 1-χ.evalNat q.val*lemma32PrimeMonomial q.val t ≠ 0 :=
      lemma83_one_sub_ne_zero ((lemma83_character_monomial_half χ q t ht.le).trans_lt (by norm_num))
    rw [← lemma83_local_series_correction χ β hβ j d r q s hs]
    exact lemma83_local_cross_multiply _ _ _ _ (hn s hs)
      (hn (s+β (j+1)) (hshift _)) (hn (s+β (j+2)) (hshift _))))
  calc
    _ = lemma83EulerCorrection χ β j d r s *
        (dirichletLFunction χ (s+β (j+1))*dirichletLFunction χ (s+β (j+2))) := by ring
    _ = lemma83XiDirichletSeries χ β j d r s * dirichletLFunction χ s := he.symm
    _ = _ := by ring

lemma lemma83_euler_is_continuation {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (hβ : ∀ i, (β i).re = 0) (j : Fin 3) (d r : ℕ) (hdr : d*r ≠ 0) :
    Lemma83Continuation χ β j d r (lemma83EulerCorrection χ β j d r) := by
  refine ⟨lemma83_euler_correction_analyticOnNhd χ β hβ j d r,?_⟩
  intro s hs
  exact ⟨lemma83_xi_lseries_summable χ β hβ j d r s hs,
    lemma83_continuation_agreement χ β hβ j d r hdr s hs⟩

end ZhangLS.Spec
