import ZhangLS.Spec.Lemma153ZeroGlobal
import ZhangLS.Spec.Lemma83FinitePrimeBounds
/-! Contour-usable ramified bound: in Re(s)≥1−1/log D, the finite ramified
part is polynomial in 1+log log D, rather than an unusable coarse D^ε bound. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma153_ramified_strip_monomial {D p : ℕ} (hD : 2≤D) (hp : p.Prime)
    (hpD : p ∣ D) (s : ℂ) (hs : 1-(Real.log D)⁻¹ ≤ s.re) :
    ‖lemma32PrimeMonomial p s‖ ≤ 3/(p:ℝ) := by
  have hD0 : 0<D := by omega
  have hp0 : (0:ℝ)<p := Nat.cast_pos.mpr hp.pos
  have hp1 : (1:ℝ)≤p := by exact_mod_cast hp.one_lt.le
  have hL : 0<Real.log D := Real.log_pos (by exact_mod_cast (show 1<D by omega))
  have hpLe : (p:ℝ)≤D := by exact_mod_cast Nat.le_of_dvd hD0 hpD
  have hlog : Real.log (p:ℝ)≤Real.log D := Real.log_le_log hp0 hpLe
  have hpow : (p:ℝ)^((Real.log D)⁻¹) ≤ 3 := by
    rw [Real.rpow_def_of_pos hp0]
    apply (Real.exp_le_exp.mpr ?_).trans Real.exp_one_lt_three.le
    exact (mul_inv_le_iff₀ hL).mpr (by simpa using hlog)
  rw [lemma83_prime_monomial_norm_rpow hp.pos]
  calc
    (p:ℝ)^(-s.re) ≤ (p:ℝ)^(-1+(Real.log D)⁻¹) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by linarith)
    _ = (p:ℝ)⁻¹*(p:ℝ)^((Real.log D)⁻¹) := by rw [Real.rpow_add hp0,Real.rpow_neg_one]
    _ ≤ (p:ℝ)⁻¹*3 := mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = 3/(p:ℝ) := by ring

lemma lemma153_ramified_strip_product {D : ℕ} (hD : 3≤D) (s : ℂ)
    (hs : 1-(Real.log D)⁻¹ ≤ s.re) :
    ‖∏ p ∈ D.primeFactors, (1-lemma32PrimeMonomial p s)^2‖ ≤
      (Real.exp (3/Real.log 2))^2*(1+Real.log (Real.log D))^18 := by
  have hprod := lemma83_prime_product_le_loglog D (by omega) 3 9
    (lemma83_log_nat_gt_one hD) (by norm_num) (by norm_num)
  calc
    _ ≤ ∏ p ∈ D.primeFactors, (1+3/(p:ℝ))^2 := by
      rw [norm_prod]
      apply prod_le_prod (fun _ _ => norm_nonneg _)
      intro p hp
      apply (lemma153_ramified_factor_bound (lemma32PrimeMonomial p s)).trans
      gcongr
      exact lemma153_ramified_strip_monomial (by omega) (Nat.prime_of_mem_primeFactors hp)
        (Nat.dvd_of_mem_primeFactors hp) s hs
    _ = (∏ p ∈ D.primeFactors, (1+3/(p:ℝ)))^2 := Finset.prod_pow _ _ _
    _ ≤ (Real.exp (3/Real.log 2)*(1+Real.log (Real.log D))^9)^2 :=
      pow_le_pow_left₀ (prod_nonneg (fun _ _ => by positivity)) hprod 2
    _ = _ := by rw [mul_pow,← pow_mul]

lemma lemma153_prime_divisor_set_prod {R : Type*} [CommMonoid R] {D : ℕ}
    (hD : D ≠ 0) (f : ℕ → R) :
    (∏ q ∈ lemma153PrimeDivisorSet D, f q.val) = ∏ p ∈ D.primeFactors, f p := by
  apply prod_bij (fun q _ => q.val)
  · intro q hq
    exact Nat.mem_primeFactors.mpr ⟨q.property,(lemma153_mem_prime_divisor_set hD q).mp hq,hD⟩
  · intro q hq r hr he
    exact Subtype.ext he
  · intro p hp
    refine ⟨⟨p,Nat.prime_of_mem_primeFactors hp⟩,?_,rfl⟩
    exact (lemma153_mem_prime_divisor_set hD _).mpr (Nat.dvd_of_mem_primeFactors hp)
  · intro q hq
    rfl

noncomputable def lemma153UnramifiedProductBound : ℝ :=
  Real.exp (∑' q : Nat.Primes, 100000*(q.val:ℝ)^(-(3/2:ℝ)))

/-- Separating the finite ramified part preserves an absolute bound for the
unramified corrected product, uniformly in the character and shifts. -/
lemma lemma153_euler_product_separated_bound {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (s : ℂ) (hs : 3/4 ≤ s.re) :
    ‖lemma153EulerProduct χ β γ s‖ ≤ lemma153UnramifiedProductBound *
      ‖∏ p ∈ D.primeFactors, (1-lemma32PrimeMonomial p s)^2‖ := by
  let g : Nat.Primes → ℂ := fun q => if q.val ∣ D then 1 else lemma153UnramifiedPrimeFactor χ β γ q s
  let u : Nat.Primes → ℝ := fun q => 100000*(q.val:ℝ)^(-(3/2:ℝ))
  have hu0 (q : Nat.Primes) : 0≤u q := by dsimp [u]; positivity
  have hum : Summable u := ((Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)).subtype Nat.Prime).mul_left 100000
  have hge (q : Nat.Primes) : ‖g q-1‖ ≤ u q := by
    dsimp [g]
    split_ifs
    · simp only [sub_self,norm_zero]
      exact hu0 q
    · exact lemma153_unramified_factor_error χ β γ hpar q s hs
  have hgm : Multipliable g := by
    have hsumm := hum.of_nonneg_of_le (fun _ => norm_nonneg _) hge
    simpa only [add_sub_cancel] using multipliable_one_add_of_summable hsumm
  have hgn : ‖∏' q : Nat.Primes, g q‖ ≤ lemma153UnramifiedProductBound := by
    apply le_of_tendsto hgm.hasProd.norm
    filter_upwards with S
    calc
      _ ≤ ∏ q ∈ S, (1+u q) := by
        apply prod_le_prod (fun _ _ => norm_nonneg _)
        intro q hq
        have hh := norm_le_norm_sub_add (g q) (1:ℂ)
        rw [norm_one] at hh
        linarith [hge q]
      _ ≤ Real.exp (∑ q ∈ S, u q) := Real.prod_one_add_le_exp_sum S hu0
      _ ≤ lemma153UnramifiedProductBound := by
        apply Real.exp_le_exp.mpr
        exact hum.sum_le_tsum S (fun q _ => hu0 q)
  have hf := lemma153_finite_ite_hasProd (lemma153PrimeDivisorSet D)
    (fun q : Nat.Primes => (1-lemma32PrimeMonomial q.val s)^2)
  have hp : HasProd (fun q : Nat.Primes => lemma153PrimeFactor χ β γ q s)
      ((∏ q ∈ lemma153PrimeDivisorSet D, (1-lemma32PrimeMonomial q.val s)^2)*(∏' q : Nat.Primes, g q)) := by
    apply (hf.mul hgm.hasProd).congr_fun
    intro q
    simp only [lemma153_mem_prime_divisor_set hD q]
    unfold lemma153PrimeFactor
    by_cases hq : q.val ∣ D <;> simp [g,hq]
  have he := hp.unique (lemma153_euler_product_multipliable hD χ β γ hpar s hs).hasProd
  change _ = lemma153EulerProduct χ β γ s at he
  rw [← he,norm_mul,lemma153_prime_divisor_set_prod hD (fun p => (1-lemma32PrimeMonomial p s)^2)]
  have hh := mul_le_mul_of_nonneg_left hgn
    (norm_nonneg (∏ p ∈ D.primeFactors, (1-lemma32PrimeMonomial p s)^2))
  simpa only [mul_comm] using hh

/-- Contour-ready bound in the thin strip used downstream. -/
lemma lemma153_euler_product_strip_bound {D : ℕ} (hD : 3≤D)
    (χ : RealPrimitiveCharacter D) (β : Fin 2 → ℂ) (γ : ℂ)
    (hpar : Lemma153SmallParameters β γ) (s : ℂ)
    (hs : 3/4 ≤ s.re) (hstrip : 1-(Real.log D)⁻¹ ≤ s.re) :
    ‖lemma153EulerProduct χ β γ s‖ ≤
      (lemma153UnramifiedProductBound*(Real.exp (3/Real.log 2))^2)*
        (1+Real.log (Real.log D))^18 := by
  apply (lemma153_euler_product_separated_bound (by omega) χ β γ hpar s hs).trans
  have hb := lemma153_ramified_strip_product hD s hstrip
  have hC : 0 ≤ lemma153UnramifiedProductBound := (Real.exp_pos _).le
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hC

end ZhangLS.Spec
