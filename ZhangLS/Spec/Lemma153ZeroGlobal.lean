import ZhangLS.Spec.Lemma153ActualContinuation
import ZhangLS.Spec.Lemma153ZeroCenter
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2500000

lemma lemma153_zero_parameters : Lemma153SmallParameters (fun _ => 0) 0 := by
  constructor <;> simp

lemma lemma153_zero_baseline_expression (u v : ℂ) (hu : ‖u‖ < 1) (hv : v = 1 ∨ v = -1) :
    1+(1-v*(1-v*u)/(1-u))*u/(1-u) = lemma153ZeroB u v := by
  have hun := lemma83_one_sub_ne_zero hu
  have hup : 1+u ≠ 0 := by simpa using lemma83_one_sub_ne_zero (show ‖-u‖ < 1 by simpa using hu)
  have hu2 : 1-u^2 ≠ 0 := by rw [show 1-u^2 = (1-u)*(1+u) by ring]; exact mul_ne_zero hun hup
  unfold lemma153ZeroB
  rcases hv with rfl | rfl
  all_goals repeat' field_simp [hun,hup,hu2,mul_comm]
  all_goals ring

lemma lemma153_actual_zero_baseline {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q : Nat.Primes) (hqd : ¬q.val ∣ D) :
    lemma153Baseline χ (fun _ => 0) 0 q = lemma153ZeroB (q.val:ℂ)⁻¹ (χ.evalNat q.val) := by
  have hu : ‖(q.val:ℂ)⁻¹‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr q.property.pos)).mpr (by exact_mod_cast q.property.one_lt)
  unfold lemma153Baseline
  simp only [sub_zero]
  rw [lemma83_prime_monomial_one q.property.pos]
  have hb := lemma153_base_closed_hasSum χ (fun _ => 0) (fun _ => rfl) q.property (q.val:ℂ)⁻¹ hu
  have hz := lemma153_zero_base_hasSum χ q.property (q.val:ℂ)⁻¹ hu
  rw [hb.unique hz]
  exact lemma153_zero_baseline_expression _ _ hu (lemma32_character_prime_cases_of_not_dvd χ q.property hqd)

lemma lemma153_zero_c_expression (u v : ℂ) (hu : ‖u‖ < 1) (hv : v = 1 ∨ v = -1) :
    lemma153ZeroB u v+(1-v*u)*(v/(1-u))*u*lemma153ZeroC u = lemma153ZeroC u := by
  rw [lemma153_zero_b_compatibility u v hu hv]
  unfold lemma153ZeroE lemma153ZeroC
  ring

lemma lemma153_kappa_rational_zero (u : ℂ) (hu : 1-u ≠ 0) :
    lemma152KappaRational 1 1 u = (1-u)⁻¹ := by
  unfold lemma152KappaRational
  simp only [one_mul]
  field_simp

lemma lemma153_unramified_zero_center {D : ℕ} (χ : RealPrimitiveCharacter D)
    (q : Nat.Primes) (hqd : ¬q.val ∣ D) :
    lemma153UnramifiedPrimeFactor χ (fun _ => 0) 0 q 1 =
      (1-(q.val:ℂ)^(-2:ℤ))^2/(1-χ.evalNat q.val*(q.val:ℂ)^(-2:ℤ)) := by
  have hu : ‖(q.val:ℂ)⁻¹‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr q.property.pos)).mpr (by exact_mod_cast q.property.one_lt)
  have hv := lemma32_character_prime_cases_of_not_dvd χ q.property hqd
  unfold lemma153UnramifiedPrimeFactor
  simp only [sub_zero,neg_zero,Complex.cpow_zero,mul_one]
  rw [lemma83_prime_monomial_one q.property.pos,lemma153_actual_zero_baseline χ q hqd,
    lemma153_lambda_zero_shifts χ q.property,
    lemma153_kappa_rational_zero _ (lemma83_one_sub_ne_zero hu)]
  change lemma153ShiftedLocalCorrection (lemma153ZeroB (q.val:ℂ)⁻¹ (χ.evalNat q.val))
    (lemma153ZeroB (q.val:ℂ)⁻¹ (χ.evalNat q.val)+(1-χ.evalNat q.val*(q.val:ℂ)⁻¹)*
      (χ.evalNat q.val/(1-(q.val:ℂ)⁻¹))*(q.val:ℂ)⁻¹*lemma153ZeroC (q.val:ℂ)⁻¹)
    ((1-(χ.evalNat q.val/(1-(q.val:ℂ)⁻¹))*(q.val:ℂ)⁻¹)*lemma153ZeroC (q.val:ℂ)⁻¹)
    (lemma153ZeroC (q.val:ℂ)⁻¹) (1-χ.evalNat q.val*(q.val:ℂ)⁻¹) (χ.evalNat q.val) (q.val:ℂ)⁻¹ = _
  rw [lemma153_zero_c_expression _ _ hu hv]
  have hE : (1-(χ.evalNat q.val/(1-(q.val:ℂ)⁻¹))*(q.val:ℂ)⁻¹)*lemma153ZeroC (q.val:ℂ)⁻¹ =
      lemma153ZeroE (q.val:ℂ)⁻¹ (χ.evalNat q.val) := by
    unfold lemma153ZeroC lemma153ZeroE
    ring
  rw [hE,lemma153_zero_center_local_value _ _ hu hv]
  simp [zpow_neg,zpow_ofNat]

lemma lemma153_prime_zero_center {D : ℕ} (χ : RealPrimitiveCharacter D) (q : Nat.Primes) :
    lemma153PrimeFactor χ (fun _ => 0) 0 q 1 =
      if q.val ∣ D then (1-(q.val:ℂ)⁻¹)^2 else
        (1-(q.val:ℂ)^(-2:ℤ))^2/(1-χ.evalNat q.val*(q.val:ℂ)^(-2:ℤ)) := by
  unfold lemma153PrimeFactor
  split_ifs with hq
  · rw [lemma83_prime_monomial_one q.property.pos]
  · exact lemma153_unramified_zero_center χ q hq

noncomputable def lemma153MainTerm {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  (Nat.totient D:ℂ)^2/(D:ℂ)^2 *
    ∏' q : {q : Nat.Primes // ¬q.val ∣ D},
      (1-(q.val.val:ℂ)^(-2:ℤ))^2/(1-χ.evalNat q.val.val*(q.val.val:ℂ)^(-2:ℤ))

lemma lemma153_ramified_totient_product {D : ℕ} (hD : D ≠ 0) :
    (∏ q ∈ lemma153PrimeDivisorSet D, (1-(q.val:ℂ)⁻¹)^2) =
      (Nat.totient D:ℂ)^2/(D:ℂ)^2 := by
  have heq : (∏ q ∈ lemma153PrimeDivisorSet D, (1-(q.val:ℂ)⁻¹)) =
      ∏ p ∈ D.primeFactors, (1-(p:ℂ)⁻¹) := by
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
  have ht : (Nat.totient D:ℂ) = (D:ℂ)*(∏ p ∈ D.primeFactors, (1-(p:ℂ)⁻¹)) := by
    have hh := congrArg (fun r : ℚ => (r:ℂ)) (Nat.totient_eq_mul_prod_factors D)
    push_cast at hh
    exact hh
  have hDn : (D:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hD
  have hp : (∏ p ∈ D.primeFactors, (1-(p:ℂ)⁻¹)) = (Nat.totient D:ℂ)/(D:ℂ) := by
    apply (eq_div_iff hDn).mpr
    simpa [mul_comm] using ht.symm
  rw [prod_pow,heq,hp,div_pow]

/-- The exact global value of the zero-shift corrected product, including
Euler's totient factor and every ramification exclusion in the paper. -/
lemma lemma153_zero_product_equals_main {D : ℕ} (hD : D ≠ 0)
    (χ : RealPrimitiveCharacter D) :
    lemma153EulerProduct χ (fun _ => 0) 0 1 = lemma153MainTerm χ := by
  let g : Nat.Primes → ℂ := fun q => if q.val ∣ D then 1 else
    (1-(q.val:ℂ)^(-2:ℤ))^2/(1-χ.evalNat q.val*(q.val:ℂ)^(-2:ℤ))
  have hmajor : Summable (fun q : Nat.Primes => 100000*(q.val:ℝ)^(-(3/2:ℝ))) :=
    ((Real.summable_nat_rpow.mpr (by norm_num : -(3/2:ℝ)< -1)).subtype Nat.Prime).mul_left 100000
  have hgbound (q : Nat.Primes) : ‖g q-1‖ ≤ 100000*(q.val:ℝ)^(-(3/2:ℝ)) := by
    by_cases hq : q.val ∣ D
    · simp only [g,if_pos hq,sub_self,norm_zero]
      positivity
    · dsimp [g]
      rw [if_neg hq,← lemma153_unramified_zero_center χ q hq]
      exact lemma153_unramified_factor_error χ (fun _ => 0) 0 lemma153_zero_parameters q 1 (by norm_num)
  have hgs : Summable (fun q : Nat.Primes => ‖g q-1‖) :=
    hmajor.of_nonneg_of_le (fun _ => norm_nonneg _) hgbound
  have hgm : Multipliable g := by simpa only [add_sub_cancel] using multipliable_one_add_of_summable hgs
  have hgval : (∏' q : Nat.Primes, g q) =
      ∏' q : {q : Nat.Primes // ¬q.val ∣ D},
        (1-(q.val.val:ℂ)^(-2:ℤ))^2/(1-χ.evalNat q.val.val*(q.val.val:ℂ)^(-2:ℤ)) := by
    rw [← tprod_subtype_eq_of_mulSupport_subset (f := g) (s := {q : Nat.Primes | ¬q.val ∣ D}) (by
      intro q hq
      change ¬q.val ∣ D
      intro hd
      exact hq (by simp [g,hd]))]
    apply tprod_congr
    intro q
    dsimp [g]
    exact if_neg q.property
  have hf := lemma153_finite_ite_hasProd (lemma153PrimeDivisorSet D)
    (fun q : Nat.Primes => (1-(q.val:ℂ)⁻¹)^2)
  have hp : HasProd (fun q : Nat.Primes => lemma153PrimeFactor χ (fun _ => 0) 0 q 1)
      ((∏ q ∈ lemma153PrimeDivisorSet D, (1-(q.val:ℂ)⁻¹)^2)*(∏' q : Nat.Primes, g q)) := by
    apply (hf.mul hgm.hasProd).congr_fun
    intro q
    simp only [lemma153_mem_prime_divisor_set hD q]
    rw [lemma153_prime_zero_center]
    by_cases hq : q.val ∣ D <;> simp [g,hq]
  have he := hp.unique (lemma153_euler_product_multipliable hD χ (fun _ => 0) 0
    lemma153_zero_parameters 1 (by norm_num)).hasProd
  unfold lemma153MainTerm lemma153EulerProduct
  rw [← he,lemma153_ramified_totient_product hD,hgval]

end ZhangLS.Spec
