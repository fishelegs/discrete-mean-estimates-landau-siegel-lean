import ZhangLS.Spec.Lemma162Definitions
import ZhangLS.Spec.Lemma161LocalSeries

/-! All four exact local Section16 M₂ factors, derived from the original
κ₂, ξ₂ and modified λ₂. There is no cutoff at q=D and no zero-shift
replacement. This file does not assert the global Euler bridge for varpi. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma162_coefficient_d {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) (d l e : ℕ) (hpd : p ∣ d) :
    lemma161Coefficient χ β d l (p^(e+1)) =
      lemma161Kappa β (p^(e+1)) -
        (if p.Coprime l then χ.evalNat p/(1-(p:ℂ)⁻¹) else 0) *
          lemma161Kappa β (p^e) := by
  unfold lemma161Coefficient
  rw [lemma161_modified_lambda_prime_power χ β hp,if_pos hpd,one_mul,
    lemma161_xi_prime_power χ β hp,lemma161_modified_kappa_prime_power_excluded χ β hp hpd,
    lemma161_mobius_weight χ hp]
  split_ifs <;> simp

lemma lemma162_coefficient_unexcluded {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) (d l : ℕ) (hpd : ¬ p ∣ d) (e : ℕ) :
    lemma161Coefficient χ β d l (p^e) = lemma161Coefficient χ β 1 l (p^e) := by
  cases e with
  | zero => simp
  | succ e =>
    unfold lemma161Coefficient
    rw [lemma161_modified_lambda_prime_power χ β hp,if_neg hpd,
      lemma161_modified_lambda_prime_power χ β hp,if_neg hp.not_dvd_one,
      lemma161_xi_prime_power χ β hp,lemma161_xi_prime_power χ β hp,
      lemma161_modified_kappa_prime_power_unexcluded χ β hp hpd,
      lemma161_modified_kappa_prime_power_unexcluded χ β hp hp.not_dvd_one]

lemma lemma162_coefficient_l_unexcluded {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) (d l : ℕ) (hpl : ¬ p ∣ l) (e : ℕ) :
    lemma161Coefficient χ β d l (p^e) = lemma161Coefficient χ β d 1 (p^e) := by
  cases e with
  | zero => simp
  | succ e =>
    unfold lemma161Coefficient
    rw [lemma161_xi_prime_power χ β hp,lemma161_xi_prime_power χ β hp,
      if_pos (hp.coprime_iff_not_dvd.mpr hpl),if_pos (Nat.coprime_one_right p)]

lemma lemma162_coefficient_l {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) (l e : ℕ) (hpl : p ∣ l) :
    lemma161Coefficient χ β 1 l (p^(e+1)) =
      lemma161Coefficient χ β 1 1 (p^(e+1)) +
        lemma161LambdaFactor χ β p 1 * (χ.evalNat p/(1-(p:ℂ)⁻¹)) *
          lemma161Kappa β (p^e) := by
  unfold lemma161Coefficient
  rw [lemma161_modified_lambda_prime_power χ β hp,if_neg hp.not_dvd_one,
    lemma161_xi_prime_power χ β hp,lemma161_xi_prime_power χ β hp,
    if_neg (by simpa [hp.coprime_iff_not_dvd] using hpl),
    if_pos (Nat.coprime_one_right p),lemma161_mobius_weight χ hp]
  ring

lemma lemma162_coefficient_d_hasSum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hp : p.Prime) (d l : ℕ) (hpd : p ∣ d)
    (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => lemma161Coefficient χ β d l (p^n)*x^n)
      ((1-(if p.Coprime l then χ.evalNat p/(1-(p:ℂ)⁻¹) else 0)*x)*
        ((1-x)/(1-(p:ℂ)^(-β)*x))) := by
  let A := if p.Coprime l then χ.evalNat p/(1-(p:ℂ)⁻¹) else 0
  let K := (1-x)/(1-(p:ℂ)^(-β)*x)
  have hk : HasSum (fun n => lemma161Kappa β (p^n)*x^n) K :=
    lemma161_kappa_prime_power_hasSum β hp x (by
      simpa [norm_mul,lemma83_cpow_shift_norm hp.pos β hβ] using hx)
  have hkt : HasSum (fun n => lemma161Kappa β (p^(n+1))*x^(n+1)) (K-1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hk
  have ht : HasSum (fun n => lemma161Coefficient χ β d l (p^(n+1))*x^(n+1))
      (K-1-A*x*K) := by
    convert hkt.sub (hk.mul_left (A*x)) using 1
    funext n
    rw [lemma162_coefficient_d χ β hp d l n hpd,pow_succ]
    dsimp [A]
    ring
  convert (hasSum_nat_add_iff (f := fun n => lemma161Coefficient χ β d l (p^n)*x^n) 1).mp ht using 1
  simp only [sum_range_succ,sum_range_zero,pow_zero,lemma161_coefficient_one,one_mul,zero_add]
  dsimp [A,K]
  ring

lemma lemma162_coefficient_l_hasSum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hp : p.Prime) (l : ℕ) (hpl : p ∣ l)
    (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => lemma161Coefficient χ β 1 l (p^n)*x^n)
      (lemma161XiRational ((p:ℂ)^(-β)) (p:ℂ)⁻¹ (χ.evalNat p) x +
        lemma161LambdaFactor χ β p 1 * (χ.evalNat p/(1-(p:ℂ)⁻¹))*x*
          ((1-x)/(1-(p:ℂ)^(-β)*x))) := by
  let B := lemma161XiRational ((p:ℂ)^(-β)) (p:ℂ)⁻¹ (χ.evalNat p) x
  let K := (1-x)/(1-(p:ℂ)^(-β)*x)
  let lam := lemma161LambdaFactor χ β p 1
  let A := χ.evalNat p/(1-(p:ℂ)⁻¹)
  have hb := lemma161_coefficient_prime_hasSum χ β hβ hp x hx
  have hk : HasSum (fun n => lemma161Kappa β (p^n)*x^n) K :=
    lemma161_kappa_prime_power_hasSum β hp x (by
      simpa [norm_mul,lemma83_cpow_shift_norm hp.pos β hβ] using hx)
  have hbt : HasSum (fun n => lemma161Coefficient χ β 1 1 (p^(n+1))*x^(n+1)) (B-1) := by
    simpa [B] using (hasSum_nat_add_iff' 1).mpr hb
  have ht : HasSum (fun n => lemma161Coefficient χ β 1 l (p^(n+1))*x^(n+1))
      (B-1+lam*A*x*K) := by
    convert hbt.add (hk.mul_left (lam*A*x)) using 1
    funext n
    rw [lemma162_coefficient_l χ β hp l n hpl,pow_succ]
    dsimp [lam,A]
    ring
  convert (hasSum_nat_add_iff (f := fun n => lemma161Coefficient χ β 1 l (p^n)*x^n) 1).mp ht using 1
  simp only [sum_range_succ,sum_range_zero,pow_zero,lemma161_coefficient_one,one_mul,zero_add]
  dsimp [B,K,lam,A]
  ring

noncomputable def lemma162GeneralMPrimeFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let x := lemma32PrimeMonomial q.val s
  if q.val ∣ d then
    if q.val ∣ l then (1-v*x)⁻¹ else (1-v*x/(1-u))/(1-v*x)
  else if q.val ∣ l then
    lemma161PrimeFactor χ β q s + lemma161LambdaFactor χ β q.val 1*v*x/((1-u)*(1-v*x))
  else lemma161PrimeFactor χ β q s

/-- Exact source-derived factor in all four divisibility cases. -/
lemma lemma162_general_m_local_agreement {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (d l : ℕ) (q : Nat.Primes)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    ((1-(q.val:ℂ)^(-β)*lemma32PrimeMonomial q.val s)/
      ((1-lemma32PrimeMonomial q.val s)*(1-χ.evalNat q.val*lemma32PrimeMonomial q.val s))) *
      (∑' n : ℕ, lemma161Coefficient χ β d l (q.val^n)*lemma32PrimeMonomial q.val s^n) =
        lemma162GeneralMPrimeFactor χ β d l q s := by
  let a := (q.val:ℂ)^(-β)
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let x := lemma32PrimeMonomial q.val s
  have hx : ‖x‖ < 1 := (lemma152_monomial_norm_radius q s hs).trans_lt lemma83_regular_radius_lt_one
  have hu : ‖u‖ < 1 := by
    dsimp [u]
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr q.property.pos)).mpr (by exact_mod_cast q.property.one_lt)
  have hax : 1-a*x ≠ 0 := lemma83_one_sub_ne_zero (by
    simpa [a,norm_mul,lemma83_cpow_shift_norm q.property.pos _ hβ] using hx)
  have hxn := lemma83_one_sub_ne_zero hx
  have hun := lemma83_one_sub_ne_zero hu
  have hvxn : 1-v*x ≠ 0 := lemma83_one_sub_ne_zero (lt_of_le_of_lt
    (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hx)
  change (1-a*x)/((1-x)*(1-v*x)) *
    (∑' n : ℕ, lemma161Coefficient χ β d l (q.val^n)*x^n) = _
  by_cases hqd : q.val ∣ d
  · rw [(lemma162_coefficient_d_hasSum χ β hβ q.property d l hqd x hx).tsum_eq]
    unfold lemma162GeneralMPrimeFactor
    rw [if_pos hqd]
    change (1-a*x)/((1-x)*(1-v*x)) *
        ((1-(if q.val.Coprime l then v/(1-u) else 0)*x)*((1-x)/(1-a*x))) =
      if q.val ∣ l then (1-v*x)⁻¹ else (1-v*x/(1-u))/(1-v*x)
    by_cases hql : q.val ∣ l
    · rw [if_pos hql,if_neg (by simpa [q.property.coprime_iff_not_dvd] using hql)]
      simp only [zero_mul,sub_zero,one_mul]
      field_simp [hax,hxn,hun,hvxn]
    · rw [if_neg hql,if_pos (q.property.coprime_iff_not_dvd.mpr hql)]
      field_simp [hax,hxn,hun,hvxn]
  · simp_rw [lemma162_coefficient_unexcluded χ β q.property d l hqd]
    unfold lemma162GeneralMPrimeFactor
    rw [if_neg hqd]
    by_cases hql : q.val ∣ l
    · rw [if_pos hql,(lemma162_coefficient_l_hasSum χ β hβ q.property l hql x hx).tsum_eq]
      have hbase := lemma161_actual_local_correction χ β hβ q.property x hx
      rw [(lemma161_coefficient_prime_hasSum χ β hβ q.property x hx).tsum_eq] at hbase
      have hmc : lemma161PrimeFactor χ β q s = lemma152LocalCorrection a 0 u v x := by
        unfold lemma161PrimeFactor
        rw [lemma32_prime_monomial_eq_cpow q.property.pos β]
      rw [hmc,← hbase,mul_add]
      congr 1
      change (1-a*x)/((1-x)*(1-v*x)) *
        (lemma161LambdaFactor χ β q.val 1*(v/(1-u))*x*((1-x)/(1-a*x))) =
          lemma161LambdaFactor χ β q.val 1*v*x/((1-u)*(1-v*x))
      field_simp [hax,hxn,hun,hvxn]
    · rw [if_neg hql]
      simp_rw [lemma162_coefficient_l_unexcluded χ β q.property 1 l hql]
      rw [lemma161_actual_local_correction χ β hβ q.property x hx]
      unfold lemma161PrimeFactor
      rw [lemma32_prime_monomial_eq_cpow q.property.pos β]

end ZhangLS.Spec
