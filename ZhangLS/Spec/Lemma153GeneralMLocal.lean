import ZhangLS.Spec.Lemma153GeneralMSeries
import ZhangLS.Spec.Lemma153BaseClosed
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 3000000

lemma lemma153_general_m_prime_power_unexcluded {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hp : p.Prime) (d l : ℕ) (hpd : ¬p ∣ d) (n : ℕ) :
    lemma152Coefficient χ β d l (p^n) = lemma152Coefficient χ β 1 l (p^n) := by
  cases n with
  | zero => simp
  | succ n =>
    unfold lemma152Coefficient
    rw [lemma152_modified_lambda_prime_power χ β hp,if_neg hpd,
      lemma152_modified_lambda_prime_power χ β hp,if_neg hp.not_dvd_one,
      lemma152_xi_prime_power χ β hp,lemma152_xi_prime_power χ β hp,
      lemma152_modified_kappa_prime_power_unexcluded χ β hp hpd,
      lemma152_modified_kappa_prime_power_unexcluded χ β hp hp.not_dvd_one]

lemma lemma153_general_m_prime_power_l_unexcluded {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hp : p.Prime) (d l : ℕ) (hpl : ¬p ∣ l) (n : ℕ) :
    lemma152Coefficient χ β d l (p^n) = lemma152Coefficient χ β d 1 (p^n) := by
  cases n with
  | zero => simp
  | succ n =>
    unfold lemma152Coefficient
    rw [lemma152_xi_prime_power χ β hp,lemma152_xi_prime_power χ β hp,
      if_pos (hp.coprime_iff_not_dvd.mpr hpl),if_pos (Nat.coprime_one_right p)]

/-- The true local numerator in the q|l case, valid also on the diagonal. -/
lemma lemma153_general_m_l_hasSum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime)
    (l : ℕ) (hpl : p ∣ l) (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => lemma152Coefficient χ β 1 l (p^n)*x^n)
      (lemma153BaseClosed ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (p:ℂ)⁻¹ (χ.evalNat p) x +
        lemma152LambdaFactor χ β p 1 * (χ.evalNat p/(1-(p:ℂ)⁻¹))*x*
          lemma152KappaRational ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) x) := by
  let B := lemma153BaseClosed ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (p:ℂ)⁻¹ (χ.evalNat p) x
  let K := lemma152KappaRational ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) x
  let lam := lemma152LambdaFactor χ β p 1
  let A := χ.evalNat p/(1-(p:ℂ)⁻¹)
  have hb := lemma153_base_closed_hasSum χ β hβ hp x hx
  have hk : HasSum (fun n => lemma152Kappa β (p^n)*x^n) K :=
    lemma152_kappa_prime_power_hasSum β hp x (fun i => by
      simpa [norm_mul,lemma83_cpow_shift_norm hp.pos (β i) (hβ i)] using hx)
  have hbt : HasSum (fun n => lemma152Coefficient χ β 1 1 (p^(n+1))*x^(n+1)) (B-1) := by
    simpa [B] using (hasSum_nat_add_iff' 1).mpr hb
  have hs : HasSum (fun n => lemma152Coefficient χ β 1 l (p^(n+1))*x^(n+1))
      (B-1+lam*A*x*K) := by
    convert hbt.add (hk.mul_left (lam*A*x)) using 1
    funext n
    rw [lemma153_coefficient_prime_power_l χ β hp n l hpl,pow_succ]
    dsimp [lam,A]
    ring
  convert (hasSum_nat_add_iff (f := fun n => lemma152Coefficient χ β 1 l (p^n)*x^n) 1).mp hs using 1
  simp only [sum_range_succ,sum_range_zero,pow_zero,lemma152_coefficient_one,one_mul,zero_add]
  dsimp [B,lam,A,K]
  ring

noncomputable def lemma153GeneralMPrimeFactor {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d l : ℕ) (q : Nat.Primes) (s : ℂ) : ℂ :=
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let x := lemma32PrimeMonomial q.val s
  if q.val ∣ d then
    if q.val ∣ l then (1-v*x)⁻¹ else (1-v*x/(1-u))/(1-v*x)
  else if q.val ∣ l then
    lemma152PrimeFactor χ β q s + lemma152LambdaFactor χ β q.val 1*v*x/((1-u)*(1-v*x))
  else lemma152PrimeFactor χ β q s

lemma lemma153_general_m_local_agreement {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (d l : ℕ) (q : Nat.Primes)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    lemma152LocalRemoval ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1)) (χ.evalNat q.val)
      (lemma32PrimeMonomial q.val s) *
      (∑' n : ℕ, lemma152Coefficient χ β d l (q.val^n)*lemma32PrimeMonomial q.val s^n) =
        lemma153GeneralMPrimeFactor χ β d l q s := by
  let a := (q.val:ℂ)^(-β 0)
  let b := (q.val:ℂ)^(-β 1)
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let x := lemma32PrimeMonomial q.val s
  have hx : ‖x‖ < 1 := (lemma152_monomial_norm_radius q s hs).trans_lt lemma83_regular_radius_lt_one
  have hu : ‖u‖ < 1 := by
    dsimp [u]
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr q.property.pos)).mpr (by exact_mod_cast q.property.one_lt)
  have hax : 1-a*x ≠ 0 := lemma83_one_sub_ne_zero (by
    simpa [a,norm_mul,lemma83_cpow_shift_norm q.property.pos _ (hβ 0)] using hx)
  have hbx : 1-b*x ≠ 0 := lemma83_one_sub_ne_zero (by
    simpa [b,norm_mul,lemma83_cpow_shift_norm q.property.pos _ (hβ 1)] using hx)
  have hxn := lemma83_one_sub_ne_zero hx
  have hun := lemma83_one_sub_ne_zero hu
  have hvxn : 1-v*x ≠ 0 := lemma83_one_sub_ne_zero (lt_of_le_of_lt
    (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hx)
  change lemma152LocalRemoval a b v x *
      (∑' n : ℕ, lemma152Coefficient χ β d l (q.val^n)*x^n) = _
  by_cases hqd : q.val ∣ d
  · rw [(lemma153_coefficient_d_hasSum χ β hβ q.property d l hqd x hx).tsum_eq]
    unfold lemma153GeneralMPrimeFactor
    rw [if_pos hqd]
    change lemma152LocalRemoval a b v x *
        ((1-(if q.val.Coprime l then v/(1-u) else 0)*x)*lemma152KappaRational a b x) =
      if q.val ∣ l then (1-v*x)⁻¹ else (1-v*x/(1-u))/(1-v*x)
    by_cases hql : q.val ∣ l
    · rw [if_pos hql,if_neg (by simpa [q.property.coprime_iff_not_dvd] using hql)]
      simp only [zero_mul,sub_zero,one_mul]
      unfold lemma152LocalRemoval lemma152KappaRational
      repeat' field_simp [hax,hbx,hxn,hun,hvxn,mul_comm]
      all_goals ring
    · rw [if_neg hql,if_pos (q.property.coprime_iff_not_dvd.mpr hql)]
      unfold lemma152LocalRemoval lemma152KappaRational
      repeat' field_simp [hax,hbx,hxn,hun,hvxn,mul_comm]
      all_goals ring
  · simp_rw [lemma153_general_m_prime_power_unexcluded χ β q.property d l hqd]
    unfold lemma153GeneralMPrimeFactor
    rw [if_neg hqd]
    by_cases hql : q.val ∣ l
    · rw [if_pos hql,(lemma153_general_m_l_hasSum χ β hβ q.property l hql x hx).tsum_eq]
      have hbase := lemma153_actual_local_correction χ β hβ q.property x hx
      rw [(lemma153_base_closed_hasSum χ β hβ q.property x hx).tsum_eq] at hbase
      have hmc : lemma152PrimeFactor χ β q s = lemma152LocalCorrection a b u v x := by
        unfold lemma152PrimeFactor
        rw [lemma32_prime_monomial_eq_cpow q.property.pos (β 0),
          lemma32_prime_monomial_eq_cpow q.property.pos (β 1)]
      rw [hmc,← hbase,mul_add]
      congr 1
      change lemma152LocalRemoval a b v x *
          (lemma152LambdaFactor χ β q.val 1*(v/(1-u))*x*lemma152KappaRational a b x) =
        lemma152LambdaFactor χ β q.val 1*v*x/((1-u)*(1-v*x))
      unfold lemma152LocalRemoval lemma152KappaRational
      repeat' field_simp [hax,hbx,hxn,hun,hvxn,mul_comm]
      all_goals ring
    · rw [if_neg hql]
      simp_rw [lemma153_general_m_prime_power_l_unexcluded χ β q.property 1 l hql]
      rw [lemma153_actual_local_correction χ β hβ q.property x hx]
      unfold lemma152PrimeFactor
      rw [lemma32_prime_monomial_eq_cpow q.property.pos (β 0),
        lemma32_prime_monomial_eq_cpow q.property.pos (β 1)]

end ZhangLS.Spec
