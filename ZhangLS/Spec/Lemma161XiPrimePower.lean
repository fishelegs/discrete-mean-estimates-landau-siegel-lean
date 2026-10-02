import ZhangLS.Spec.Lemma161KappaLocal

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

lemma lemma161_modified_kappa_excluded {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d r : ℕ) (s : ℂ)
    (hdr : ∀ p ∈ d.primeFactors, p ∣ r) :
    lemma161ModifiedKappa χ β d r s = lemma161Kappa β d := by
  let oneIndex : Lemma83SupportedIndex d r := ⟨1,by simp⟩
  have hone (h : Lemma83SupportedIndex d r) : h = oneIndex := by
    apply Subtype.ext
    exact lemma83_supported_eq_one hdr h
  unfold lemma161ModifiedKappa
  rw [tsum_eq_single oneIndex (by intro h hne; exact False.elim (hne (hone h)))]
  simp [oneIndex,RealPrimitiveCharacter.evalNat]

@[simp] lemma lemma161_modified_kappa_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (r : ℕ) (s : ℂ) : lemma161ModifiedKappa χ β 1 r s = 1 := by
  rw [lemma161_modified_kappa_excluded χ β 1 r s (by simp)]
  simp

lemma lemma161_modified_kappa_prime_power_excluded {D p r : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hp : p.Prime)
    (hpr : p ∣ r) (e : ℕ) (s : ℂ) :
    lemma161ModifiedKappa χ β (p^e) r s = lemma161Kappa β (p^e) := by
  apply lemma161_modified_kappa_excluded
  intro q hq
  exact ((Nat.prime_of_mem_primeFactors hq).dvd_of_dvd_pow
    (Nat.dvd_of_mem_primeFactors hq)).trans hpr

/-- Reindex the actual χ-weighted supported sum, retaining every tail term. -/
lemma lemma161_modified_kappa_prime_power_unexcluded {D p r : ℕ}
    (χ : RealPrimitiveCharacter D) (β : ℂ) (hp : p.Prime)
    (hpr : ¬p ∣ r) (e : ℕ) (s : ℂ) :
    lemma161ModifiedKappa χ β (p^(e+1)) r s =
      ∑' k : ℕ, lemma161Kappa β (p^(e+1+k)) * (χ.evalNat p * (p:ℂ)^(-s))^k := by
  unfold lemma161ModifiedKappa
  rw [← (lemma83SupportedPrimePowerEquiv hp hpr e).tsum_eq]
  apply tsum_congr
  intro k
  simp only [lemma83SupportedPrimePowerEquiv,Equiv.coe_fn_mk]
  rw [← pow_add,Nat.cast_pow,← Complex.natCast_cpow_natCast_mul,
    Complex.cpow_nat_mul,div_eq_mul_inv,← inv_pow,Complex.cpow_neg]
  simp [RealPrimitiveCharacter.evalNat,Nat.cast_pow,map_pow,mul_pow,mul_assoc]

@[simp] lemma lemma161_xi_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) : lemma161Xi χ β 1 d l = 1 := by
  simp [lemma161Xi,Finset.filter_singleton,RealPrimitiveCharacter.evalNat]

@[simp] lemma lemma161_xi_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) : lemma161Xi χ β 0 d l = 0 := by
  simp [lemma161Xi]

lemma lemma161_modified_lambda_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) (e d : ℕ) :
    lemma161ModifiedLambda χ β (p^(e+1)) d =
      if p ∣ d then 1 else lemma161LambdaFactor χ β p 1 := by
  unfold lemma161ModifiedLambda
  rw [Nat.primeFactors_pow _ (Nat.succ_ne_zero e),hp.primeFactors]
  by_cases hpd : p ∣ d <;> simp [filter_singleton,hpd]

lemma lemma161_xi_prime_power_sum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) (e d l : ℕ) :
    lemma161Xi χ β (p^(e+1)) d l =
      ∑ k ∈ range (e+2), if (p^k).Coprime l then
        (ArithmeticFunction.moebius (p^k) : ℂ) * χ.evalNat (p^k) * (p^k : ℂ) /
          (Nat.totient (p^k) : ℂ) *
            lemma161ModifiedKappa χ β (p^(e+1-k)) (d*p^k) 1 else 0 := by
  unfold lemma161Xi
  rw [Finset.sum_filter,Nat.sum_divisorsAntidiagonal'
    (fun a b => if b.Coprime l then
      (ArithmeticFunction.moebius b : ℂ) * χ.evalNat b * (b : ℂ) /
        (Nat.totient b : ℂ) * lemma161ModifiedKappa χ β a (d*b) 1 else 0),
    Nat.sum_divisors_prime_pow hp]
  apply sum_congr rfl
  intro k hk
  rw [Nat.pow_div (show k ≤ e+1 by have := mem_range.mp hk; omega) hp.pos]
  simp only [Nat.cast_pow]

/-- The exact two terms in Appendix A’s proof of Lemma16.1, proved from the original finite divisor sum. -/
lemma lemma161_xi_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) (e d l : ℕ) :
    lemma161Xi χ β (p^(e+1)) d l =
      lemma161ModifiedKappa χ β (p^(e+1)) d 1 -
        if p.Coprime l then χ.evalNat p * (p:ℂ)/(p-1:ℕ) * lemma161Kappa β (p^e) else 0 := by
  rw [lemma161_xi_prime_power_sum χ β hp e d l]
  rw [show e+2 = (e+1)+1 by omega,Finset.sum_range_succ']
  have hμ (k : ℕ) : (ArithmeticFunction.moebius (p^(k+1)) : ℂ) =
      if k = 0 then -1 else 0 := lemma83_moebius_prime_power_succ hp k
  simp only [hμ]
  have hs : (∑ k ∈ range (e+1),
      if (p^(k+1)).Coprime l then
        (if k = 0 then -1 else 0) * χ.evalNat (p^(k+1)) * (p^(k+1):ℂ) /
          (Nat.totient (p^(k+1)):ℂ) *
            lemma161ModifiedKappa χ β (p^(e+1-(k+1))) (d*p^(k+1)) 1 else 0) =
      if p.Coprime l then -(χ.evalNat p*(p:ℂ)/(p-1:ℕ)*lemma161Kappa β (p^e)) else 0 := by
    rw [sum_eq_single 0]
    · simp only [zero_add,pow_one,Nat.add_sub_cancel_right]
      rw [lemma161_modified_kappa_prime_power_excluded χ β hp (dvd_mul_left p d) e,
        Nat.totient_prime hp]
      split_ifs <;> ring
    · intro k hk hk0
      simp [hk0]
    · simp
  rw [hs]
  simp only [pow_zero,Nat.sub_zero,mul_one,Nat.coprime_one_left,Nat.coprime_one_right,if_true,
    ArithmeticFunction.moebius_apply_one,Int.cast_one,Nat.cast_one,
    Nat.totient_one,div_one,RealPrimitiveCharacter.evalNat,map_one,one_mul]
  split_ifs <;> simp_all <;> ring

/-- The actual coefficients required by M₂(1,1;s), not a synthetic Euler model. -/
lemma lemma161_coefficient_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : p.Prime) (e : ℕ) :
    lemma161Coefficient χ β 1 1 (p^(e+1)) =
      lemma161LambdaFactor χ β p 1 *
        ((∑' k : ℕ, lemma161Kappa β (p^(e+1+k)) *
          (χ.evalNat p * (p:ℂ)^(-1:ℤ))^k) -
            χ.evalNat p*(p:ℂ)/(p-1:ℕ)*lemma161Kappa β (p^e)) := by
  unfold lemma161Coefficient
  rw [lemma161_modified_lambda_prime_power χ β hp,if_neg hp.not_dvd_one,
    lemma161_xi_prime_power χ β hp,if_pos (Nat.coprime_one_right p),
    lemma161_modified_kappa_prime_power_unexcluded χ β hp hp.not_dvd_one]
  simp only [Complex.cpow_neg,Complex.cpow_one,zpow_neg_one]

end ZhangLS.Spec
