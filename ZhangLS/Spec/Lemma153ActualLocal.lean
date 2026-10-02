import ZhangLS.Spec.Lemma153GeneralMRatio
import ZhangLS.Spec.Lemma153PrimePowerBridge
import ZhangLS.Spec.Lemma153EulerDefinitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

/-- The three actual normalized M-ratios needed by the prime-power arithmetic
bridge. The cases are derived from (15.18), not imposed as assumptions. -/
lemma lemma153_actual_local_ratios {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (q : Nat.Primes) (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) :
    let B := lemma153Baseline χ β γ q
    let lam := lemma152LambdaFactor χ β q.val 1
    let A := χ.evalNat q.val/(1-(q.val:ℂ)⁻¹)
    let y := lemma32PrimeMonomial q.val (1-γ)
    let K := lemma152KappaRational ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1)) y
    (∀ n : ℕ, 0<n → lemma153GeneralMEulerProduct χ β 1 (q.val^n) (1-γ) /
      lemma153GeneralMEulerProduct χ β 1 1 (1-γ) = (B+lam*A*y*K)/B) ∧
    (∀ n : ℕ, 0<n → lemma153GeneralMEulerProduct χ β (q.val^n) 1 (1-γ) /
      lemma153GeneralMEulerProduct χ β 1 1 (1-γ) = ((1-A*y)*K)/B) ∧
    (∀ k l : ℕ, 0<k → 0<l → lemma153GeneralMEulerProduct χ β (q.val^k) (q.val^l) (1-γ) /
      lemma153GeneralMEulerProduct χ β 1 1 (1-γ) = K/B) := by
  dsimp only
  have hs : 9/10 ≤ (1-γ).re := by simp [hγ]; norm_num
  have hx : ‖lemma32PrimeMonomial q.val (1-γ)‖ < 1 :=
    (lemma152_monomial_norm_radius q (1-γ) hs).trans_lt lemma83_regular_radius_lt_one
  refine ⟨?_,?_,?_⟩
  · intro n hn
    have hr := lemma153_general_m_prime_power_ratio χ β hβ q 0 n (by omega) (1-γ) hs hM
    simp only [pow_zero] at hr
    rw [hr,(lemma153_general_m_l_hasSum χ β hβ q.property (q.val^n)
      (dvd_pow_self q.val hn.ne') _ hx).tsum_eq]
    rfl
  · intro n hn
    have hr := lemma153_general_m_prime_power_ratio χ β hβ q n 0 (by omega) (1-γ) hs hM
    simp only [pow_zero] at hr
    rw [hr,(lemma153_coefficient_d_hasSum χ β hβ q.property (q.val^n) 1
      (dvd_pow_self q.val hn.ne') _ hx).tsum_eq]
    simp [lemma153Baseline]
  · intro k l hk hl
    rw [lemma153_general_m_prime_power_ratio χ β hβ q k l (by omega) (1-γ) hs hM,
      (lemma153_coefficient_d_hasSum χ β hβ q.property (q.val^k) (q.val^l)
        (dvd_pow_self q.val hk.ne') _ hx).tsum_eq]
    have hcop : ¬q.val.Coprime (q.val^l) := by
      intro hc
      exact (q.property.coprime_iff_not_dvd.mp hc) (dvd_pow_self q.val hl.ne')
    simp [hcop,lemma153Baseline]

lemma lemma153_actual_unramified_chi_varpi {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (q : Nat.Primes) (hqd : ¬q.val ∣ D) (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) (n : ℕ) :
    χ.evalNat (q.val^n)*lemma153Varpi χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n) =
      let B := lemma153Baseline χ β γ q
      let lam := lemma152LambdaFactor χ β q.val 1
      let A := χ.evalNat q.val/(1-(q.val:ℂ)⁻¹)
      let y := lemma32PrimeMonomial q.val (1-γ)
      let K := lemma152KappaRational ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1)) y
      lemma153LocalChiVarpi B (B+lam*A*y*K) ((1-A*y)*K) K lam
        (χ.evalNat q.val*(q.val:ℂ)^γ) n := by
  have hv : χ.evalNat q.val^2 = 1 := by
    rcases lemma32_character_prime_cases_of_not_dvd χ q.property hqd with h | h <;> rw [h] <;> norm_num
  have hr := lemma153_actual_local_ratios χ β hβ γ hγ q hM
  exact lemma153_chi_varpi_prime_power χ β γ (lemma153GeneralMEulerProduct χ β)
    q.property hv (by simpa using hM) _ _ _ _ hr.1 hr.2.1 hr.2.2 n

/-- Exact corrected local extraction for the genuine arithmetic coefficient,
with every M-ratio premise and every division justified. -/
lemma lemma153_actual_prime_factor_extraction {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (γ : ℂ) (hγ : γ.re = 0)
    (q : Nat.Primes) (hM : lemma152EulerProduct χ β (1-γ) ≠ 0)
    (s : ℂ) (hs : 9/10 ≤ s.re) :
    (1-lemma32PrimeMonomial q.val s)^2 *
      (1-χ.evalNat q.val*(q.val:ℂ)^γ*lemma32PrimeMonomial q.val s)^2 *
      (∑' n : ℕ, lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n)*
        lemma32PrimeMonomial q.val s^n) = lemma153PrimeFactor χ β γ q s := by
  by_cases hqd : q.val ∣ D
  · rw [lemma153PrimeFactor,if_pos hqd]
    exact lemma153_ramified_local_extraction χ β γ (lemma153GeneralMEulerProduct χ β)
      (by simpa using hM) q.property hqd _ _
  · rw [lemma153PrimeFactor,if_neg hqd]
    have hv : χ.evalNat q.val^2 = 1 := by
      rcases lemma32_character_prime_cases_of_not_dvd χ q.property hqd with h | h <;> rw [h] <;> norm_num
    have hx : ‖lemma32PrimeMonomial q.val s‖ < 1 :=
      (lemma152_monomial_norm_radius q s hs).trans_lt lemma83_regular_radius_lt_one
    have hw : ‖(q.val:ℂ)^γ‖ = 1 := by
      simpa using lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hγ])
    have htx : ‖χ.evalNat q.val*(q.val:ℂ)^γ*lemma32PrimeMonomial q.val s‖ < 1 := by
      simp only [norm_mul,hw,mul_one]
      exact lt_of_le_of_lt (mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hx
    have hs0 : 9/10 ≤ (1-γ).re := by simp [hγ]; norm_num
    have hB : lemma153Baseline χ β γ q ≠ 0 := by
      have hb := lemma153_base_local_nonzero χ β hβ q (1-γ) hs0 hM
      rw [(lemma153_base_closed_hasSum χ β hβ q.property (lemma32PrimeMonomial q.val (1-γ))
        ((lemma152_monomial_norm_radius q (1-γ) hs0).trans_lt lemma83_regular_radius_lt_one)).tsum_eq] at hb
      exact hb
    have hr := lemma153_actual_local_ratios χ β hβ γ hγ q hM
    exact lemma153_actual_prime_power_extraction χ β γ (lemma153GeneralMEulerProduct χ β)
      q.property hv (by simpa using hM) _ _ _ _ hB (by ring) hr.1 hr.2.1 hr.2.2 _ hx htx

end ZhangLS.Spec
