import ZhangLS.Spec.Lemma171Target
import ZhangLS.Spec.Lemma32LocalSeries

/-!
# Lemma 17.1: exact local Euler factors for the actual ν²

All three character-value cases are proved as convergent series. This is ν²,
without the τ₂² divisor weight in Lemma 3.2.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma171_coefficient_prime_power_of_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 1) (e : ℕ) :
    lemma171Coefficient χ (p^e) = (e+1 : ℝ)^2 := by
  rw [lemma171_coefficient_eq_real_square,lemma31_actual_nu_prime_power_of_one χ hp h]
  simp

lemma lemma171_coefficient_prime_power_of_zero {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 0) (e : ℕ) :
    lemma171Coefficient χ (p^e) = 1 := by
  simp [lemma171Coefficient,lemma31_actual_nu_prime_power χ hp e,h,zero_pow_eq]

lemma lemma171_coefficient_prime_power_of_neg_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = -1) (e : ℕ) :
    lemma171Coefficient χ (p^e) = if Even (e+1) then 0 else 1 := by
  simp only [lemma171Coefficient,lemma31_actual_nu_prime_power χ hp e,h,neg_one_geom_sum]
  split_ifs <;> simp

lemma lemma171_local_series_of_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 1) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun e : ℕ => (lemma171Coefficient χ (p^e) : ℂ)*z^e)
      ((1+z)/(1-z)^3) := by
  convert lemma32_square_geometric_hasSum z hz using 1
  funext e
  simp [lemma171_coefficient_prime_power_of_one χ hp h]

lemma lemma171_local_series_of_zero {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 0) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun e : ℕ => (lemma171Coefficient χ (p^e) : ℂ)*z^e) (1-z)⁻¹ := by
  convert hasSum_geometric_of_norm_lt_one hz using 1
  funext e
  simp [lemma171_coefficient_prime_power_of_zero χ hp h]

lemma lemma171_local_series_of_neg_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = -1) (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun e : ℕ => (lemma171Coefficient χ (p^e) : ℂ)*z^e) (1-z^2)⁻¹ := by
  have hzz : ‖z^2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have he : HasSum (fun e : ℕ => (lemma171Coefficient χ (p^(2*e)) : ℂ)*z^(2*e))
      (1-z^2)⁻¹ := by
    convert hasSum_geometric_of_norm_lt_one hzz using 1
    funext e
    have hodd : ¬Even (2*e+1) := Nat.not_even_two_mul_add_one e
    rw [lemma171_coefficient_prime_power_of_neg_one χ hp h (2*e),if_neg hodd]
    simp [pow_mul]
  have ho : HasSum (fun e : ℕ => (lemma171Coefficient χ (p^(2*e+1)) : ℂ)*z^(2*e+1)) 0 := by
    convert (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0) using 1
    funext e
    have heven : Even (2*e+1+1) := ⟨e+1,by omega⟩
    simp [lemma171_coefficient_prime_power_of_neg_one χ hp h,heven]
  simpa only [add_zero] using (HasSum.even_add_odd
    (f := fun e : ℕ => (lemma171Coefficient χ (p^e) : ℂ)*z^e) he ho)

/-- Removal of the two zeta and two L factors from the actual local series. -/
noncomputable def lemma171LocalCorrection {D : ℕ} (χ : RealPrimitiveCharacter D)
    (p : ℕ) (z : ℂ) : ℂ :=
  (1-z)^2*(1-χ.evalNat p*z)^2*∑' e : ℕ, (lemma171Coefficient χ (p^e) : ℂ)*z^e

lemma lemma171_local_correction_of_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 1) (z : ℂ) (hz : ‖z‖ < 1) :
    lemma171LocalCorrection χ p z = 1-z^2 := by
  unfold lemma171LocalCorrection
  rw [h,(lemma171_local_series_of_one χ hp h z hz).tsum_eq]
  have hn : 1-z ≠ 0 := sub_ne_zero.mpr (by intro h; rw [← h] at hz; norm_num at hz)
  simp only [one_mul]
  field_simp
  all_goals ring

lemma lemma171_local_correction_of_zero {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = 0) (z : ℂ) (hz : ‖z‖ < 1) :
    lemma171LocalCorrection χ p z = 1-z := by
  unfold lemma171LocalCorrection
  rw [h,(lemma171_local_series_of_zero χ hp h z hz).tsum_eq]
  have hn : 1-z ≠ 0 := sub_ne_zero.mpr (by intro h; rw [← h] at hz; norm_num at hz)
  simp only [zero_mul,sub_zero,one_pow,mul_one]
  field_simp

lemma lemma171_local_correction_of_neg_one {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (h : χ.evalNat p = -1) (z : ℂ) (hz : ‖z‖ < 1) :
    lemma171LocalCorrection χ p z = 1-z^2 := by
  unfold lemma171LocalCorrection
  rw [h,(lemma171_local_series_of_neg_one χ hp h z hz).tsum_eq]
  have hzz : ‖z^2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg z]
  have hn : 1-z^2 ≠ 0 := sub_ne_zero.mpr (by intro h; rw [← h] at hzz; norm_num at hzz)
  simp only [neg_one_mul,sub_neg_eq_add]
  field_simp
  all_goals ring

lemma lemma171_character_prime_cases_of_not_dvd {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (hpd : ¬p ∣ D) : χ.evalNat p = 1 ∨ χ.evalNat p = -1 := by
  have hu : IsUnit (p : ZMod D) := by
    rw [ZMod.isUnit_iff_coprime]
    exact hp.coprime_iff_not_dvd.mpr hpd
  have hn : χ.evalNat p ≠ 0 := (hu.map χ.chi.toMonoidHom).ne_zero
  rcases MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (p : ZMod D) with h | h | h
  · exact False.elim (hn h)
  · exact Or.inl h
  · exact Or.inr h

/-- Exact ramified/unramified Euler correction in Appendix B, p. 109. -/
lemma lemma171_local_correction {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (z : ℂ) (hz : ‖z‖ < 1) :
    lemma171LocalCorrection χ p z = if p ∣ D then 1-z else 1-z^2 := by
  by_cases hd : p ∣ D
  · rw [if_pos hd]
    exact lemma171_local_correction_of_zero χ hp
      (χ.evalNat_eq_zero_of_dvd_modulus hd hp.ne_one) z hz
  · rw [if_neg hd]
    rcases lemma171_character_prime_cases_of_not_dvd χ hp hd with h | h
    · exact lemma171_local_correction_of_one χ hp h z hz
    · exact lemma171_local_correction_of_neg_one χ hp h z hz



end ZhangLS.Spec
