import ZhangLS.Spec.Lemma153LocalCorrection
import ZhangLS.Spec.Lemma153PrimeLocal
/-! The exact zero-shift center, including the diagonal χ(q)=1 case where
the divided-difference representation of the supported tail is not usable. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma153ZeroB (u v : ℂ) : ℂ :=
  (1-v*u)/(1-u)*(1-v*u^2)/(1-u^2)
noncomputable def lemma153ZeroC (u : ℂ) : ℂ := (1-u)⁻¹
noncomputable def lemma153ZeroE (u v : ℂ) : ℂ := (1-v*u/(1-u))/(1-u)

lemma lemma153_zero_b_ne_zero (u v : ℂ) (hu : ‖u‖ < 1) (hv : v = 1 ∨ v = -1) :
    lemma153ZeroB u v ≠ 0 := by
  have hvn : ‖v‖ = 1 := by rcases hv with rfl | rfl <;> simp
  have hu2 : ‖u^2‖ < 1 := by rw [norm_pow]; nlinarith [norm_nonneg u]
  unfold lemma153ZeroB
  apply div_ne_zero
  · apply mul_ne_zero
    · exact div_ne_zero (lemma83_one_sub_ne_zero (by simpa [norm_mul,hvn] using hu))
        (lemma83_one_sub_ne_zero hu)
    · exact lemma83_one_sub_ne_zero (by simpa [norm_mul,hvn] using hu2)
  · exact lemma83_one_sub_ne_zero hu2

lemma lemma153_zero_b_compatibility (u v : ℂ) (hu : ‖u‖ < 1) (hv : v = 1 ∨ v = -1) :
    lemma153ZeroB u v = lemma153ZeroC u + (1-v*u)*lemma153ZeroE u v -
      (1-v*u)*lemma153ZeroC u := by
  have hun := lemma83_one_sub_ne_zero hu
  have hup : 1+u ≠ 0 := by simpa using lemma83_one_sub_ne_zero (show ‖-u‖ < 1 by simpa using hu)
  have hu2 : 1-u^2 ≠ 0 := by
    rw [show 1-u^2 = (1-u)*(1+u) by ring]
    exact mul_ne_zero hun hup
  unfold lemma153ZeroB lemma153ZeroC lemma153ZeroE
  rcases hv with rfl | rfl
  all_goals field_simp
  all_goals ring

lemma lemma153_zero_center_local_value (u v : ℂ) (hu : ‖u‖ < 1) (hv : v = 1 ∨ v = -1) :
    lemma153ShiftedLocalCorrection (lemma153ZeroB u v) (lemma153ZeroC u)
      (lemma153ZeroE u v) (lemma153ZeroC u) (1-v*u) v u =
        (1-u^2)^2/(1-v*u^2) := by
  have hun := lemma83_one_sub_ne_zero hu
  have hup : 1+u ≠ 0 := by simpa using lemma83_one_sub_ne_zero (show ‖-u‖ < 1 by simpa using hu)
  have hu2 : 1-u^2 ≠ 0 := by
    rw [show 1-u^2 = (1-u)*(1+u) by ring]
    exact mul_ne_zero hun hup
  have hu2p : 1+u^2 ≠ 0 := by
    simpa using lemma83_one_sub_ne_zero (show ‖-(u^2)‖ < 1 by
      rw [norm_neg,norm_pow]
      nlinarith [norm_nonneg u])
  have hu3 : 1+u+u^2+u^3 ≠ 0 := by
    rw [show 1+u+u^2+u^3 = (1+u)*(1+u^2) by ring]
    exact mul_ne_zero hup hu2p
  unfold lemma153ShiftedLocalCorrection lemma153ZeroB lemma153ZeroC lemma153ZeroE
  rcases hv with rfl | rfl
  all_goals repeat' field_simp [hun,hup,hu2,hu2p,hu3]
  all_goals ring

lemma lemma153_lambda_zero_shifts {D p : ℕ} (χ : RealPrimitiveCharacter D) (hp : p.Prime) :
    lemma152LambdaFactor χ (fun _ => 0) p 1 = 1-χ.evalNat p*(p:ℂ)⁻¹ := by
  have hu : ‖(p:ℂ)⁻¹‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hvu : 1-χ.evalNat p*(p:ℂ)⁻¹ ≠ 0 := lemma83_one_sub_ne_zero
    (lt_of_le_of_lt (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)) hu)
  rw [lemma152_lambda_factor_rational χ (fun _ => 0) hp.pos]
  simp only [neg_zero,Complex.cpow_zero,one_mul]
  exact mul_div_cancel_right₀ _ hvu

lemma lemma153_zero_kappa_prime_power (p : ℕ) (hp : p.Prime) (n : ℕ) :
    lemma152Kappa (fun _ => 0) (p^n) = 1 := by
  rw [lemma152_kappa_prime_power (fun _ => 0) hp]
  simp

lemma lemma153_zero_coefficient_prime_power {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (n : ℕ) :
    lemma152Coefficient χ (fun _ => 0) 1 1 (p^(n+1)) =
      1-χ.evalNat p*(1-χ.evalNat p*(p:ℂ)⁻¹)/(1-(p:ℂ)⁻¹) := by
  have hu : ‖(p:ℂ)⁻¹‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hvu : ‖χ.evalNat p*(p:ℂ)⁻¹‖ < 1 :=
    lt_of_le_of_lt (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)) hu
  have hun := lemma83_one_sub_ne_zero hu
  have hvun := lemma83_one_sub_ne_zero hvu
  rw [lemma152_coefficient_prime_power χ (fun _ => 0) hp,
    lemma153_lambda_zero_shifts χ hp,lemma152_mobius_weight χ hp]
  simp_rw [lemma153_zero_kappa_prime_power p hp,one_mul,zpow_neg_one]
  rw [(hasSum_geometric_of_norm_lt_one hvu).tsum_eq]
  rw [mul_sub,mul_inv_cancel₀ hvun]
  ring

lemma lemma153_zero_base_hasSum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => lemma152Coefficient χ (fun _ => 0) 1 1 (p^n)*x^n)
      (1+(1-χ.evalNat p*(1-χ.evalNat p*(p:ℂ)⁻¹)/(1-(p:ℂ)⁻¹))*x/(1-x)) := by
  let c := 1-χ.evalNat p*(1-χ.evalNat p*(p:ℂ)⁻¹)/(1-(p:ℂ)⁻¹)
  have hs : HasSum (fun n : ℕ => lemma152Coefficient χ (fun _ => 0) 1 1 (p^(n+1))*x^(n+1))
      (c*x/(1-x)) := by
    convert (hasSum_geometric_of_norm_lt_one hx).mul_left (c*x) using 1
    · funext n
      rw [lemma153_zero_coefficient_prime_power χ hp,pow_succ]
      dsimp [c]
      ring
  convert (hasSum_nat_add_iff (f := fun n => lemma152Coefficient χ (fun _ => 0) 1 1 (p^n)*x^n) 1).mp hs using 1
  simp [c,add_comm]

end ZhangLS.Spec
