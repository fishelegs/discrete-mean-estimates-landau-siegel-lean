import ZhangLS.Spec.Lemma161XiPrimePower
import ZhangLS.Spec.Lemma152LocalCorrection
import ZhangLS.Spec.Lemma83LocalAgreement

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1200000

@[simp] lemma lemma161_coefficient_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) : lemma161Coefficient χ β d l 1 = 1 := by
  simp [lemma161Coefficient,lemma161ModifiedLambda]

@[simp] lemma lemma161_coefficient_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (d l : ℕ) : lemma161Coefficient χ β d l 0 = 0 := by
  simp [lemma161Coefficient]

lemma lemma161_lambda_factor_rational {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hp : 0 < p) :
    lemma161LambdaFactor χ β p 1 =
      (1-(p:ℂ)^(-β)*(χ.evalNat p*(p:ℂ)⁻¹))/(1-χ.evalNat p*(p:ℂ)⁻¹) := by
  have hn : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have h : (p:ℂ)^(-1-β) = (p:ℂ)^(-β)*(p:ℂ)⁻¹ := by
    rw [show (-1:ℂ)-β = -β + -1 by ring,Complex.cpow_add _ _ hn,Complex.cpow_neg_one]
  simp only [lemma161LambdaFactor,h,Complex.cpow_neg_one]
  congr 2 <;> ring

lemma lemma161_mobius_weight {D p : ℕ} (χ : RealPrimitiveCharacter D) (hp : p.Prime) :
    χ.evalNat p*(p:ℂ)/(p-1:ℕ) = χ.evalNat p/(1-(p:ℂ)⁻¹) := by
  have hn : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp1 : (p:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [Nat.cast_sub hp.one_le,Nat.cast_one]
  repeat' field_simp [hn,hp1]
  all_goals ring

noncomputable def lemma161XiRational (a u v x : ℂ) : ℂ :=
  1 + ((1-a*(v*u))/(1-v*u)) *
    ((a-1)*x/((1-a*(v*u))*(1-a*x)) - (v/(1-u))*x*((1-x)/(1-a*x)))

/-- Exact local generating series, without an artificial off-diagonal exclusion. -/
lemma lemma161_coefficient_prime_hasSum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hp : p.Prime) (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => lemma161Coefficient χ β 1 1 (p^n)*x^n)
      (lemma161XiRational ((p:ℂ)^(-β)) (p:ℂ)⁻¹ (χ.evalNat p) x) := by
  let a := (p:ℂ)^(-β)
  let t := χ.evalNat p*(p:ℂ)⁻¹
  let K := (1-x)/(1-a*x)
  let A := χ.evalNat p/(1-(p:ℂ)⁻¹)
  let l := lemma161LambdaFactor χ β p 1
  have hnorm : ‖a‖ = 1 := lemma83_cpow_shift_norm hp.pos β hβ
  have ht : ‖t‖ < 1 := by
    dsimp [t]
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    apply lt_of_le_of_lt (mul_le_of_le_one_left (by positivity) (χ.evalNat_norm_le_one p))
    exact (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hat : ‖a*t‖ < 1 := by simpa [norm_mul,hnorm] using ht
  have hax : ‖a*x‖ < 1 := by simpa [norm_mul,hnorm] using hx
  have hk : HasSum (fun n => lemma161Kappa β (p^n)*x^n) K :=
    lemma161_kappa_prime_power_hasSum β hp x hax
  have hs : HasSum (fun n => (∑' k : ℕ, lemma161Kappa β (p^(n+1+k))*t^k)*x^(n+1))
      ((a-1)*x/((1-a*t)*(1-a*x))) := by
    convert (hasSum_geometric_of_norm_lt_one hax).mul_left ((a-1)*x/(1-a*t)) using 1
    · funext n
      simp only [lemma161_kappa_prime_power β hp]
      rw [(lemma161_local_tail_succ_hasSum a t hat n).tsum_eq,pow_succ,mul_pow]
      ring
    · simp only [div_eq_mul_inv,mul_inv_rev]
      ring
  have hξ : HasSum (fun n => lemma161Coefficient χ β 1 1 (p^(n+1))*x^(n+1))
      (l*((a-1)*x/((1-a*t)*(1-a*x))-A*x*K)) := by
    convert (hs.sub (hk.mul_left (A*x))).mul_left l using 1
    funext n
    rw [lemma161_coefficient_prime_power χ β hp,lemma161_mobius_weight χ hp,pow_succ]
    dsimp [l,t,A]
    simp only [zpow_neg_one]
    ring
  have hξall := (hasSum_nat_add_iff
    (f := fun n => lemma161Coefficient χ β 1 1 (p^n)*x^n) 1).mp hξ
  convert hξall using 1
  simp only [sum_range_succ,sum_range_zero,pow_zero,lemma161_coefficient_one,one_mul,zero_add]
  dsimp [l,K,A,t,a]
  rw [lemma161_lambda_factor_rational χ β hp.pos]
  unfold lemma161XiRational
  ring

lemma lemma161_local_correction_identity (a u v x : ℂ)
    (hv : v = 0 ∨ v = 1 ∨ v = -1)
    (hu : 1-u ≠ 0) (hx : 1-x ≠ 0) (hvu : 1-v*u ≠ 0)
    (hvx : 1-v*x ≠ 0) (hax : 1-a*x ≠ 0) (hat : 1-a*(v*u) ≠ 0) :
    (1-a*x)/((1-x)*(1-v*x)) * lemma161XiRational a u v x =
      lemma152LocalCorrection a 0 u v x := by
  unfold lemma161XiRational lemma152LocalCorrection
  rcases hv with rfl | rfl | rfl
  all_goals
    simp only [zero_mul,one_mul,neg_one_mul,mul_neg,sub_zero,sub_neg_eq_add,zero_pow,
      zero_div,mul_zero,add_zero,sub_self,zero_sub] at *
    repeat' field_simp [hu,hx,hvu,hvx,hax,hat,mul_comm]
    all_goals ring

/-- Cancellation proved from actual κ₂, ξ₂ and λ̃₂. The b=0 specialization
of the general rational correction is algebraic, not a second paper shift. -/
lemma lemma161_actual_local_correction {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : ℂ) (hβ : β.re = 0) (hp : p.Prime) (x : ℂ) (hx : ‖x‖ < 1) :
    (1-(p:ℂ)^(-β)*x)/((1-x)*(1-χ.evalNat p*x)) *
      (∑' n : ℕ, lemma161Coefficient χ β 1 1 (p^n)*x^n) =
        lemma152LocalCorrection ((p:ℂ)^(-β)) 0 (p:ℂ)⁻¹ (χ.evalNat p) x := by
  have hu : ‖(p:ℂ)⁻¹‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hvu : ‖χ.evalNat p*(p:ℂ)⁻¹‖ < 1 :=
    lt_of_le_of_lt (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)) hu
  have hvx : ‖χ.evalNat p*x‖ < 1 :=
    lt_of_le_of_lt (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)) hx
  have hnorm := lemma83_cpow_shift_norm hp.pos β hβ
  have hax : ‖(p:ℂ)^(-β)*x‖ < 1 := by simpa [norm_mul,hnorm] using hx
  have hat : ‖(p:ℂ)^(-β)*(χ.evalNat p*(p:ℂ)⁻¹)‖ < 1 := by
    simpa [norm_mul,hnorm] using hvu
  rw [(lemma161_coefficient_prime_hasSum χ β hβ hp x hx).tsum_eq]
  exact lemma161_local_correction_identity _ _ _ _
    (MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (p:ZMod D))
    (lemma83_one_sub_ne_zero hu) (lemma83_one_sub_ne_zero hx)
    (lemma83_one_sub_ne_zero hvu) (lemma83_one_sub_ne_zero hvx)
    (lemma83_one_sub_ne_zero hax) (lemma83_one_sub_ne_zero hat)

end ZhangLS.Spec
