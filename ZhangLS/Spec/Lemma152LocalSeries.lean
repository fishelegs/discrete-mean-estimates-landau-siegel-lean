import ZhangLS.Spec.Lemma152XiPrimePower
import ZhangLS.Spec.Lemma152LocalCorrection
import ZhangLS.Spec.Lemma83LocalAgreement
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

@[simp] lemma lemma152_coefficient_one {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d l : ℕ) : lemma152Coefficient χ β d l 1 = 1 := by
  simp [lemma152Coefficient,lemma152ModifiedLambda]

@[simp] lemma lemma152_coefficient_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (d l : ℕ) : lemma152Coefficient χ β d l 0 = 0 := by
  simp [lemma152Coefficient]

lemma lemma152_lambda_factor_rational {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hp : 0 < p) :
    lemma152LambdaFactor χ β p 1 =
      (1-(p:ℂ)^(-β 0)*(χ.evalNat p*(p:ℂ)⁻¹))*
        (1-(p:ℂ)^(-β 1)*(χ.evalNat p*(p:ℂ)⁻¹))/(1-χ.evalNat p*(p:ℂ)⁻¹) := by
  have hn : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne'
  have h (i : Fin 2) : (p:ℂ)^(-1-β i) = (p:ℂ)^(-β i)*(p:ℂ)⁻¹ := by
    rw [show (-1:ℂ)-β i = -β i + -1 by ring,Complex.cpow_add _ _ hn,
      Complex.cpow_neg_one]
  simp only [lemma152LambdaFactor,h,Complex.cpow_neg_one]
  congr 2 <;> ring

lemma lemma152_mobius_weight {D p : ℕ} (χ : RealPrimitiveCharacter D) (hp : p.Prime) :
    χ.evalNat p*(p:ℂ)/(p-1:ℕ) = χ.evalNat p/(1-(p:ℂ)⁻¹) := by
  have hn : (p:ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hp1 : (p:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [Nat.cast_sub hp.one_le,Nat.cast_one]
  repeat' field_simp [hn,hp1]
  all_goals ring

/-- The actual prime coefficient series converges to the rational expression. -/
lemma lemma152_coefficient_prime_hasSum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime)
    (x : ℂ) (hx : ‖x‖ < 1) (hxt : x ≠ χ.evalNat p*(p:ℂ)⁻¹) :
    HasSum (fun n : ℕ => lemma152Coefficient χ β 1 1 (p^n)*x^n)
      (lemma152XiRational ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (p:ℂ)⁻¹ (χ.evalNat p) x) := by
  let a := (p:ℂ)^(-β 0)
  let b := (p:ℂ)^(-β 1)
  let t := χ.evalNat p*(p:ℂ)⁻¹
  let K := lemma152KappaRational a b x
  let T := lemma152KappaRational a b t
  let V := lemma152TailRational a b t x
  let A := χ.evalNat p/(1-(p:ℂ)⁻¹)
  let l := lemma152LambdaFactor χ β p 1
  have hnorm (i : Fin 2) := lemma83_cpow_shift_norm hp.pos (β i) (hβ i)
  have ht : ‖t‖ < 1 := by
    dsimp [t]
    rw [norm_mul,norm_inv,Complex.norm_natCast]
    apply lt_of_le_of_lt (mul_le_of_le_one_left (by positivity) (χ.evalNat_norm_le_one p))
    exact (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hk : HasSum (fun n => lemma152Kappa β (p^n)*x^n) K :=
    lemma152_kappa_prime_power_hasSum β hp x (fun i => by simpa [norm_mul,hnorm i] using hx)
  have hkt : HasSum (fun n => lemma152Kappa β (p^n)*t^n) T :=
    lemma152_kappa_prime_power_hasSum β hp t (fun i => by simpa [norm_mul,hnorm i] using ht)
  have hall : HasSum (fun n => (∑' k : ℕ, lemma152Kappa β (p^(n+k))*t^k)*x^n) V := by
    simpa only [lemma152_kappa_prime_power β hp,V,lemma152TailRational,a,b] using
      lemma152_local_kappa_tail_hasSum a b x t (hnorm 0) (hnorm 1) hx ht hxt
  have hs : HasSum (fun n => (∑' k : ℕ, lemma152Kappa β (p^(n+1+k))*t^k)*x^(n+1)) (V-T) := by
    simpa [hkt.tsum_eq] using (hasSum_nat_add_iff' 1).mpr hall
  have hξ : HasSum (fun n => lemma152Coefficient χ β 1 1 (p^(n+1))*x^(n+1))
      (l*(V-T-A*x*K)) := by
    convert (hs.sub (hk.mul_left (A*x))).mul_left l using 1
    funext n
    rw [lemma152_coefficient_prime_power χ β hp,lemma152_mobius_weight χ hp,pow_succ]
    dsimp [l,t,A]
    simp only [zpow_neg_one]
    ring
  have hξall := (hasSum_nat_add_iff
    (f := fun n => lemma152Coefficient χ β 1 1 (p^n)*x^n) 1).mp hξ
  convert hξall using 1
  simp only [sum_range_succ,sum_range_zero,pow_zero,lemma152_coefficient_one,one_mul,zero_add]
  dsimp [l,V,K,T,A,t,a,b]
  rw [lemma152_lambda_factor_rational χ β hp.pos]
  unfold lemma152XiRational
  ring

/-- Exact Euler correction obtained from the original Section 15 series. -/
lemma lemma152_actual_local_correction {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime)
    (x : ℂ) (hx : ‖x‖ < 1) (hxt : x ≠ χ.evalNat p*(p:ℂ)⁻¹) :
    lemma152LocalRemoval ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (χ.evalNat p) x *
      (∑' n : ℕ, lemma152Coefficient χ β 1 1 (p^n)*x^n) =
        lemma152LocalCorrection ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (p:ℂ)⁻¹ (χ.evalNat p) x := by
  have hu : ‖(p:ℂ)⁻¹‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hvu : ‖χ.evalNat p*(p:ℂ)⁻¹‖ < 1 :=
    lt_of_le_of_lt (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)) hu
  have hvx : ‖χ.evalNat p*x‖ < 1 :=
    lt_of_le_of_lt (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)) hx
  have hnorm (i : Fin 2) := lemma83_cpow_shift_norm hp.pos (β i) (hβ i)
  have hix (i : Fin 2) : ‖(p:ℂ)^(-β i)*x‖ < 1 := by simpa [norm_mul,hnorm i] using hx
  have hit (i : Fin 2) : ‖(p:ℂ)^(-β i)*(χ.evalNat p*(p:ℂ)⁻¹)‖ < 1 := by
    simpa [norm_mul,hnorm i] using hvu
  rw [(lemma152_coefficient_prime_hasSum χ β hβ hp x hx hxt).tsum_eq]
  exact lemma152_local_correction_identity _ _ _ _ _
    (MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (p:ZMod D))
    (sub_ne_zero.mpr hxt) (lemma83_one_sub_ne_zero hu) (lemma83_one_sub_ne_zero hx)
    (lemma83_one_sub_ne_zero hvu) (lemma83_one_sub_ne_zero hvx)
    (lemma83_one_sub_ne_zero (hix 0)) (lemma83_one_sub_ne_zero (hix 1))
    (lemma83_one_sub_ne_zero (hit 0)) (lemma83_one_sub_ne_zero (hit 1))

end ZhangLS.Spec
