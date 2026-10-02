import ZhangLS.Spec.Lemma153TailDiagonal
import ZhangLS.Spec.Lemma153NormalizationNonzero
/-! Actual baseline local series and correction on the whole unit disc.
The former x≠χ(q)/q restriction is completely removed. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 3000000

noncomputable def lemma153BaseClosed (a b u v x : ℂ) : ℂ :=
  1 + ((1-a*(v*u))*(1-b*(v*u))/(1-v*u)) *
    (lemma153TailClosed a b x (v*u) - lemma152KappaRational a b (v*u) -
      (v/(1-u))*x*lemma152KappaRational a b x)

/-- The actual prime coefficient series converges to the rational expression. -/
lemma lemma153_base_closed_hasSum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime)
    (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => lemma152Coefficient χ β 1 1 (p^n)*x^n)
      (lemma153BaseClosed ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (p:ℂ)⁻¹ (χ.evalNat p) x) := by
  let a := (p:ℂ)^(-β 0)
  let b := (p:ℂ)^(-β 1)
  let t := χ.evalNat p*(p:ℂ)⁻¹
  let K := lemma152KappaRational a b x
  let T := lemma152KappaRational a b t
  let V := lemma153TailClosed a b x t
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
    simpa only [lemma152_kappa_prime_power β hp,V,lemma153TailClosed,a,b] using
      lemma153_tail_closed_hasSum a b x t (hnorm 0) (hnorm 1) hx ht
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
  unfold lemma153BaseClosed
  ring


lemma lemma153_base_closed_correction_identity (a b u v x : ℂ)
    (hv : v = 0 ∨ v = 1 ∨ v = -1)
    (hu : 1-u ≠ 0) (hx : 1-x ≠ 0) (hvu : 1-v*u ≠ 0)
    (hvx : 1-v*x ≠ 0) (hax : 1-a*x ≠ 0) (hbx : 1-b*x ≠ 0)
    (hau : 1-a*(v*u) ≠ 0) (hbu : 1-b*(v*u) ≠ 0) :
    lemma152LocalRemoval a b v x * lemma153BaseClosed a b u v x =
      lemma152LocalCorrection a b u v x := by
  unfold lemma152LocalRemoval lemma153BaseClosed lemma153TailClosed
    lemma152KappaRational lemma152LocalCorrection
  rcases hv with rfl | rfl | rfl
  all_goals
    simp only [zero_mul,one_mul,neg_one_mul,mul_neg,sub_zero,sub_neg_eq_add,zero_pow,
      zero_div,mul_zero,add_zero,sub_self,zero_sub] at *
    repeat' field_simp [hu,hx,hvu,hvx,hax,hbx,hau,hbu,mul_comm]
    all_goals ring

/-- The actual prime series gives the rational M-correction at every point
|x|<1, including the formerly excluded diagonal. -/
lemma lemma153_actual_local_correction {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime)
    (x : ℂ) (hx : ‖x‖ < 1) :
    lemma152LocalRemoval ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (χ.evalNat p) x *
      (∑' n : ℕ, lemma152Coefficient χ β 1 1 (p^n)*x^n) =
        lemma152LocalCorrection ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1))
          (p:ℂ)⁻¹ (χ.evalNat p) x := by
  have hu : ‖(p:ℂ)⁻¹‖ < 1 := by
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr hp.pos)).mpr (by exact_mod_cast hp.one_lt)
  have hvu : ‖χ.evalNat p*(p:ℂ)⁻¹‖ < 1 := lt_of_le_of_lt
    (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)) hu
  have hvx : ‖χ.evalNat p*x‖ < 1 := lt_of_le_of_lt
    (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one p)) hx
  have hnorm (i : Fin 2) := lemma83_cpow_shift_norm hp.pos (β i) (hβ i)
  have hix (i : Fin 2) : ‖(p:ℂ)^(-β i)*x‖ < 1 := by simpa [norm_mul,hnorm i] using hx
  have hit (i : Fin 2) : ‖(p:ℂ)^(-β i)*(χ.evalNat p*(p:ℂ)⁻¹)‖ < 1 := by
    simpa [norm_mul,hnorm i] using hvu
  rw [(lemma153_base_closed_hasSum χ β hβ hp x hx).tsum_eq]
  exact lemma153_base_closed_correction_identity _ _ _ _ _
    (MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (p:ZMod D))
    (lemma83_one_sub_ne_zero hu) (lemma83_one_sub_ne_zero hx)
    (lemma83_one_sub_ne_zero hvu) (lemma83_one_sub_ne_zero hvx)
    (lemma83_one_sub_ne_zero (hix 0)) (lemma83_one_sub_ne_zero (hix 1))
    (lemma83_one_sub_ne_zero (hit 0)) (lemma83_one_sub_ne_zero (hit 1))

lemma lemma153_base_local_nonzero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (q : Nat.Primes)
    (s : ℂ) (hs : 9/10 ≤ s.re) (hM : lemma152EulerProduct χ β s ≠ 0) :
    (∑' n : ℕ, lemma152Coefficient χ β 1 1 (q.val^n)*
      lemma32PrimeMonomial q.val s^n) ≠ 0 := by
  intro hz
  have hq := lemma153_prime_factor_nonzero_of_product χ β s hM q
  apply hq
  unfold lemma152PrimeFactor
  rw [lemma32_prime_monomial_eq_cpow q.property.pos (β 0),
    lemma32_prime_monomial_eq_cpow q.property.pos (β 1),
    ← lemma153_actual_local_correction χ β hβ q.property
      (lemma32PrimeMonomial q.val s)
      ((lemma152_monomial_norm_radius q s hs).trans_lt lemma83_regular_radius_lt_one),hz,mul_zero]

end ZhangLS.Spec
