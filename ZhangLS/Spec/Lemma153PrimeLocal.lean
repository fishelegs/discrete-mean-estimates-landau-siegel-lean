import ZhangLS.Spec.Lemma153Definitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1500000

noncomputable def lemma153LocalLambda (a b u v : ℂ) : ℂ :=
  (1-a*(v*u))*(1-b*(v*u))/(1-v*u)
noncomputable def lemma153LocalB (a b u v y : ℂ) : ℂ :=
  lemma152XiRational a b u v y
noncomputable def lemma153LocalF (a b y : ℂ) : ℂ :=
  lemma152KappaRational a b y
noncomputable def lemma153LocalE (a b u v y : ℂ) : ℂ :=
  (1-v*y/(1-u))*lemma153LocalF a b y
noncomputable def lemma153LocalC (a b u v y : ℂ) : ℂ :=
  lemma153LocalB a b u v y + lemma153LocalLambda a b u v *
    (v*y/(1-u))*lemma153LocalF a b y

lemma lemma153_local_compatibility (a b u v y : ℂ) :
    lemma153LocalB a b u v y = lemma153LocalC a b u v y +
      lemma153LocalLambda a b u v * lemma153LocalE a b u v y -
        lemma153LocalLambda a b u v * lemma153LocalF a b y := by
  unfold lemma153LocalC lemma153LocalE
  ring

lemma lemma153_coefficient_prime_power_d {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hp : p.Prime) (e d l : ℕ) (hpd : p ∣ d) :
    lemma152Coefficient χ β d l (p^(e+1)) =
      lemma152Kappa β (p^(e+1)) -
        if p.Coprime l then χ.evalNat p/(1-(p:ℂ)⁻¹)*lemma152Kappa β (p^e) else 0 := by
  unfold lemma152Coefficient
  rw [lemma152_modified_lambda_prime_power χ β hp,if_pos hpd,one_mul,
    lemma152_xi_prime_power χ β hp,
    lemma152_modified_kappa_prime_power_excluded χ β hp hpd,
    lemma152_mobius_weight χ hp]

lemma lemma153_coefficient_prime_power_l {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hp : p.Prime) (e l : ℕ) (hpl : p ∣ l) :
    lemma152Coefficient χ β 1 l (p^(e+1)) =
      lemma152Coefficient χ β 1 1 (p^(e+1)) +
        lemma152LambdaFactor χ β p 1 *
          (χ.evalNat p/(1-(p:ℂ)⁻¹))*lemma152Kappa β (p^e) := by
  have hcop : ¬ p.Coprime l := by simpa [hp.coprime_iff_not_dvd] using hpl
  unfold lemma152Coefficient
  rw [lemma152_modified_lambda_prime_power χ β hp,if_neg hp.not_dvd_one]
  rw [lemma152_xi_prime_power χ β hp,if_neg hcop,
    lemma152_xi_prime_power χ β hp,if_pos (Nat.coprime_one_right p),
    lemma152_mobius_weight χ hp]
  ring

lemma lemma153_coefficient_d_hasSum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime)
    (d l : ℕ) (hpd : p ∣ d) (x : ℂ) (hx : ‖x‖ < 1) :
    HasSum (fun n : ℕ => lemma152Coefficient χ β d l (p^n)*x^n)
      ((1-(if p.Coprime l then χ.evalNat p/(1-(p:ℂ)⁻¹) else 0)*x)*
        lemma152KappaRational ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) x) := by
  let A := if p.Coprime l then χ.evalNat p/(1-(p:ℂ)⁻¹) else 0
  let K := lemma152KappaRational ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) x
  have hk : HasSum (fun n => lemma152Kappa β (p^n)*x^n) K :=
    lemma152_kappa_prime_power_hasSum β hp x (fun i => by
      simpa [norm_mul,lemma83_cpow_shift_norm hp.pos (β i) (hβ i)] using hx)
  have hkt : HasSum (fun n => lemma152Kappa β (p^(n+1))*x^(n+1)) (K-1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hk
  have hs : HasSum (fun n => lemma152Coefficient χ β d l (p^(n+1))*x^(n+1))
      (K-1-A*x*K) := by
    convert hkt.sub (hk.mul_left (A*x)) using 1
    funext n
    rw [lemma153_coefficient_prime_power_d χ β hp n d l hpd,pow_succ]
    dsimp [A]
    split_ifs <;> ring
  convert (hasSum_nat_add_iff (f := fun n => lemma152Coefficient χ β d l (p^n)*x^n) 1).mp hs using 1
  simp only [sum_range_succ,sum_range_zero,pow_zero,lemma152_coefficient_one,one_mul,zero_add]
  dsimp [A,K]
  ring

lemma lemma153_coefficient_l_hasSum {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (hβ : ∀ i, (β i).re = 0) (hp : p.Prime)
    (l : ℕ) (hpl : p ∣ l) (x : ℂ) (hx : ‖x‖ < 1)
    (hxt : x ≠ χ.evalNat p*(p:ℂ)⁻¹) :
    HasSum (fun n : ℕ => lemma152Coefficient χ β 1 l (p^n)*x^n)
      (lemma153LocalC ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (p:ℂ)⁻¹ (χ.evalNat p) x) := by
  let B := lemma152XiRational ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) (p:ℂ)⁻¹ (χ.evalNat p) x
  let K := lemma152KappaRational ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) x
  let lam := lemma152LambdaFactor χ β p 1
  let A := χ.evalNat p/(1-(p:ℂ)⁻¹)
  have hb := lemma152_coefficient_prime_hasSum χ β hβ hp x hx hxt
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
  dsimp [B,lam,A,K,lemma153LocalC,lemma153LocalB,lemma153LocalF,lemma153LocalLambda]
  rw [lemma152_lambda_factor_rational χ β hp.pos]
  ring

end ZhangLS.Spec
