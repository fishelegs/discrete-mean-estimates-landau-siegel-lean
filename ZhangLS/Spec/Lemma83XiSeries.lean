import ZhangLS.Spec.Lemma83XiPrimePower
import ZhangLS.Spec.Lemma83ShiftedTail
import ZhangLS.Spec.Lemma83LocalCorrection
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma83ActualKappaRational (β : Fin 3 → ℂ) (p : ℕ) (x : ℂ) : ℂ :=
  lemma83KappaRational ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) ((p:ℂ)^(-β 2)) x

lemma lemma83_actual_kappa_hasSum (β : Fin 3 → ℂ) {p : ℕ} (hp : p.Prime) (x : ℂ)
    (h : ∀ i : Fin 3, ‖(p:ℂ)^(-β i)*x‖ < 1) :
    HasSum (fun n => lemma83Kappa β (p^n)*x^n) (lemma83ActualKappaRational β p x) :=
  lemma83_kappa_prime_power_hasSum β hp x (h 0) (h 1) (h 2)

lemma lemma83_xi_r_hasSum (β : Fin 3 → ℂ) (j : Fin 3) {p : ℕ}
    (hp : p.Prime) (d r : ℕ) (hpr : p ∣ r) (x : ℂ)
    (hx : ∀ i : Fin 3, ‖(p:ℂ)^(-β i)*x‖ < 1) :
    HasSum (fun n => lemma83Xi β j (p^n) d r*x^n) (lemma83ActualKappaRational β p x) := by
  convert lemma83_actual_kappa_hasSum β hp x hx using 1
  funext n
  cases n with
  | zero => simp
  | succ n => rw [lemma83_xi_prime_power_r β j hp n d r hpr]

lemma lemma83_xi_d_hasSum (β : Fin 3 → ℂ) (j : Fin 3) {p : ℕ}
    (hp : p.Prime) (d r : ℕ) (hpd : p ∣ d) (hpr : ¬p ∣ r) (x : ℂ)
    (hx : ∀ i : Fin 3, ‖(p:ℂ)^(-β i)*x‖ < 1) :
    HasSum (fun n => lemma83Xi β j (p^n) d r*x^n)
      ((1 - ((p:ℂ)^(1-β j)/(p-1 : ℕ))*x)*lemma83ActualKappaRational β p x) := by
  let K := lemma83ActualKappaRational β p x
  let A : ℂ := (p:ℂ)^(1-β j)/(p-1 : ℕ)
  have hk := lemma83_actual_kappa_hasSum β hp x hx
  have ht : HasSum (fun n => lemma83Kappa β (p^(n+1))*x^(n+1)) (K-1) := by
    simpa [K] using (hasSum_nat_add_iff' 1).mpr hk
  have hh : HasSum (fun n => lemma83Xi β j (p^(n+1)) d r*x^(n+1)) (K-1-A*x*K) := by
    convert ht.sub (hk.mul_left (A*x)) using 1
    funext n
    rw [lemma83_xi_prime_power_d β j hp n d r hpd hpr,pow_succ]
    dsimp [A]
    ring
  have hall := (hasSum_nat_add_iff (f := fun n => lemma83Xi β j (p^n) d r*x^n) 1).mp hh
  convert hall using 1
  simp only [sum_range_succ,sum_range_zero,pow_zero,lemma83_xi_one,one_mul,zero_add]
  dsimp [K,A]
  ring

lemma lemma83_actual_kappa_tail_hasSum (β : Fin 3 → ℂ) {p : ℕ}
    (hp : p.Prime) (hβ : ∀ i : Fin 3, ‖(p:ℂ)^(-β i)‖ = 1)
    (x t : ℂ) (hx : ‖x‖ < 1) (ht : ‖t‖ < 1) (hxt : x ≠ t) :
    HasSum (fun n => (∑' k : ℕ, lemma83Kappa β (p^(n+k))*t^k)*x^n)
      ((x*lemma83ActualKappaRational β p x-t*lemma83ActualKappaRational β p t)/(x-t)) := by
  simpa only [lemma83_kappa_prime_power β hp,lemma83ActualKappaRational,
    lemma83KappaRational] using
    lemma83_local_kappa_shifted_tail_hasSum ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1))
      ((p:ℂ)^(-β 2)) x t (hβ 0) (hβ 1) (hβ 2) hx ht hxt

/-- Actual ξ local generating series at a prime outside dr, before rational cancellation. -/
lemma lemma83_xi_regular_hasSum (β : Fin 3 → ℂ) (j : Fin 3) {p : ℕ}
    (hp : p.Prime) (hβ : ∀ i : Fin 3, ‖(p:ℂ)^(-β i)‖ = 1)
    (d r : ℕ) (hpd : ¬p ∣ d*r) (x : ℂ) (hx : ‖x‖ < 1)
    (ht : ‖(p:ℂ)^(-(1-β j))‖ < 1) (hxt : x ≠ (p:ℂ)^(-(1-β j))) :
    HasSum (fun n => lemma83Xi β j (p^n) d r*x^n)
      (1 + lemma83LambdaFactor β p (1-β j) *
        ((x*lemma83ActualKappaRational β p x -
          (p:ℂ)^(-(1-β j))*lemma83ActualKappaRational β p ((p:ℂ)^(-(1-β j)))) /
          (x-(p:ℂ)^(-(1-β j))) - lemma83ActualKappaRational β p ((p:ℂ)^(-(1-β j))) -
          ((p:ℂ)^(1-β j)/(p-1 : ℕ))*x*lemma83ActualKappaRational β p x)) := by
  let t : ℂ := (p:ℂ)^(-(1-β j))
  let A : ℂ := (p:ℂ)^(1-β j)/(p-1 : ℕ)
  let K := lemma83ActualKappaRational β p x
  let T := lemma83ActualKappaRational β p t
  let V := (x*K-t*T)/(x-t)
  let l := lemma83LambdaFactor β p (1-β j)
  have hk := lemma83_actual_kappa_hasSum β hp x
    (fun i => by simpa [norm_mul,hβ i] using hx)
  have hkt := lemma83_actual_kappa_hasSum β hp t
    (fun i => by simpa [norm_mul,hβ i,t] using ht)
  have hall := lemma83_actual_kappa_tail_hasSum β hp hβ x t hx ht hxt
  have hs : HasSum (fun n => (∑' k : ℕ, lemma83Kappa β (p^(n+1+k))*t^k)*x^(n+1))
      (V-T) := by
    have hh := (hasSum_nat_add_iff' 1).mpr hall
    simpa [V,K,T,hkt.tsum_eq] using hh
  have hξ : HasSum (fun n => lemma83Xi β j (p^(n+1)) d r*x^(n+1))
      (l*(V-T-A*x*K)) := by
    convert (hs.sub (hk.mul_left (A*x))).mul_left l using 1
    funext n
    rw [lemma83_xi_prime_power_regular β j hp n d r hpd,pow_succ]
    dsimp [l,t,A]
    ring
  have hξall := (hasSum_nat_add_iff
    (f := fun n => lemma83Xi β j (p^n) d r*x^n) 1).mp hξ
  convert hξall using 1
  simp only [sum_range_succ,sum_range_zero,pow_zero,lemma83_xi_one,one_mul,zero_add]
  dsimp [l,V,K,T,A,t]
  ring

end ZhangLS.Spec
