import ZhangLS.Spec.Lemma152Definitions
import ZhangLS.Spec.Lemma83ShiftedTail
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 1000000

/-- The two-shift local coefficient of (1-X)/((1-aX)(1-bX)). -/
noncomputable def lemma152LocalKappa (a b : ℂ) : ℕ → ℂ
  | 0 => 1
  | n+1 => lemma83LocalH2 a b (n+1) - lemma83LocalH2 a b n

@[simp] lemma lemma152_local_kappa_zero (a b : ℂ) : lemma152LocalKappa a b 0 = 1 := rfl

lemma lemma152_local_kappa_succ (a b : ℂ) (n : ℕ) :
    lemma152LocalKappa a b (n+1) = lemma83LocalH2 a b (n+1) - lemma83LocalH2 a b n := rfl

noncomputable def lemma152KappaRational (a b x : ℂ) : ℂ :=
  (1-x)/((1-a*x)*(1-b*x))

lemma lemma152_local_kappa_hasSum (a b x : ℂ)
    (ha : ‖a*x‖ < 1) (hb : ‖b*x‖ < 1) :
    HasSum (fun n => lemma152LocalKappa a b n*x^n) (lemma152KappaRational a b x) := by
  let H := (1-a*x)⁻¹*(1-b*x)⁻¹
  have hh : HasSum (fun n => lemma83LocalH2 a b n*x^n) H :=
    lemma83_local_h2_hasSum a b x ha hb
  have ht : HasSum (fun n => lemma83LocalH2 a b (n+1)*x^(n+1)) (H-1) := by
    simpa using (hasSum_nat_add_iff' 1).mpr hh
  have hk : HasSum (fun n => lemma152LocalKappa a b (n+1)*x^(n+1))
      (H-1-x*H) := by
    convert ht.sub (hh.mul_left x) using 1
    funext n
    rw [lemma152_local_kappa_succ,pow_succ]
    ring
  have hall : HasSum (fun n => lemma152LocalKappa a b n*x^n) (H-1-x*H+1) := by
    simpa using (hasSum_nat_add_iff (f := fun n => lemma152LocalKappa a b n*x^n) 1).mp hk
  convert hall using 1
  dsimp [H,lemma152KappaRational]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

lemma lemma152_double_power_coefficient_prime_power (β : Fin 2 → ℂ) {p : ℕ}
    (hp : p.Prime) (n : ℕ) :
    (lemma83PowerCoefficient (β 0)*lemma83PowerCoefficient (β 1)) (p^n) =
      lemma83LocalH2 ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) n := by
  rw [lemma83_convolution_prime_power _ _ hp]
  simp only [lemma83_power_coefficient_prime_power _ hp,lemma83LocalH2]

/-- The local model is proved equal to the actual arithmetic coefficient. -/
lemma lemma152_kappa_prime_power (β : Fin 2 → ℂ) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    lemma152Kappa β (p^n) =
      lemma152LocalKappa ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) n := by
  cases n with
  | zero => simp
  | succ n =>
    rw [lemma152Kappa,lemma83_moebius_convolution_prime_power_succ _ hp,
      lemma152_double_power_coefficient_prime_power β hp,
      lemma152_double_power_coefficient_prime_power β hp,lemma152_local_kappa_succ]

lemma lemma152_kappa_prime_power_hasSum (β : Fin 2 → ℂ) {p : ℕ}
    (hp : p.Prime) (x : ℂ) (h : ∀ i, ‖(p:ℂ)^(-β i)*x‖ < 1) :
    HasSum (fun n => lemma152Kappa β (p^n)*x^n)
      (lemma152KappaRational ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) x) := by
  simpa only [lemma152_kappa_prime_power β hp] using
    lemma152_local_kappa_hasSum ((p:ℂ)^(-β 0)) ((p:ℂ)^(-β 1)) x (h 0) (h 1)

lemma lemma152_local_kappa_double_summable (a b x t : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hx : ‖x‖ < 1) (ht : ‖t‖ < 1) :
    Summable (fun ij : ℕ × ℕ => lemma152LocalKappa a b (ij.1+ij.2)*x^ij.1*t^ij.2) := by
  obtain ⟨ρ,hρmax,hρ1⟩ := exists_between (max_lt hx ht)
  have hρ : 0 < ρ := lt_of_le_of_lt (le_trans (norm_nonneg x) (le_max_left _ _)) hρmax
  have hn : ‖(ρ : ℂ)‖ = ρ := by simp [Real.norm_eq_abs,hρ.le]
  apply lemma83_shifted_double_summable _ x t ρ hρ
    (lt_of_le_of_lt (le_max_left _ _) hρmax) (lt_of_le_of_lt (le_max_right _ _) hρmax)
  have hh := summable_norm_iff.mpr (lemma152_local_kappa_hasSum a b (ρ:ℂ)
    (by simpa only [norm_mul,ha,hn,one_mul] using hρ1)
    (by simpa only [norm_mul,hb,hn,one_mul] using hρ1)).summable
  simpa only [norm_mul,norm_pow,hn] using hh

/-- Exact convergent shifted series, used on the absolute convergence half-plane.
The off-diagonal hypothesis is discharged there before analytic continuation. -/
lemma lemma152_local_kappa_tail_hasSum (a b x t : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hx : ‖x‖ < 1) (ht : ‖t‖ < 1) (hxt : x ≠ t) :
    HasSum (fun r : ℕ => (∑' η : ℕ, lemma152LocalKappa a b (r+η)*t^η)*x^r)
      ((x*lemma152KappaRational a b x-t*lemma152KappaRational a b t)/(x-t)) := by
  apply lemma83_shifted_tail_hasSum _ x t _ _ hxt
  · exact lemma152_local_kappa_hasSum a b x
      (by simpa [norm_mul,ha] using hx) (by simpa [norm_mul,hb] using hx)
  · exact lemma152_local_kappa_hasSum a b t
      (by simpa [norm_mul,ha] using ht) (by simpa [norm_mul,hb] using ht)
  · exact lemma152_local_kappa_double_summable a b x t ha hb hx ht

@[simp] lemma lemma152_local_kappa_one (n : ℕ) : lemma152LocalKappa 1 1 n = 1 := by
  cases n with
  | zero => rfl
  | succ n => simp [lemma152_local_kappa_succ,lemma83_local_h2_one]

end ZhangLS.Spec
