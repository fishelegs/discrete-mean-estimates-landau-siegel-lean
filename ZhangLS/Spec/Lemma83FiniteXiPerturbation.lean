import ZhangLS.Spec.Lemma83FiniteShiftLambda
import ZhangLS.Spec.Lemma32Geometric

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

noncomputable def lemma83PrimeShiftMass (β : Fin 3 → ℂ) (p : ℕ) : ℝ :=
  ‖(p:ℂ)^(-β 0)-1‖+‖(p:ℂ)^(-β 1)-1‖+‖(p:ℂ)^(-β 2)-1‖

lemma lemma83_norm_pow_sub_one (a : ℂ) (ha : ‖a‖ ≤ 1) (n : ℕ) :
    ‖a^n-1‖ ≤ (n:ℝ)*‖a-1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ,show a^n*a-1 = (a^n-1)*a+(a-1) by ring]
    calc
      _ ≤ ‖(a^n-1)*a‖+‖a-1‖ := norm_add_le _ _
      _ ≤ (n:ℝ)*‖a-1‖+‖a-1‖ := by
        rw [norm_mul]
        have hh := (mul_le_mul ih ha (norm_nonneg _) (by positivity)).trans_eq (mul_one _)
        linarith
      _ = _ := by push_cast; ring

lemma lemma83_unit_mul_sub_one (a b : ℂ) (ha : ‖a‖ ≤ 1) :
    ‖a*b-1‖ ≤ ‖a-1‖+‖b-1‖ := by
  rw [show a*b-1 = a*(b-1)+(a-1) by ring]
  apply (norm_add_le _ _).trans
  rw [norm_mul]
  have hh := mul_le_mul_of_nonneg_right ha (norm_nonneg (b-1))
  linarith

lemma lemma83_local_h2_perturbation (a b : ℂ) (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1)
    (n : ℕ) :
    ‖lemma83LocalH2 a b n-(n+1:ℂ)‖ ≤ (n+1:ℝ)^2*(‖a-1‖+‖b-1‖) := by
  rw [← lemma83_local_h2_one]
  unfold lemma83LocalH2 lemma83AddConvolution
  rw [←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ ij ∈ antidiagonal n, (n+1:ℝ)*(‖a-1‖+‖b-1‖) := by
      apply sum_le_sum
      intro ij hij
      have hi : (ij.1:ℝ) ≤ n+1 := by exact_mod_cast (show ij.1 ≤ n+1 by have := mem_antidiagonal.mp hij; omega)
      have hj : (ij.2:ℝ) ≤ n+1 := by exact_mod_cast (show ij.2 ≤ n+1 by have := mem_antidiagonal.mp hij; omega)
      simp only [one_pow,mul_one]
      have hh := lemma83_unit_mul_sub_one (a^ij.1) (b^ij.2)
        (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ha)
      have hi' := lemma83_norm_pow_sub_one a ha ij.1
      have hj' := lemma83_norm_pow_sub_one b hb ij.2
      nlinarith [mul_le_mul_of_nonneg_right hi (norm_nonneg (a-1)),
        mul_le_mul_of_nonneg_right hj (norm_nonneg (b-1))]
    _ = _ := by simp; ring

lemma lemma83_local_h3_perturbation (a b c : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    ‖lemma83LocalH3 a b c n-lemma83LocalH3 1 1 1 n‖ ≤
      (n+1:ℝ)^3*(‖a-1‖+‖b-1‖+‖c-1‖) := by
  unfold lemma83LocalH3 lemma83AddConvolution
  rw [←sum_sub_distrib]
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ ij ∈ antidiagonal n, (n+1:ℝ)^2*(‖a-1‖+‖b-1‖+‖c-1‖) := by
      apply sum_le_sum
      intro ij hij
      have hiN : ij.1 ≤ n := by have := mem_antidiagonal.mp hij; omega
      have hjN : ij.2 ≤ n := by have := mem_antidiagonal.mp hij; omega
      have hi : (ij.1:ℝ)+1 ≤ n+1 := by exact_mod_cast Nat.add_le_add_right hiN 1
      have hj : (ij.2:ℝ) ≤ n+1 := by exact_mod_cast hjN.trans (Nat.le_succ n)
      simp only [lemma83_local_h2_one,one_pow,mul_one]
      rw [show lemma83LocalH2 a b ij.1*c^ij.2-(ij.1+1:ℂ) =
        (lemma83LocalH2 a b ij.1-(ij.1+1:ℂ))*c^ij.2+(ij.1+1:ℂ)*(c^ij.2-1) by ring]
      have h1 : ‖(lemma83LocalH2 a b ij.1-(ij.1+1:ℂ))*c^ij.2‖ ≤
          (n+1:ℝ)^2*(‖a-1‖+‖b-1‖) := by
        rw [norm_mul,norm_pow]
        calc
          _ ≤ ((ij.1+1:ℝ)^2*(‖a-1‖+‖b-1‖))*1 := mul_le_mul
            (lemma83_local_h2_perturbation a b ha hb _) (pow_le_one₀ (norm_nonneg _) hc)
            (pow_nonneg (norm_nonneg _) _) (by positivity)
          _ ≤ _ := by rw [mul_one]; gcongr
      have h2 : ‖(ij.1+1:ℂ)*(c^ij.2-1)‖ ≤ (n+1:ℝ)^2*‖c-1‖ := by
        rw [norm_mul,show (ij.1+1:ℂ) = ((ij.1+1:ℕ):ℂ) by push_cast; rfl,
          Complex.norm_natCast]
        calc
          _ ≤ ((ij.1+1:ℕ):ℝ)*((ij.2:ℝ)*‖c-1‖) :=
            mul_le_mul_of_nonneg_left (lemma83_norm_pow_sub_one c hc _) (by positivity)
          _ ≤ (n+1:ℝ)*((n+1:ℝ)*‖c-1‖) := by push_cast; gcongr
          _ = _ := by ring
      exact (norm_add_le _ _).trans (by nlinarith)
    _ = _ := by simp; ring

lemma lemma83_local_kappa_perturbation (a b c : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hc : ‖c‖ ≤ 1) (n : ℕ) :
    ‖lemma83LocalKappa a b c n-(n+1:ℂ)‖ ≤
      2*(n+1:ℝ)^3*(‖a-1‖+‖b-1‖+‖c-1‖) := by
  rw [←lemma83_local_kappa_one]
  cases n with
  | zero => simp; positivity
  | succ n =>
    simp only [lemma83_local_kappa_succ]
    rw [show (lemma83LocalH3 a b c (n+1)-lemma83LocalH3 a b c n)-
      (lemma83LocalH3 1 1 1 (n+1)-lemma83LocalH3 1 1 1 n) =
      (lemma83LocalH3 a b c (n+1)-lemma83LocalH3 1 1 1 (n+1))-
      (lemma83LocalH3 a b c n-lemma83LocalH3 1 1 1 n) by ring]
    have h1 := lemma83_local_h3_perturbation a b c ha hb hc (n+1)
    have h0 := lemma83_local_h3_perturbation a b c ha hb hc n
    have hp : (n+1:ℝ)^3 ≤ (n+1+1:ℝ)^3 := by gcongr; linarith
    have hh := norm_sub_le (lemma83LocalH3 a b c (n+1)-lemma83LocalH3 1 1 1 (n+1))
      (lemma83LocalH3 a b c n-lemma83LocalH3 1 1 1 n)
    push_cast at *
    nlinarith [mul_le_mul_of_nonneg_right hp (by positivity : 0 ≤ ‖a-1‖+‖b-1‖+‖c-1‖)]

lemma lemma83_kappa_prime_power_zero_shift {p : ℕ} (hp : p.Prime) (n : ℕ) :
    lemma83Kappa (fun _ => 0) (p^n) = (n+1:ℂ) := by
  simp [lemma83_kappa_prime_power _ hp]

/-- Quantitative coefficient perturbation with the actual local phase error. -/
theorem lemma83_kappa_prime_power_perturbation (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ‖lemma83Kappa β (p^n)-lemma83Kappa (fun _ => 0) (p^n)‖ ≤
      2*(n+1:ℝ)^3*lemma83PrimeShiftMass β p := by
  rw [lemma83_kappa_prime_power_zero_shift hp,lemma83_kappa_prime_power β hp]
  exact lemma83_local_kappa_perturbation _ _ _
    (lemma83_cpow_shift_norm hp.pos _ (hβ 0)).le
    (lemma83_cpow_shift_norm hp.pos _ (hβ 1)).le
    (lemma83_cpow_shift_norm hp.pos _ (hβ 2)).le n

lemma lemma83_prime_shift_mass_nonneg (β : Fin 3 → ℂ) (p : ℕ) :
    0 ≤ lemma83PrimeShiftMass β p := by unfold lemma83PrimeShiftMass; positivity

lemma lemma83_prime_shift_term_le (β : Fin 3 → ℂ) (p : ℕ) (j : Fin 3) :
    ‖(p:ℂ)^(-β j)-1‖ ≤ lemma83PrimeShiftMass β p := by
  fin_cases j <;> dsimp [lemma83PrimeShiftMass] <;>
    linarith [norm_nonneg ((p:ℂ)^(-β 0)-1),norm_nonneg ((p:ℂ)^(-β 1)-1),
      norm_nonneg ((p:ℂ)^(-β 2)-1)]

lemma lemma83_prime_shift_mass_bound (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) (b : ℝ) (hsmall : ∀ i, ‖β i‖ ≤ b)
    {p : ℕ} (hp : p.Prime) : lemma83PrimeShiftMass β p ≤ 3*b*Real.log p := by
  have hlog : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hh (i : Fin 3) : ‖(p:ℂ)^(-β i)-1‖ ≤ b*Real.log p :=
    (lemma83_cpow_shift_sub_one_bound hp.pos _ (hβ i)).trans
      (mul_le_mul_of_nonneg_right (hsmall i) hlog)
  unfold lemma83PrimeShiftMass
  linarith [hh 0,hh 1,hh 2]

/-- Exact unshifted ramified coefficients. -/
lemma lemma83_xi_prime_power_r_zero_shift (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (e d r : ℕ) (hpr : p ∣ r) :
    lemma83Xi (fun _ => 0) j (p^(e+1)) d r = (e+2:ℂ) := by
  rw [lemma83_xi_prime_power_r _ j hp e d r hpr,lemma83_kappa_prime_power_zero_shift hp]
  push_cast
  ring

/-- Exact unshifted exceptional coefficients; it does not divide by the numerator. -/
lemma lemma83_xi_prime_power_d_zero_shift (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (e d r : ℕ) (hpd : p ∣ d) (hpr : ¬p ∣ r) :
    lemma83Xi (fun _ => 0) j (p^(e+1)) d r = 1-(e+1:ℂ)/(p-1:ℕ) := by
  rw [lemma83_xi_prime_power_d _ j hp e d r hpd hpr,
    lemma83_kappa_prime_power_zero_shift hp,lemma83_kappa_prime_power_zero_shift hp]
  simp only [sub_zero,Complex.cpow_one,Nat.cast_add,Nat.cast_one]
  have hpn : (p:ℂ)-1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hp.ne_one)
  rw [Nat.cast_sub hp.one_le,Nat.cast_one]
  field_simp
  ring

lemma lemma83_xi_prime_power_r_perturbation (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (e d r : ℕ) (hpr : p ∣ r) :
    ‖lemma83Xi β j (p^(e+1)) d r-lemma83Xi (fun _ => 0) j (p^(e+1)) d r‖ ≤
      2*(e+2:ℝ)^3*lemma83PrimeShiftMass β p := by
  rw [lemma83_xi_prime_power_r β j hp e d r hpr,
    lemma83_xi_prime_power_r (fun _ => 0) j hp e d r hpr]
  convert lemma83_kappa_prime_power_perturbation β hβ hp (e+1) using 1 <;> push_cast <;> ring

lemma lemma83_prime_mobius_weight_perturbation (β : ℂ) {p : ℕ} (hp : p.Prime) :
    ‖(p:ℂ)^(1-β)/(p-1:ℕ)-(p:ℂ)/(p-1:ℕ)‖ ≤ 2*‖(p:ℂ)^(-β)-1‖ := by
  rw [lemma83_prime_mobius_weight β hp]
  have hz := lemma83_prime_mobius_weight (0:ℂ) hp
  simp only [sub_zero,Complex.cpow_one,neg_zero,Complex.cpow_zero] at hz
  rw [hz,←sub_div,norm_div]
  have hh := div_le_div₀ (norm_nonneg _) (le_refl ‖(p:ℂ)^(-β)-1‖)
    (by norm_num : (0:ℝ)<1/2)
    (lemma83_one_sub_norm_ge_half (lemma83_prime_reciprocal_norm_le_half hp))
  exact hh.trans_eq (by ring)

/-- All primes dividing d but not r, with uniform additive error even at p=2. -/
theorem lemma83_xi_prime_power_d_perturbation (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (e d r : ℕ) (hpd : p ∣ d) (hpr : ¬p ∣ r) :
    ‖lemma83Xi β j (p^(e+1)) d r-lemma83Xi (fun _ => 0) j (p^(e+1)) d r‖ ≤
      8*(e+2:ℝ)^3*lemma83PrimeShiftMass β p := by
  let K := lemma83PrimeShiftMass β p
  have hK : 0 ≤ K := lemma83_prime_shift_mass_nonneg β p
  have hterm := lemma83_prime_shift_term_le β p j
  have hk1 := lemma83_kappa_prime_power_perturbation β hβ hp (e+1)
  have hk0 := lemma83_kappa_prime_power_perturbation β hβ hp e
  have hw := lemma83_prime_mobius_weight_norm_bound (β j) (hβ j) hp
  have hwd := lemma83_prime_mobius_weight_perturbation (β j) hp
  have hbase : ‖lemma83Kappa (fun _ => 0) (p^e)‖ = (e+1:ℝ) := by
    rw [lemma83_kappa_prime_power_zero_shift hp]
    norm_cast
  let w : ℂ := (p:ℂ)^(1-β j)/(p-1:ℕ)
  let w0 : ℂ := (p:ℂ)/(p-1:ℕ)
  have hc : ‖lemma83Kappa β (p^e)*w-lemma83Kappa (fun _ => 0) (p^e)*w0‖ ≤
      4*(e+1:ℝ)^3*K+2*(e+1:ℝ)*K := by
    rw [show lemma83Kappa β (p^e)*w-lemma83Kappa (fun _ => 0) (p^e)*w0 =
      (lemma83Kappa β (p^e)-lemma83Kappa (fun _ => 0) (p^e))*w+
      lemma83Kappa (fun _ => 0) (p^e)*(w-w0) by ring]
    have h1 := mul_le_mul hk0 hw (norm_nonneg _) (by positivity : 0 ≤ 2*(e+1:ℝ)^3*K)
    have h2 := mul_le_mul_of_nonneg_left (hwd.trans (by gcongr)) (by positivity : 0 ≤ (e+1:ℝ))
    have hh := norm_add_le ((lemma83Kappa β (p^e)-lemma83Kappa (fun _ => 0) (p^e))*w)
      (lemma83Kappa (fun _ => 0) (p^e)*(w-w0))
    rw [norm_mul,norm_mul,hbase] at hh
    dsimp [w,w0,K] at *
    nlinarith
  rw [lemma83_xi_prime_power_d β j hp e d r hpd hpr,
    lemma83_xi_prime_power_d (fun _ => 0) j hp e d r hpd hpr]
  simp only [sub_zero,Complex.cpow_one,mul_div_assoc]
  rw [show (lemma83Kappa β (p^(e+1))-lemma83Kappa β (p^e)*w)-
      (lemma83Kappa (fun _ => 0) (p^(e+1))-lemma83Kappa (fun _ => 0) (p^e)*w0) =
      (lemma83Kappa β (p^(e+1))-lemma83Kappa (fun _ => 0) (p^(e+1)))-
      (lemma83Kappa β (p^e)*w-lemma83Kappa (fun _ => 0) (p^e)*w0) by ring]
  have hh := norm_sub_le (lemma83Kappa β (p^(e+1))-lemma83Kappa (fun _ => 0) (p^(e+1)))
    (lemma83Kappa β (p^e)*w-lemma83Kappa (fun _ => 0) (p^e)*w0)
  have hp1 : (e+1:ℝ)^3 ≤ (e+2:ℝ)^3 := by gcongr; linarith
  have hp2 : (e+1:ℝ) ≤ (e+2:ℝ)^3 := by nlinarith [Nat.cast_nonneg (α := ℝ) e]
  push_cast at hk1
  nlinarith [mul_le_mul_of_nonneg_right hp1 hK,mul_le_mul_of_nonneg_right hp2 hK]

end ZhangLS.Spec
