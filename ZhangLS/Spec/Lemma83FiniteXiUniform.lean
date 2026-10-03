import ZhangLS.Spec.Lemma83FiniteXiRegular

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma83_lambda_prime_phase_perturbation (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re = 0) (j : Fin 3) {p : ℕ} (hp : p.Prime) :
    ‖lemma83LambdaFactor β p (1-β j) - (1-(p:ℂ)⁻¹)^2‖ ≤
      32*lemma83PrimeShiftMass β p/(p:ℝ) := by
  let u : ℂ := (p:ℂ)⁻¹
  let t : ℂ := (p:ℂ)^(-(1-β j))
  let a : Fin 3 → ℂ := fun i => (p:ℂ)^(-β i)
  let E : ℝ := lemma83PrimeShiftMass β p/(p:ℝ)
  have hK := lemma83_prime_shift_mass_nonneg β p
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hphase (i : Fin 3) : ‖a i-1‖ ≤ lemma83PrimeShiftMass β p :=
    lemma83_prime_shift_term_le β p i
  have ht : ‖t‖ = (p:ℝ)⁻¹ := lemma83_cpow_tail_norm hp.pos _ (hβ j)
  have hu : ‖u‖ ≤ 1/2 := lemma83_prime_reciprocal_norm_le_half hp
  have ht2 : ‖t‖ ≤ 1/2 := lemma83_tail_parameter_norm_le_half _ (hβ j) hp
  have hat : a j*t=u := lemma83_prime_reciprocal_relation _ hp.pos
  have htu : ‖t-u‖ ≤ E := by
    rw [← hat,show t-a j*t = (1-a j)*t by ring,norm_mul,norm_sub_rev,ht]
    simpa [E,div_eq_mul_inv] using
      mul_le_mul_of_nonneg_right (hphase j) (by positivity : 0 ≤ (p:ℝ)⁻¹)
  have hau (i : Fin 3) : ‖a i*t-u‖ ≤ 2*E := by
    rw [show a i*t-u = (a i-1)*t+(t-u) by ring]
    have hh : ‖(a i-1)*t‖ ≤ E := by
      rw [norm_mul,ht]
      simpa [E,div_eq_mul_inv] using
        mul_le_mul_of_nonneg_right (hphase i) (by positivity : 0 ≤ (p:ℝ)⁻¹)
    exact (norm_add_le _ _).trans (by linarith)
  have hav (i : Fin 3) : ‖(1-a i*t)-(1-u)‖ ≤ 2*E := by
    simpa only [sub_sub_sub_cancel_left,norm_sub_rev] using hau i
  have hnorm (i : Fin 3) : ‖1-a i*t‖ ≤ 3/2 := by
    have hh := norm_sub_le (1:ℂ) (a i*t)
    rw [norm_one,norm_mul,lemma83_cpow_shift_norm hp.pos _ (hβ i),one_mul] at hh
    linarith
  have hv : ‖1-u‖ ≤ 1 := by
    have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
    have huR : (p:ℝ)⁻¹ ≤ 1 := (inv_le_one₀ (Nat.cast_pos.mpr hp.pos)).mpr hpR
    have he : (1:ℂ)-u = ((1-(p:ℝ)⁻¹:ℝ):ℂ) := by simp [u]
    rw [he,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by linarith)]
    linarith [inv_nonneg.mpr (Nat.cast_nonneg (α := ℝ) p)]
  have htv : ‖(1-t)-(1-u)‖ ≤ 2*E := by
    simpa only [sub_sub_sub_cancel_left,norm_sub_rev] using htu.trans (by linarith : E ≤ 2*E)
  have hh := lemma83_triple_quotient_perturbation (1-a 0*t) (1-a 1*t)
    (1-a 2*t) (1-u) (1-t) (2*E) (by positivity) (hnorm 0) (hnorm 1) hv
    (hav 0) (hav 1) (hav 2) htv (lemma83_one_sub_norm_ge_half ht2)
  rw [lemma83_lambda_factor_inverse β hp.pos]
  convert hh using 1
  · simp [lemma83ActualKappaRational,lemma83KappaRational,inv_div,a,t,u]
  · dsimp [E]; ring

lemma lemma83_product_sub_product_norm (a b c d : ℂ) :
    ‖a*b-c*d‖ ≤ ‖a‖*‖b-d‖+‖a-c‖*‖d‖ := by
  rw [show a*b-c*d = a*(b-d)+(a-c)*d by ring]
  simpa only [norm_mul] using norm_add_le (a*(b-d)) ((a-c)*d)

lemma lemma83_zero_shift_kappa_tail_norm {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ‖∑' k : ℕ, lemma83Kappa (fun _ => 0) (p^(n+k))*((p:ℂ)⁻¹)^k‖ ≤ 4*(n+1:ℝ) := by
  rw [lemma83_zero_shift_kappa_tail hp]
  have hu := lemma83_prime_reciprocal_norm_le_half hp
  have hv := lemma83_one_sub_norm_ge_half hu
  have h1 : ‖(n+1:ℂ)/(1-(p:ℂ)⁻¹)‖ ≤ 2*(n+1:ℝ) := by
    rw [norm_div,show (n+1:ℂ) = ((n+1:ℕ):ℂ) by push_cast; rfl,Complex.norm_natCast]
    have hh := div_le_div₀ (by positivity) (le_refl ((n+1:ℕ):ℝ)) (by norm_num : (0:ℝ)<1/2) hv
    push_cast at hh ⊢
    nlinarith only [hh]
  have h2 : ‖(p:ℂ)⁻¹/(1-(p:ℂ)⁻¹)^2‖ ≤ 2 := by
    rw [norm_div,norm_pow]
    have hv2 : (1/2:ℝ)^2 ≤ ‖1-(p:ℂ)⁻¹‖^2 := by gcongr
    have hh := div_le_div₀ (by norm_num : (0:ℝ)≤1/2) hu
      (by norm_num : (0:ℝ)<(1/2)^2) hv2
    norm_num at hh
    simpa only [norm_inv,Complex.norm_natCast] using hh
  exact (norm_add_le _ _).trans (by linarith [Nat.cast_nonneg (α := ℝ) n])

lemma lemma83_kappa_mobius_correction_perturbation (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) {p : ℕ} (hp : p.Prime) (n : ℕ) :
    ‖lemma83Kappa β (p^n)*((p:ℂ)^(1-β j)/(p-1:ℕ))-
      lemma83Kappa (fun _ => 0) (p^n)*((p:ℂ)/(p-1:ℕ))‖ ≤
      6*(n+1:ℝ)^3*lemma83PrimeShiftMass β p := by
  let K := lemma83PrimeShiftMass β p
  have hK : 0 ≤ K := lemma83_prime_shift_mass_nonneg β p
  have hk := lemma83_kappa_prime_power_perturbation β hβ hp n
  have hw := lemma83_prime_mobius_weight_norm_bound (β j) (hβ j) hp
  have hwd : ‖(p:ℂ)^(1-β j)/(p-1:ℕ)-(p:ℂ)/(p-1:ℕ)‖ ≤ 2*K :=
    (lemma83_prime_mobius_weight_perturbation (β j) hp).trans
      (mul_le_mul_of_nonneg_left (lemma83_prime_shift_term_le β p j) (by norm_num))
  have hbase : ‖lemma83Kappa (fun _ => 0) (p^n)‖ = (n+1:ℝ) := by
    rw [lemma83_kappa_prime_power_zero_shift hp]
    norm_cast
  have hh : ‖lemma83Kappa β (p^n)*((p:ℂ)^(1-β j)/(p-1:ℕ))-
      lemma83Kappa (fun _ => 0) (p^n)*((p:ℂ)/(p-1:ℕ))‖ ≤
      ‖(p:ℂ)^(1-β j)/(p-1:ℕ)‖*‖lemma83Kappa β (p^n)-lemma83Kappa (fun _ => 0) (p^n)‖+
      ‖(p:ℂ)^(1-β j)/(p-1:ℕ)-(p:ℂ)/(p-1:ℕ)‖*(n+1:ℝ) := by
    simpa only [hbase,mul_comm] using lemma83_product_sub_product_norm ((p:ℂ)^(1-β j)/(p-1:ℕ))
      (lemma83Kappa β (p^n)) ((p:ℂ)/(p-1:ℕ)) (lemma83Kappa (fun _ => 0) (p^n))
  have h1 := mul_le_mul hw hk (norm_nonneg _) (by norm_num : (0:ℝ)≤2)
  have h2 := mul_le_mul_of_nonneg_right hwd (by positivity : 0 ≤ (n+1:ℝ))
  have hn : (n+1:ℝ) ≤ (n+1:ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) n] : 1≤(n+1:ℝ)) (by norm_num : (1:ℕ)≤3)
  nlinarith [mul_le_mul_of_nonneg_right hn hK]

/-- Actual regular-prime ξ coefficients are additively close to their exact center. -/
theorem lemma83_xi_prime_power_regular_perturbation (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (e d r : ℕ) (hpd : ¬p ∣ d*r) :
    ‖lemma83Xi β j (p^(e+1)) d r-lemma83Xi (fun _ => 0) j (p^(e+1)) d r‖ ≤
      6500*(e+2:ℝ)^3*lemma83PrimeShiftMass β p := by
  let K := lemma83PrimeShiftMass β p
  let T : ℂ := ∑' k : ℕ, lemma83Kappa β (p^(e+1+k))*((p:ℂ)^(-(1-β j)))^k
  let T0 : ℂ := ∑' k : ℕ, lemma83Kappa (fun _ => 0) (p^(e+1+k))*((p:ℂ)⁻¹)^k
  let Q : ℂ := lemma83Kappa β (p^e)*((p:ℂ)^(1-β j)/(p-1:ℕ))
  let Q0 : ℂ := lemma83Kappa (fun _ => 0) (p^e)*((p:ℂ)/(p-1:ℕ))
  let L := lemma83LambdaFactor β p (1-β j)
  let L0 := lemma83LambdaFactor (fun _ => 0) p 1
  have hK : 0 ≤ K := lemma83_prime_shift_mass_nonneg β p
  have hT : ‖T-T0‖ ≤ 900*(e+2:ℝ)^3*K := by
    convert lemma83_kappa_tail_perturbation β hβ j hp (e+1) using 1 <;> push_cast <;> ring
  have hQ : ‖Q-Q0‖ ≤ 6*(e+2:ℝ)^3*K :=
    (lemma83_kappa_mobius_correction_perturbation β hβ j hp e).trans (by gcongr; linarith)
  have hB : ‖(T-Q)-(T0-Q0)‖ ≤ 906*(e+2:ℝ)^3*K := by
    rw [show (T-Q)-(T0-Q0) = (T-T0)-(Q-Q0) by ring]
    exact (norm_sub_le _ _).trans (by linarith)
  have hT0 : ‖T0‖ ≤ 4*(e+2:ℝ) := by
    convert lemma83_zero_shift_kappa_tail_norm hp (e+1) using 1 <;> push_cast <;> ring
  have hQ0 : ‖Q0‖ ≤ 2*(e+1:ℝ) := by
    dsimp [Q0]
    rw [norm_mul,lemma83_kappa_prime_power_zero_shift hp,
      show (e+1:ℂ) = ((e+1:ℕ):ℂ) by push_cast; rfl,Complex.norm_natCast]
    have hh := lemma83_prime_mobius_weight_norm_bound (0:ℂ) (by simp) hp
    simp only [sub_zero,Complex.cpow_one] at hh
    have hh' := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ ((e+1:ℕ):ℝ))
    push_cast at hh' ⊢
    nlinarith only [hh']
  have hB0 : ‖T0-Q0‖ ≤ 6*(e+2:ℝ) := (norm_sub_le _ _).trans (by linarith)
  have hL : ‖L‖ ≤ 7 := lemma83_lambda_prime_norm_bound β hβ j hp
  have hLd : ‖L-L0‖ ≤ 16*K := by
    dsimp [L,L0]
    rw [lemma83_lambda_prime_zero_shift hp]
    apply (lemma83_lambda_prime_phase_perturbation β hβ j hp).trans
    rw [div_le_iff₀ (Nat.cast_pos.mpr hp.pos)]
    nlinarith [mul_le_mul_of_nonneg_left (show (2:ℝ)≤p by exact_mod_cast hp.two_le) hK]
  rw [lemma83_xi_prime_power_regular β j hp e d r hpd,
    lemma83_xi_prime_power_regular (fun _ => 0) j hp e d r hpd]
  simp only [sub_zero,Complex.cpow_neg_one,Complex.cpow_one,mul_div_assoc]
  change ‖L*(T-Q)-L0*(T0-Q0)‖ ≤ _
  have hh := lemma83_product_sub_product_norm L (T-Q) L0 (T0-Q0)
  have h1 := mul_le_mul hL hB (norm_nonneg _) (by norm_num : (0:ℝ)≤7)
  have h2 := mul_le_mul hLd hB0 (norm_nonneg _) (by positivity : 0 ≤ 16*K)
  have hn : (e+2:ℝ) ≤ (e+2:ℝ)^3 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by linarith [Nat.cast_nonneg (α := ℝ) e] : 1≤(e+2:ℝ)) (by norm_num : (1:ℕ)≤3)
  nlinarith [mul_le_mul_of_nonneg_right hn hK]

/-- Uniform local perturbation for every prime-power and every d,r. -/
theorem lemma83_xi_prime_power_perturbation (β : Fin 3 → ℂ)
    (hβ : ∀ i, (β i).re=0) (j : Fin 3) {p : ℕ} (hp : p.Prime)
    (n d r : ℕ) :
    ‖lemma83Xi β j (p^n) d r-lemma83Xi (fun _ => 0) j (p^n) d r‖ ≤
      6500*(n+1:ℝ)^3*lemma83PrimeShiftMass β p := by
  have hK := lemma83_prime_shift_mass_nonneg β p
  cases n with
  | zero => simp; positivity
  | succ e =>
    have he : (↑(e+1)+1:ℝ) = e+2 := by push_cast; ring
    rw [he]
    by_cases hpr : p ∣ r
    · exact (lemma83_xi_prime_power_r_perturbation β hβ j hp e d r hpr).trans (by nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ)≤e+2) 3) hK])
    by_cases hpd : p ∣ d
    · exact (lemma83_xi_prime_power_d_perturbation β hβ j hp e d r hpd hpr).trans (by nlinarith [mul_nonneg (pow_nonneg (by positivity : (0:ℝ)≤e+2) 3) hK])
    · exact lemma83_xi_prime_power_regular_perturbation β hβ j hp e d r
        (fun h => (hp.dvd_mul.mp h).elim hpd hpr)

end ZhangLS.Spec
