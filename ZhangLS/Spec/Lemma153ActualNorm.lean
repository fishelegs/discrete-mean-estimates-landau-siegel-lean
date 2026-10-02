import ZhangLS.Spec.Lemma153ActualLocal
import ZhangLS.Spec.Lemma153EulerBounds
import ZhangLS.Spec.Lemma153VarpiMultiplicative
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2500000

lemma lemma153_actual_local_ratio_bounds {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) (q : Nat.Primes) :
    let B := lemma153Baseline χ β γ q
    let lam := lemma152LambdaFactor χ β q.val 1
    let A := χ.evalNat q.val/(1-(q.val:ℂ)⁻¹)
    let y := lemma32PrimeMonomial q.val (1-γ)
    let K := lemma152KappaRational ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1)) y
    B ≠ 0 ∧ ‖(B+lam*A*y*K)/B-1‖ ≤ 10000*‖(q.val:ℂ)⁻¹‖ ∧
      ‖lam*((1-A*y)*K)/B-1‖ ≤ 10000*‖(q.val:ℂ)⁻¹‖ ∧ ‖lam*K/B‖ ≤ 10000 := by
  let a := (q.val:ℂ)^(-β 0)
  let b := (q.val:ℂ)^(-β 1)
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let y := lemma32PrimeMonomial q.val (1-γ)
  let B := lemma153Baseline χ β γ q
  let lam := lemma152LambdaFactor χ β q.val 1
  let A := v/(1-u)
  let K := lemma152KappaRational a b y
  let t := v*(q.val:ℂ)^γ
  have ha : ‖a‖ ≤ 1 := (lemma83_cpow_shift_norm q.property.pos (β 0) (hpar.beta_re 0)).le
  have hb : ‖b‖ ≤ 1 := (lemma83_cpow_shift_norm q.property.pos (β 1) (hpar.beta_re 1)).le
  have hu : ‖u‖ ≤ 1/2 := by
    dsimp [u]
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ q.val by exact_mod_cast q.property.two_le)
  have hv : ‖v‖ ≤ 1 := χ.evalNat_norm_le_one _
  have hy : ‖y‖ = ‖u‖ := by
    dsimp [y,u]
    rw [lemma83_prime_monomial_norm_rpow q.property.pos]
    simp [hpar.gamma_re,Real.rpow_neg_one]
  have hyl : ‖y‖ ≤ 1/2 := hy.trans_le hu
  have hBl : 1/18 ≤ ‖B‖ := lemma153_base_norm_lower χ β hpar.beta_re hpar.beta_small γ
    hpar.gamma_re hpar.gamma_small hpar.small_error q
  have hBn : B ≠ 0 := by intro hz; rw [hz,norm_zero] at hBl; norm_num at hBl
  have hBi : ‖B⁻¹‖ ≤ 18 := by
    rw [norm_inv]
    have hh := one_div_le_one_div_of_le (by norm_num : (0:ℝ)<1/18) hBl
    simpa using hh
  have hB1 : ‖B-1‖ ≤ 384*‖u‖ := by
    simpa only [B,lemma153Baseline,← hy] using lemma153_base_norm_difference χ β hpar.beta_re q.property y hyl
  have hlam : ‖lam‖ ≤ 5 := lemma152_lambda_norm_le χ β hpar.beta_re q.property
  have hlam1 : ‖lam-1‖ ≤ 7*‖u‖ := by
    rw [show lam = lemma153LocalLambda a b u v by
      exact lemma152_lambda_factor_rational χ β q.property.pos]
    exact lemma153_lambda_rational_difference a b u v ha hb hu hv
  have hK := lemma153_kappa_rational_bounds a b y ha hb hyl
  have hA : ‖A‖ ≤ 2 := by
    have hd : 1/2 ≤ ‖1-u‖ := by have := norm_sub_norm_le (1:ℂ) u; rw [norm_one] at this; linarith
    dsimp [A]
    rw [norm_div]
    exact (div_le_div₀ (by positivity) hv (by norm_num : (0:ℝ)<1/2) hd).trans (by norm_num)
  have hrat := lemma153_normalized_ratio_bounds B lam K A y ‖u‖ (norm_nonneg _) hu hy
    hBn hBi hB1 hlam hlam1 hK.1 (by simpa only [hy] using hK.2) hA
  exact ⟨hBn,hrat⟩

lemma lemma153_local_chi_varpi_norm (B C E F lam t : ℂ)
    (hB : B ≠ 0) (hcompat : B = C+lam*E-lam*F) (ht : ‖t‖ ≤ 1)
    (u : ℝ) (hu : u ≤ 1/2) (hg : ‖C/B-1‖ ≤ 10000*u)
    (he : ‖lam*E/B-1‖ ≤ 10000*u) (hf : ‖lam*F/B‖ ≤ 10000) (n : ℕ) :
    ‖lemma153LocalChiVarpi B C E F lam t n‖ ≤ 50000*((n:ℝ)+1) := by
  have hg0 : ‖C/B‖ ≤ 5001 := by
    have hh := norm_le_norm_sub_add (C/B) (1:ℂ)
    rw [norm_one] at hh
    linarith
  have he0 : ‖lam*E/B‖ ≤ 5001 := by
    have hh := norm_le_norm_sub_add (lam*E/B) (1:ℂ)
    rw [norm_one] at hh
    linarith
  have hg1 : ‖(C-lam*F)/B‖ ≤ 15001 := by
    rw [sub_div]
    exact (norm_sub_le _ _).trans (by linarith)
  have he1 : ‖(lam*E-lam*F)/B‖ ≤ 15001 := by
    rw [sub_div]
    exact (norm_sub_le _ _).trans (by linarith)
  have htN : ‖t^n‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) ht
  have hH : ‖lemma83LocalH2 1 t n‖ ≤ (n:ℝ)+1 := lemma152_h2_norm_le 1 t (by simp) ht n
  rw [lemma153_local_chi_varpi_eq B C E F lam t hB hcompat]
  apply (norm_add_le _ _).trans
  apply (add_le_add (norm_add_le _ _) le_rfl).trans
  rw [norm_mul,norm_mul]
  have h1 := mul_le_mul he1 htN (norm_nonneg _) (by norm_num : (0:ℝ)≤15001)
  have h2 := mul_le_mul hf hH (norm_nonneg _) (by norm_num : (0:ℝ)≤10000)
  nlinarith only [hg1,h1,h2,Nat.cast_nonneg (α := ℝ) n]

lemma lemma153_actual_prime_power_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) (q : Nat.Primes) (n : ℕ) :
    ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^(n+1))‖ ≤
      50000*((n:ℝ)+2)^2 := by
  by_cases hqd : q.val ∣ D
  · rw [lemma153_coefficient_ramified_prime_power χ β γ (lemma153GeneralMEulerProduct χ β) q.property hqd n,norm_zero]
    positivity
  let B := lemma153Baseline χ β γ q
  let lam := lemma152LambdaFactor χ β q.val 1
  let A := χ.evalNat q.val/(1-(q.val:ℂ)⁻¹)
  let y := lemma32PrimeMonomial q.val (1-γ)
  let K := lemma152KappaRational ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1)) y
  have hr := lemma153_actual_local_ratio_bounds χ β γ hpar q
  have hu : ‖(q.val:ℂ)⁻¹‖ ≤ 1/2 := by
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ q.val by exact_mod_cast q.property.two_le)
  have ht : ‖χ.evalNat q.val*(q.val:ℂ)^γ‖ ≤ 1 := by
    have hw : ‖(q.val:ℂ)^γ‖ = 1 := by
      simpa using lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hpar.gamma_re])
    simpa only [norm_mul,hw,mul_one] using χ.evalNat_norm_le_one q.val
  have hn := lemma153_local_chi_varpi_norm B (B+lam*A*y*K) ((1-A*y)*K) K lam
    (χ.evalNat q.val*(q.val:ℂ)^γ) hr.1 (by ring) ht ‖(q.val:ℂ)⁻¹‖ hu hr.2.1 hr.2.2.1 hr.2.2.2 (n+1)
  have he := lemma153_actual_unramified_chi_varpi χ β hpar.beta_re γ hpar.gamma_re q hqd hM (n+1)
  unfold lemma153Coefficient
  rw [lemma153_tau_two_prime_power q.property]
  rw [show χ.evalNat (q.val^(n+1))*((n+1+1:ℕ):ℂ)*
      lemma153Varpi χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^(n+1)) =
        ((n+1+1:ℕ):ℂ)*(χ.evalNat (q.val^(n+1))*
          lemma153Varpi χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^(n+1))) by ring,he,norm_mul]
  rw [Complex.norm_natCast]
  push_cast at hn ⊢
  have hh := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ (n:ℝ)+1+1)
  nlinarith only [hh]

lemma lemma153_local_norm_majorant_summable :
    Summable (fun n : ℕ => (50000:ℝ)*((n:ℝ)+2)^2*(1/2:ℝ)^n) := by
  have hg := summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have h1 := summable_pow_mul_geometric_of_norm_lt_one 1 (by norm_num : ‖(1/2:ℝ)‖ < 1)
  have h2 := summable_pow_mul_geometric_of_norm_lt_one 2 (by norm_num : ‖(1/2:ℝ)‖ < 1)
  convert (h2.mul_left 50000).add ((h1.mul_left 200000).add (hg.mul_left 200000)) using 1
  funext n
  ring

noncomputable def lemma153LocalNormConstant : ℝ :=
  ∑' n : ℕ, (50000:ℝ)*((n:ℝ)+2)^2*(1/2:ℝ)^n

lemma lemma153_local_norm_constant_nonneg : 0 ≤ lemma153LocalNormConstant :=
  tsum_nonneg (fun _ => by positivity)

lemma lemma153_actual_local_norm_series {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (hM : lemma152EulerProduct χ β (1-γ) ≠ 0) (q : Nat.Primes)
    (z : ℂ) (hz : ‖z‖ ≤ 1/2) :
    Summable (fun n : ℕ => ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n)*z^n‖) ∧
      (∑' n : ℕ, ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n)*z^n‖) ≤
        1+lemma153LocalNormConstant*‖z‖ := by
  have hm := lemma153_local_norm_majorant_summable.mul_left ‖z‖
  have hbound (n : ℕ) : ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^(n+1))*z^(n+1)‖ ≤
      ‖z‖*((50000:ℝ)*((n:ℝ)+2)^2*(1/2:ℝ)^n) := by
    rw [norm_mul,norm_pow,pow_succ ‖z‖]
    have hn := lemma153_actual_prime_power_norm χ β γ hpar hM q n
    have hp := pow_le_pow_left₀ (norm_nonneg _) hz n
    calc
      _ ≤ (50000*((n:ℝ)+2)^2)*((1/2:ℝ)^n*‖z‖) := by gcongr
      _ = _ := by ring
  have ht : Summable (fun n : ℕ => ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^(n+1))*z^(n+1)‖) :=
    hm.of_nonneg_of_le (fun _ => norm_nonneg _) hbound
  have hfull : Summable (fun n : ℕ => ‖lemma153Coefficient χ β γ (lemma153GeneralMEulerProduct χ β) (q.val^n)*z^n‖) :=
    (summable_nat_add_iff 1).mp ht
  refine ⟨hfull,?_⟩
  have hsum := ht.tsum_le_tsum hbound hm
  rw [tsum_mul_left] at hsum
  rw [hfull.tsum_eq_zero_add]
  simp only [pow_zero,lemma153_coefficient_one χ β γ (lemma153GeneralMEulerProduct χ β) (by simpa using hM),
    mul_one,norm_one]
  dsimp [lemma153LocalNormConstant] at *
  nlinarith only [hsum]

end ZhangLS.Spec
