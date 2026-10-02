import ZhangLS.Spec.Lemma153EulerDefinitions
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical
set_option maxHeartbeats 2500000

lemma lemma153_unramified_factor_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ)
    (q : Nat.Primes) (s : ℂ) (hs : 3/4 ≤ s.re) :
    ‖lemma153UnramifiedPrimeFactor χ β γ q s-1‖ ≤
      100000*(q.val:ℝ)^(-(3/2:ℝ)) := by
  let a := (q.val:ℂ)^(-β 0)
  let b := (q.val:ℂ)^(-β 1)
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let y := lemma32PrimeMonomial q.val (1-γ)
  let z := lemma32PrimeMonomial q.val s
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
  have ht : ‖t‖ ≤ 1 := by
    have hw : ‖(q.val:ℂ)^γ‖ = 1 := by
      simpa using lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hpar.gamma_re])
    dsimp [t]
    simpa only [norm_mul,hw,mul_one] using hv
  have hbound := lemma153_shifted_correction_error_bound B (B+lam*A*y*K) ((1-A*y)*K) K lam t z
    hBn (by ring) ht ‖u‖ 10000 (norm_nonneg _) hu (by norm_num) hrat.1 hrat.2.1 hrat.2.2
  change ‖lemma153ShiftedLocalCorrection B (B+lam*A*y*K) ((1-A*y)*K) K lam t z-1‖ ≤ _
  apply hbound.trans
  have hzn : ‖z‖ ≤ (q.val:ℝ)^(-(3/4:ℝ)) := by
    dsimp [z]
    rw [lemma83_prime_monomial_norm_rpow q.property.pos]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast q.property.one_lt.le) (by linarith)
  have hp0 : 0 < (q.val:ℝ) := Nat.cast_pos.mpr q.property.pos
  have hp1 : 1 ≤ (q.val:ℝ) := by exact_mod_cast q.property.one_lt.le
  have hz2 : ‖z‖^2 ≤ (q.val:ℝ)^(-(3/2:ℝ)) := by
    calc
      _ ≤ ((q.val:ℝ)^(-(3/4:ℝ)))^2 := pow_le_pow_left₀ (norm_nonneg _) hzn 2
      _ = _ := by rw [← Real.rpow_natCast,← Real.rpow_mul (le_of_lt hp0)]; norm_num
  have huz : ‖u‖*‖z‖ ≤ (q.val:ℝ)^(-(3/2:ℝ)) := by
    calc
      _ ≤ (q.val:ℝ)⁻¹*(q.val:ℝ)^(-(3/4:ℝ)) := by
        dsimp [u]
        rw [norm_inv,Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_left hzn (by positivity)
      _ = (q.val:ℝ)^(-(7/4:ℝ)) := by
        rw [← Real.rpow_neg_one,← Real.rpow_add hp0]
        norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  nlinarith

lemma lemma153_ramified_factor_error (z : ℂ) (hz : ‖z‖ ≤ 1) :
    ‖(1-z)^2-1‖ ≤ 3*‖z‖ := by
  rw [show (1-z)^2-1 = z^2-2*z by ring]
  apply (norm_sub_le _ _).trans
  rw [norm_pow,norm_mul]
  norm_num only [norm_ofNat]
  nlinarith [norm_nonneg z]

end ZhangLS.Spec
