import ZhangLS.Spec.Lemma153CenterReduction
import ZhangLS.Spec.Lemma153ActualNorm
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped Classical
set_option maxHeartbeats 3000000

lemma lemma153_quotient_difference_bound (a a₀ d d₀ : ℂ)
    (ha₀ : ‖a₀‖ ≤ 5) (hd : 1/4 ≤ ‖d‖) (hd₀ : 1/2 ≤ ‖d₀‖) :
    ‖a/d-a₀/d₀‖ ≤ 4*‖a-a₀‖+40*‖d-d₀‖ := by
  have hdn : d ≠ 0 := by intro h; rw [h,norm_zero] at hd; norm_num at hd
  have hd₀n : d₀ ≠ 0 := by intro h; rw [h,norm_zero] at hd₀; norm_num at hd₀
  have he : a/d-a₀/d₀ = (a-a₀)/d + a₀*(d₀-d)/(d*d₀) := by field_simp; ring
  rw [he]
  apply (norm_add_le _ _).trans
  have h1 : ‖(a-a₀)/d‖ ≤ 4*‖a-a₀‖ := by
    rw [norm_div]
    apply (div_le_div_of_nonneg_left (norm_nonneg _) (by norm_num : (0:ℝ)<1/4) hd).trans
    ring_nf
    exact le_rfl
  have hdd : 1/8 ≤ ‖d*d₀‖ := by rw [norm_mul]; nlinarith [norm_nonneg d,norm_nonneg d₀]
  have h2 : ‖a₀*(d₀-d)/(d*d₀)‖ ≤ 40*‖d-d₀‖ := by
    rw [norm_div,norm_mul,norm_sub_rev d₀ d]
    have hnum := mul_le_mul_of_nonneg_right ha₀ (norm_nonneg (d-d₀))
    apply (div_le_div₀ (by positivity) hnum (by norm_num : (0:ℝ)<1/8) hdd).trans
    ring_nf
    exact le_rfl
  linarith

lemma lemma153_lambda_shift_variation (a b u v : ℂ)
    (ha : ‖a‖ ≤ 1) (hb : ‖b‖ ≤ 1) (hu : ‖u‖ ≤ 1/2) (hv : ‖v‖ ≤ 1) :
    ‖lemma153LocalLambda a b u v-lemma153LocalLambda 1 1 u v‖ ≤
      3*‖u‖*(‖a-1‖+‖b-1‖) := by
  have hvu : ‖v*u‖ ≤ 1/2 := by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hu
  have hvun := lemma83_one_sub_ne_zero (hvu.trans_lt (by norm_num))
  have hd : 1/2 ≤ ‖1-v*u‖ := by have hh := lemma152_one_sub_norm_lower hvu; linarith
  have hab : ‖a*b-1‖ ≤ ‖a-1‖+‖b-1‖ := by
    rw [show a*b-1 = a*(b-1)+(a-1) by ring]
    apply (norm_add_le _ _).trans
    rw [norm_mul]
    have hh := mul_le_of_le_one_left (norm_nonneg (b-1)) ha
    linarith
  have he : lemma153LocalLambda a b u v-lemma153LocalLambda 1 1 u v =
      (-(v*u)*((a-1)+(b-1))+v^2*u^2*(a*b-1))/(1-v*u) := by
    unfold lemma153LocalLambda
    field_simp [hvun]
    ring
  have hn : ‖-(v*u)*((a-1)+(b-1))+v^2*u^2*(a*b-1)‖ ≤
      (3/2)*‖u‖*(‖a-1‖+‖b-1‖) := by
    apply (norm_add_le _ _).trans
    simp only [norm_mul,norm_neg,norm_pow]
    have h1 : ‖v‖*‖u‖*‖(a-1)+(b-1)‖ ≤ ‖u‖*(‖a-1‖+‖b-1‖) := by
      have hsum := norm_add_le (a-1) (b-1)
      calc
        _ ≤ 1*‖u‖*(‖a-1‖+‖b-1‖) := by gcongr
        _ = _ := by ring
    have hv2 : ‖v‖^2 ≤ 1 := by nlinarith [norm_nonneg v]
    have h2 : ‖v‖^2*‖u‖^2*‖a*b-1‖ ≤ ‖u‖^2*(‖a-1‖+‖b-1‖) := by
      calc
        _ ≤ 1*‖u‖^2*(‖a-1‖+‖b-1‖) := by gcongr
        _ = _ := by ring
    have h3 := mul_le_mul_of_nonneg_right hu
      (mul_nonneg (norm_nonneg u) (add_nonneg (norm_nonneg (a-1)) (norm_nonneg (b-1))))
    nlinarith only [h1,h2,h3]
  rw [he,norm_div]
  apply (div_le_div₀ (by positivity) hn (by norm_num : (0:ℝ)<1/2) hd).trans
  ring_nf
  exact le_rfl

lemma lemma153_prime_normalizer_lower {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) (q : Nat.Primes) :
    1/2 ≤ ‖lemma152PrimeFactor χ β q (1-γ)‖ := by
  have hs : (1-γ).re = 1 := by simp [hpar.gamma_re]
  have hd : ‖(1-γ)-1‖ = ‖γ‖ := by simp
  have hc := lemma152_prime_comparison χ β hpar.beta_re hpar.beta_small q (1-γ)
    (by rw [hs]; norm_num) (by simpa only [hd] using hpar.gamma_small)
  rw [hd] at hc
  have hpw : (q.val:ℝ)^(-(17/10:ℝ)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast q.property.one_lt.le) (by norm_num)
  have hp0 : 0 ≤ 10*lemma152CorrectionConstant*(‖β 0‖+‖β 1‖+‖γ‖) := by
    have := lemma152_correction_constant_pos
    positivity
  have he := hc.trans ((mul_le_of_le_one_right hp0 hpw).trans hpar.small_error)
  have hz : 1 ≤ ‖lemma152PrimeFactor χ (fun _ => 0) q 1‖ :=
    (lemma153_zero_center_factor_real χ q).2.trans (Complex.re_le_norm _)
  have hh := norm_sub_norm_le (lemma152PrimeFactor χ (fun _ => 0) q 1)
    (lemma152PrimeFactor χ β q (1-γ))
  rw [norm_sub_rev] at hh
  linarith

noncomputable def lemma153MixedRatio {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (q : Nat.Primes) : ℂ :=
  lemma152LambdaFactor χ β q.val 1 *
    lemma152KappaRational ((q.val:ℂ)^(-β 0)) ((q.val:ℂ)^(-β 1))
      (lemma32PrimeMonomial q.val (1-γ)) / lemma153Baseline χ β γ q

lemma lemma153_actual_mixed_ratio_reduction {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) (q : Nat.Primes) :
    lemma153MixedRatio χ β γ q = lemma152LambdaFactor χ β q.val 1 /
      ((1-χ.evalNat q.val*lemma32PrimeMonomial q.val (1-γ))*lemma152PrimeFactor χ β q (1-γ)) := by
  let a := (q.val:ℂ)^(-β 0)
  let b := (q.val:ℂ)^(-β 1)
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let y := lemma32PrimeMonomial q.val (1-γ)
  have hu : ‖u‖ < 1 := by
    dsimp [u]
    rw [norm_inv,Complex.norm_natCast]
    exact (inv_lt_one₀ (Nat.cast_pos.mpr q.property.pos)).mpr (by exact_mod_cast q.property.one_lt)
  have hy : ‖y‖ = ‖u‖ := by
    dsimp [y,u]
    rw [lemma83_prime_monomial_norm_rpow q.property.pos]
    simp [hpar.gamma_re,Real.rpow_neg_one]
  have hvu : ‖v*u‖ < 1 := lt_of_le_of_lt
    (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) hu
  have hvy : ‖v*y‖ < 1 := lt_of_le_of_lt
    (by rw [norm_mul]; exact mul_le_of_le_one_left (norm_nonneg _) (χ.evalNat_norm_le_one _)) (hy.trans_lt hu)
  have hn (i : Fin 2) := lemma83_cpow_shift_norm q.property.pos (β i) (hpar.beta_re i)
  have hnY (i : Fin 2) : ‖(q.val:ℂ)^(-β i)*y‖ < 1 := by simpa [norm_mul,hn i] using hy.trans_lt hu
  have hnU (i : Fin 2) : ‖(q.val:ℂ)^(-β i)*(v*u)‖ < 1 := by simpa [norm_mul,hn i] using hvu
  have hB := (lemma153_actual_local_ratio_bounds χ β γ hpar q).1
  have he := lemma153_mixed_ratio_reduction a b u v y (lemma152LambdaFactor χ β q.val 1) hB
    (MulChar.isQuadratic_iff_sq_eq_one.mpr χ.quadratic (q.val:ZMod D))
    (lemma83_one_sub_ne_zero hu) (lemma83_one_sub_ne_zero (hy.trans_lt hu))
    (lemma83_one_sub_ne_zero hvu) (lemma83_one_sub_ne_zero hvy)
    (lemma83_one_sub_ne_zero (hnY 0)) (lemma83_one_sub_ne_zero (hnY 1))
    (lemma83_one_sub_ne_zero (hnU 0)) (lemma83_one_sub_ne_zero (hnU 1))
  unfold lemma153MixedRatio lemma153Baseline
  rw [he]
  congr 2
  unfold lemma152PrimeFactor
  rw [lemma32_prime_monomial_eq_cpow q.property.pos (β 0),
    lemma32_prime_monomial_eq_cpow q.property.pos (β 1)]

end ZhangLS.Spec
