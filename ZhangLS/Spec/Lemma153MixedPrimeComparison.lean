import ZhangLS.Spec.Lemma153MixedVariation
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped Classical
set_option maxHeartbeats 2500000

lemma lemma153_mixed_prime_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) (q : Nat.Primes) :
    ‖lemma153MixedRatio χ β γ q-lemma153MixedRatio χ (fun _ => 0) 0 q‖ ≤
      (520+1000*lemma152CorrectionConstant)*(‖β 0‖+‖β 1‖+‖γ‖)*(q.val:ℝ)^(-(4/5:ℝ)) := by
  let E := ‖β 0‖+‖β 1‖+‖γ‖
  let Q := (q.val:ℝ)^(-(4/5:ℝ))
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let y := lemma32PrimeMonomial q.val (1-γ)
  let H := 1-v*y
  let H₀ := 1-v*u
  let T := lemma152PrimeFactor χ β q (1-γ)
  let T₀ := lemma152PrimeFactor χ (fun _ => 0) q 1
  let lam := lemma152LambdaFactor χ β q.val 1
  let lam₀ := lemma152LambdaFactor χ (fun _ => 0) q.val 1
  have hE : 0≤E := by dsimp [E]; positivity
  have hQ : 0≤Q := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hC := lemma152_correction_constant_pos
  have hq0 : (0:ℝ)<q.val := Nat.cast_pos.mpr q.property.pos
  have hq1 : (1:ℝ)≤q.val := by exact_mod_cast q.property.one_lt.le
  have hu : ‖u‖ ≤ 1/2 := by
    dsimp [u]
    rw [norm_inv,Complex.norm_natCast]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num : (0:ℝ)<2)
      (show (2:ℝ) ≤ q.val by exact_mod_cast q.property.two_le)
  have hy : ‖y‖ = ‖u‖ := by
    dsimp [y,u]
    rw [lemma83_prime_monomial_norm_rpow q.property.pos]
    simp [hpar.gamma_re,Real.rpow_neg_one]
  have hv : ‖v‖ ≤ 1 := χ.evalNat_norm_le_one _
  have hvu : ‖v*u‖ ≤ 1/2 := by rw [norm_mul]; exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hu
  have hvy : ‖v*y‖ ≤ 1/2 := by rw [norm_mul,hy]; exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hu
  have hH : 1/2 ≤ ‖H‖ := by have hh := lemma152_one_sub_norm_lower hvy; dsimp [H]; linarith
  have hH₀ : 1/2 ≤ ‖H₀‖ := by have hh := lemma152_one_sub_norm_lower hvu; dsimp [H₀]; linarith
  have hHu : ‖H‖ ≤ 3/2 := by have hh := norm_sub_le (1:ℂ) (v*y); rw [norm_one] at hh; dsimp [H]; linarith
  have hT : 1/2 ≤ ‖T‖ := lemma153_prime_normalizer_lower χ β γ hpar q
  have hT₀ : 1 ≤ ‖T₀‖ := (lemma153_zero_center_factor_real χ q).2.trans (Complex.re_le_norm _)
  have hT₀u : ‖T₀‖ ≤ 1+lemma152CorrectionConstant := by
    have hh := lemma152_prime_norm_le χ (fun _ => 0) (fun _ => rfl) q 1 (by norm_num)
    have hp := Real.rpow_le_one_of_one_le_of_nonpos hq1 (by norm_num : -(19/10:ℝ)≤0)
    dsimp [T₀]
    nlinarith only [hh,mul_le_of_le_one_right hC.le hp]
  have hLam₀ : ‖lam₀‖ ≤ 5 := lemma152_lambda_norm_le χ (fun _ => 0) (fun _ => rfl) q.property
  have hyD : ‖y-u‖ ≤ 10*E*Q := by
    have hh := lemma152_center_monomial_variation q.property.pos (1-γ)
      (by simpa using hpar.gamma_small)
    simp only [sub_sub_cancel_left,norm_neg] at hh
    dsimp [y,u,Q,E]
    apply hh.trans
    gcongr
    linarith [norm_nonneg (β 0),norm_nonneg (β 1)]
  have hHD : ‖H-H₀‖ ≤ 10*E*Q := by
    have he : H-H₀ = -v*(y-u) := by dsimp [H,H₀]; ring
    rw [he,norm_mul,norm_neg]
    exact (mul_le_of_le_one_left (norm_nonneg _) hv).trans hyD
  have hTD : ‖T-T₀‖ ≤ 10*lemma152CorrectionConstant*E*Q := by
    have hh := lemma152_prime_comparison χ β hpar.beta_re hpar.beta_small q (1-γ)
      (by simp [hpar.gamma_re]; norm_num) (by simpa using hpar.gamma_small)
    simp only [sub_sub_cancel_left,norm_neg] at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hq1 (by norm_num : -(17/10:ℝ)≤-(4/5:ℝ))) (by positivity)
  have hLamD : ‖lam-lam₀‖ ≤ 30*E*Q := by
    let a := (q.val:ℂ)^(-β 0)
    let b := (q.val:ℂ)^(-β 1)
    have ha : ‖a‖ ≤ 1 := (lemma83_cpow_shift_norm q.property.pos _ (hpar.beta_re 0)).le
    have hb : ‖b‖ ≤ 1 := (lemma83_cpow_shift_norm q.property.pos _ (hpar.beta_re 1)).le
    have haD := lemma152_shift_monomial_variation q.property.pos (β 0) (hpar.beta_small 0)
    have hbD := lemma152_shift_monomial_variation q.property.pos (β 1) (hpar.beta_small 1)
    rw [lemma32_prime_monomial_eq_cpow q.property.pos] at haD hbD
    have hab : ‖a-1‖+‖b-1‖ ≤ 10*E*(q.val:ℝ)^(1/5:ℝ) := by
      dsimp [a,b,E]
      nlinarith only [haD,hbD,mul_nonneg (norm_nonneg γ)
        (Real.rpow_nonneg (Nat.cast_nonneg q.val) (1/5:ℝ))]
    have he : lam = lemma153LocalLambda a b u v := lemma152_lambda_factor_rational χ β q.property.pos
    have he₀ : lam₀ = lemma153LocalLambda 1 1 u v := by
      dsimp [lam₀]
      rw [lemma152_lambda_factor_rational χ (fun _ => 0) q.property.pos]
      simp [lemma153LocalLambda,u,v]
    rw [he,he₀]
    apply (lemma153_lambda_shift_variation a b u v ha hb hu hv).trans
    calc
      _ ≤ 3*‖u‖*(10*E*(q.val:ℝ)^(1/5:ℝ)) := mul_le_mul_of_nonneg_left hab (by positivity)
      _ = 30*E*Q := by
        dsimp [u,Q]
        rw [norm_inv,Complex.norm_natCast,← Real.rpow_neg_one]
        calc
          _ = (30*E)*((q.val:ℝ)^(-1:ℝ)*(q.val:ℝ)^(1/5:ℝ)) := by ring
          _ = _ := by rw [← Real.rpow_add hq0]; norm_num
  have hd : 1/4 ≤ ‖H*T‖ := by rw [norm_mul]; nlinarith [norm_nonneg H,norm_nonneg T]
  have hd₀ : 1/2 ≤ ‖H₀*T₀‖ := by rw [norm_mul]; nlinarith [norm_nonneg H₀,norm_nonneg T₀]
  have hdenD : ‖H*T-H₀*T₀‖ ≤ (10+25*lemma152CorrectionConstant)*E*Q := by
    apply (lemma153_norm_mul_difference H T H₀ T₀).trans
    calc
      _ ≤ (3/2)*(10*lemma152CorrectionConstant*E*Q)+(10*E*Q)*(1+lemma152CorrectionConstant) := by
        exact add_le_add (mul_le_mul hHu hTD (norm_nonneg _) (by norm_num))
          (mul_le_mul hHD hT₀u (norm_nonneg _) (by positivity))
      _ = _ := by ring
  rw [lemma153_actual_mixed_ratio_reduction χ β γ hpar q,
    lemma153_actual_mixed_ratio_reduction χ (fun _ => 0) 0 lemma153_zero_parameters q]
  simp only [sub_zero,lemma83_prime_monomial_one q.property.pos]
  change ‖lam/(H*T)-lam₀/(H₀*T₀)‖ ≤ _
  apply (lemma153_quotient_difference_bound lam lam₀ (H*T) (H₀*T₀) hLam₀ hd hd₀).trans
  calc
    _ ≤ 4*(30*E*Q)+40*((10+25*lemma152CorrectionConstant)*E*Q) := by gcongr
    _ = _ := by dsimp [E,Q]; ring

end ZhangLS.Spec
