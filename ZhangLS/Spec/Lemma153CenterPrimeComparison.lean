import ZhangLS.Spec.Lemma153MixedPrimeComparison
import ZhangLS.Spec.Lemma153CenterLipschitz
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
open scoped Classical
set_option maxHeartbeats 2500000

lemma lemma153_unramified_reduced_center {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) (q : Nat.Primes) :
    lemma153UnramifiedPrimeFactor χ β γ q 1 =
      lemma153ReducedCorrection (lemma153MixedRatio χ β γ q) (χ.evalNat q.val/(1-(q.val:ℂ)⁻¹))
        (lemma32PrimeMonomial q.val (1-γ)) (χ.evalNat q.val*(q.val:ℂ)^γ) (q.val:ℂ)⁻¹ := by
  unfold lemma153UnramifiedPrimeFactor
  rw [lemma83_prime_monomial_one q.property.pos,
    lemma153_reduced_correction_identity _ _ _ _ _ _ _ (lemma153_actual_local_ratio_bounds χ β γ hpar q).1]
  rfl

noncomputable def lemma153CenterPrimeConstant : ℝ :=
  200000*(540+1000*lemma152CorrectionConstant)

lemma lemma153_center_prime_constant_pos : 0 < lemma153CenterPrimeConstant := by
  have := lemma152_correction_constant_pos
  unfold lemma153CenterPrimeConstant
  positivity

lemma lemma153_unramified_center_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) (q : Nat.Primes) :
    ‖lemma153UnramifiedPrimeFactor χ β γ q 1-lemma153UnramifiedPrimeFactor χ (fun _ => 0) 0 q 1‖ ≤
      lemma153CenterPrimeConstant*(‖β 0‖+‖β 1‖+‖γ‖)*(q.val:ℝ)^(-(9/5:ℝ)) := by
  let E := ‖β 0‖+‖β 1‖+‖γ‖
  let u : ℂ := (q.val:ℂ)⁻¹
  let v := χ.evalNat q.val
  let A := v/(1-u)
  let y := lemma32PrimeMonomial q.val (1-γ)
  let t := v*(q.val:ℂ)^γ
  let f := lemma153MixedRatio χ β γ q
  let f₀ := lemma153MixedRatio χ (fun _ => 0) 0 q
  have hE : 0≤E := by dsimp [E]; positivity
  have hq0 : (0:ℝ)<q.val := Nat.cast_pos.mpr q.property.pos
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
  have hA : ‖A‖ ≤ 2 := by
    have hd : 1/2 ≤ ‖1-u‖ := by have hh := lemma152_one_sub_norm_lower hu; linarith
    dsimp [A]
    rw [norm_div]
    exact (div_le_div₀ (by positivity) hv (by norm_num : (0:ℝ)<1/2) hd).trans (by norm_num)
  have ht : ‖t‖ ≤ 1 := by
    have hw : ‖(q.val:ℂ)^γ‖ = 1 := by
      simpa using lemma83_cpow_shift_norm q.property.pos (-γ) (by simp [hpar.gamma_re])
    dsimp [t]
    simpa only [norm_mul,hw,mul_one] using hv
  have hr₀ := lemma153_actual_local_ratio_bounds χ (fun _ => 0) 0 lemma153_zero_parameters q
  have hf₀ : ‖f₀‖ ≤ 10000 := hr₀.2.2.2
  have hf₀1 : ‖f₀-1‖ ≤ 30000*‖u‖ := by
    apply lemma153_mixed_ratio_sub_one _ _ _ A u ‖u‖ hA le_rfl
    · simpa only [sub_zero,lemma83_prime_monomial_one q.property.pos] using hr₀.2.2.1
    · exact hf₀
  have hfD := lemma153_mixed_prime_comparison χ β γ hpar q
  have hyD : ‖y-u‖ ≤ 10*E*(q.val:ℝ)^(-(4/5:ℝ)) := by
    have hh := lemma152_center_monomial_variation q.property.pos (1-γ) (by simpa using hpar.gamma_small)
    simp only [sub_sub_cancel_left,norm_neg] at hh
    apply hh.trans
    dsimp [E]
    gcongr
    linarith [norm_nonneg (β 0),norm_nonneg (β 1)]
  have htD : ‖t-v‖ ≤ 10*E*(q.val:ℝ)^(1/5:ℝ) := by
    have hh := lemma152_shift_monomial_variation q.property.pos (-γ) (by simpa using hpar.gamma_small)
    rw [lemma32_prime_monomial_eq_cpow q.property.pos,neg_neg,norm_neg] at hh
    rw [show t-v = v*((q.val:ℂ)^γ-1) by dsimp [t]; ring,norm_mul]
    apply (mul_le_of_le_one_left (norm_nonneg _) hv).trans
    apply hh.trans
    dsimp [E]
    gcongr
    linarith [norm_nonneg (β 0),norm_nonneg (β 1)]
  have hpow1 : ‖u‖*(q.val:ℝ)^(-(4/5:ℝ)) = (q.val:ℝ)^(-(9/5:ℝ)) := by
    dsimp [u]
    rw [norm_inv,Complex.norm_natCast,← Real.rpow_neg_one,← Real.rpow_add hq0]
    norm_num
  have hpow2 : ‖u‖^2*(q.val:ℝ)^(1/5:ℝ) = (q.val:ℝ)^(-(9/5:ℝ)) := by
    dsimp [u]
    rw [norm_inv,Complex.norm_natCast,← Real.rpow_neg_one,← Real.rpow_natCast,
      ← Real.rpow_mul hq0.le,← Real.rpow_add hq0]
    norm_num
  have huf : ‖u‖*‖f-f₀‖ ≤ (520+1000*lemma152CorrectionConstant)*E*(q.val:ℝ)^(-(9/5:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_left hfD (norm_nonneg u)
    calc
      _ ≤ ‖u‖*((520+1000*lemma152CorrectionConstant)*E*(q.val:ℝ)^(-(4/5:ℝ))) := hh
      _ = _ := by rw [show ‖u‖*((520+1000*lemma152CorrectionConstant)*E*(q.val:ℝ)^(-(4/5:ℝ))) =
        ((520+1000*lemma152CorrectionConstant)*E)*(‖u‖*(q.val:ℝ)^(-(4/5:ℝ))) by ring,hpow1]
  have huy : ‖u‖*‖y-u‖ ≤ 10*E*(q.val:ℝ)^(-(9/5:ℝ)) := by
    calc
      _ ≤ ‖u‖*(10*E*(q.val:ℝ)^(-(4/5:ℝ))) := mul_le_mul_of_nonneg_left hyD (norm_nonneg _)
      _ = _ := by rw [show ‖u‖*(10*E*(q.val:ℝ)^(-(4/5:ℝ))) = (10*E)*(‖u‖*(q.val:ℝ)^(-(4/5:ℝ))) by ring,hpow1]
  have hut : ‖u‖^2*‖t-v‖ ≤ 10*E*(q.val:ℝ)^(-(9/5:ℝ)) := by
    calc
      _ ≤ ‖u‖^2*(10*E*(q.val:ℝ)^(1/5:ℝ)) := mul_le_mul_of_nonneg_left htD (sq_nonneg _)
      _ = _ := by rw [show ‖u‖^2*(10*E*(q.val:ℝ)^(1/5:ℝ)) = (10*E)*(‖u‖^2*(q.val:ℝ)^(1/5:ℝ)) by ring,hpow2]
  have hb := lemma153_reduced_center_lipschitz f f₀ A y u t v u ‖u‖ (norm_nonneg _) hu rfl hy.le le_rfl hA ht hv hf₀ hf₀1
  rw [lemma153_unramified_reduced_center χ β γ hpar q,
    lemma153_unramified_reduced_center χ (fun _ => 0) 0 lemma153_zero_parameters q]
  simp only [sub_zero,lemma83_prime_monomial_one q.property.pos,Complex.cpow_zero,mul_one]
  apply hb.trans
  unfold lemma153CenterPrimeConstant
  dsimp [E] at *
  nlinarith only [huf,huy,hut]

lemma lemma153_center_prime_comparison {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 2 → ℂ) (γ : ℂ) (hpar : Lemma153SmallParameters β γ) (q : Nat.Primes) :
    ‖lemma153PrimeFactor χ β γ q 1-lemma153PrimeFactor χ (fun _ => 0) 0 q 1‖ ≤
      lemma153CenterPrimeConstant*(‖β 0‖+‖β 1‖+‖γ‖)*(q.val:ℝ)^(-(9/5:ℝ)) := by
  unfold lemma153PrimeFactor
  split_ifs
  · simp only [sub_self,norm_zero]
    have := lemma153_center_prime_constant_pos
    positivity
  · exact lemma153_unramified_center_comparison χ β γ hpar q

end ZhangLS.Spec
