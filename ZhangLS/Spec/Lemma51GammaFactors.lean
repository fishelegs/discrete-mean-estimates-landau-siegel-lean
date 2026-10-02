import ZhangLS.Spec.Lemma51GammaAsymptotic
import ZhangLS.Spec.Lemma44ModulusControl

/-! # Sharp logarithmic derivatives of the actual Dirichlet Gamma factors -/

namespace ZhangLS.Spec

open Complex Set MeasureTheory

set_option maxHeartbeats 1000000

theorem lemma51_log_horizontal_im_bound {z : ℂ} (him : z.im ≠ 0)
    {a : ℝ} (ha : 0 ≤ a) :
    ‖Complex.log (z + (a : ℂ)) - Complex.log z‖ ≤ a / |z.im| := by
  have hzne (x : ℝ) : z + (x : ℂ) ≠ 0 := by
    intro h
    apply him
    simpa using congrArg Complex.im h
  have hc : Continuous (fun x : ℝ => (z + (x : ℂ))⁻¹) :=
    (continuous_const.add Complex.continuous_ofReal).inv₀ hzne
  have he : (∫ x : ℝ in 0..a, (z + (x : ℂ))⁻¹) =
      Complex.log (z + (a : ℂ)) - Complex.log z := by
    convert intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun x : ℝ => Complex.log (z + (x : ℂ)))
      (f' := fun x : ℝ => (z + (x : ℂ))⁻¹)
      (fun x _ => ?_) (hc.intervalIntegrable 0 a) using 1 <;> simp
    have hp : z + (x : ℂ) ∈ Complex.slitPlane := by
      change 0 < (z + (x : ℂ)).re ∨ (z + (x : ℂ)).im ≠ 0
      right
      simpa using him
    simpa [one_div] using (Complex.ofRealCLM.hasDerivAt.const_add z).clog_real hp
  rw [← he]
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := a) (f := fun x : ℝ => (z + (x : ℂ))⁻¹)
    (C := 1 / |z.im|) (fun x _ => by
      rw [norm_inv, one_div]
      apply (inv_le_inv₀ (norm_pos_iff.mpr (hzne x)) (abs_pos.mpr him)).mpr
      simpa using Complex.abs_im_le_norm (z + (x : ℂ)))
  simpa [abs_of_nonneg ha, div_eq_mul_inv, mul_comm] using hb

theorem lemma51_Gamma_logDeriv_im_axis {z : ℂ}
    (hre : 0 < z.re) (hre' : z.re ≤ 1) (him : 1 ≤ |z.im|) :
    ‖logDeriv Complex.Gamma z - Complex.log ((z.im : ℂ) * I)‖ ≤ 9 / |z.im| := by
  have hzne : z.im ≠ 0 := by intro h; rw [h, abs_zero] at him; norm_num at him
  have hbase : ((z.im : ℂ) * I).im ≠ 0 := by simpa using hzne
  have hb := lemma51_log_horizontal_im_bound hbase (a := z.re) hre.le
  have he : (z.im : ℂ) * I + (z.re : ℂ) = z := by apply Complex.ext <;> simp
  rw [he] at hb
  simp only [mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_one, zero_mul,
    add_zero] at hb
  have ht := norm_add_le (logDeriv Complex.Gamma z - Complex.log z)
    (Complex.log z - Complex.log ((z.im : ℂ) * I))
  have hh := lemma51_Gamma_logDeriv_sub_log_bound hre him
  have hdiv : z.re / |z.im| ≤ 1 / |z.im| :=
    div_le_div_of_nonneg_right hre' (abs_nonneg _)
  have he' : (logDeriv Complex.Gamma z - Complex.log z) +
      (Complex.log z - Complex.log ((z.im : ℂ) * I)) =
      logDeriv Complex.Gamma z - Complex.log ((z.im : ℂ) * I) := by ring
  rw [he'] at ht
  apply ht.trans
  calc
    _ ≤ 8 / |z.im| + 1 / |z.im| := add_le_add hh (hb.trans hdiv)
    _ = 9 / |z.im| := by ring

theorem lemma51_GammaR_logDeriv_im_axis {s : ℂ}
    (hre : 0 < s.re) (hre' : s.re ≤ 2) (him : 2 ≤ |s.im|) :
    ‖logDeriv Complex.Gammaℝ s + Complex.log (Real.pi : ℂ) / 2 -
      Complex.log (((s.im / 2 : ℝ) : ℂ) * I) / 2‖ ≤ 9 / |s.im| := by
  have hzne : s.im ≠ 0 := by intro h; rw [h, abs_zero] at him; norm_num at him
  have hh := lemma51_Gamma_logDeriv_im_axis (z := s / 2)
    (by simp; linarith) (by simp; linarith) (by simp [abs_div]; linarith)
  rw [lemma44_GammaR_logDeriv hzne]
  have he : -Complex.log (Real.pi : ℂ) / 2 + logDeriv Complex.Gamma (s / 2) / 2 +
      Complex.log (Real.pi : ℂ) / 2 - Complex.log (((s.im / 2 : ℝ) : ℂ) * I) / 2 =
      (logDeriv Complex.Gamma (s / 2) - Complex.log (((s / 2).im : ℂ) * I)) / 2 := by
    simp only [Complex.div_ofNat_im]
    ring
  rw [he, norm_div]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  simp only [Complex.div_ofNat_im, abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh ⊢
  exact (div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by ring)

theorem lemma51_gammaFactor_logDeriv_im_axis {N : ℕ}
    (θ : DirichletCharacter ℂ N) {s : ℂ}
    (hre : 0 < s.re) (hre' : s.re ≤ 1) (him : 2 ≤ |s.im|) :
    ‖logDeriv (DirichletCharacter.gammaFactor θ) s + Complex.log (Real.pi : ℂ) / 2 -
      Complex.log (((s.im / 2 : ℝ) : ℂ) * I) / 2‖ ≤ 9 / |s.im| := by
  rcases θ.even_or_odd with heven | hodd
  · have heq : DirichletCharacter.gammaFactor θ = Complex.Gammaℝ := by
      funext z; exact heven.gammaFactor_def z
    rw [heq]
    exact lemma51_GammaR_logDeriv_im_axis hre (by linarith) him
  · have heq : DirichletCharacter.gammaFactor θ = fun z : ℂ => Complex.Gammaℝ (z + 1) := by
      funext z; exact hodd.gammaFactor_def z
    have hzne : (s + 1).im ≠ 0 := by
      simp only [add_im, one_im, add_zero]
      intro h; rw [h, abs_zero] at him; norm_num at him
    have hc := logDeriv_comp (g := fun z : ℂ => z + 1) (x := s)
      (lemma23_GammaR_differentiableAt_of_im_ne_zero hzne)
      (differentiableAt_id.add_const (1 : ℂ))
    rw [heq]
    have hl : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by simpa [Function.comp_def] using hc
    rw [hl]
    simpa using lemma51_GammaR_logDeriv_im_axis (s := s + 1)
      (by simp; linarith) (by simp; linarith) (by simpa using him)

theorem lemma51_log_im_pair {y : ℝ} (hy : 0 < y) :
    Complex.log ((y : ℂ) * I) + Complex.log ((-y : ℂ) * I) =
      (2 * Real.log y : ℝ) := by
  have hp := Complex.log_mul_ofReal y hy I I_ne_zero
  have hm := Complex.log_mul_ofReal y hy (-I) (neg_ne_zero.mpr I_ne_zero)
  rw [show (y : ℂ) * I = I * (y : ℂ) by ring,
    show (-y : ℂ) * I = (-I) * (y : ℂ) by ring, hp, hm,
    Complex.log_I, Complex.log_neg_I]
  push_cast
  ring

theorem lemma51_DirichletZ_logDeriv_sharp {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (hre : 0 < s.re) (hre' : s.re < 1) (him : 2 ≤ s.im) :
    ‖logDeriv (lemma23DirichletZ θ) s + Complex.log (N : ℂ) +
      (Real.log (s.im / (2 * Real.pi)) : ℂ)‖ ≤ 18 / s.im := by
  have ht : 0 < s.im := by linarith
  have hp := lemma51_gammaFactor_logDeriv_im_axis θ hre hre'.le
    (by rwa [abs_of_pos ht])
  have hm := lemma51_gammaFactor_logDeriv_im_axis θ⁻¹
    (s := 1 - s) (by simp; linarith) (by simp; linarith)
    (by simpa [abs_of_pos ht] using him)
  simp only [sub_im, one_im, zero_sub, abs_neg, abs_of_pos ht] at hm
  have hi := lemma51_log_im_pair (y := s.im / 2) (by positivity)
  have hlog : Real.log (s.im / (2 * Real.pi)) = Real.log (s.im / 2) - Real.log Real.pi := by
    rw [show s.im / (2 * Real.pi) = (s.im / 2) / Real.pi by ring,
      Real.log_div (by positivity) Real.pi_ne_zero]
  have he : logDeriv (lemma23DirichletZ θ) s + Complex.log (N : ℂ) +
      (Real.log (s.im / (2 * Real.pi)) : ℂ) =
      -((logDeriv (DirichletCharacter.gammaFactor θ) s + Complex.log (Real.pi : ℂ) / 2 -
        Complex.log (((s.im / 2 : ℝ) : ℂ) * I) / 2) +
      (logDeriv (DirichletCharacter.gammaFactor θ⁻¹) (1 - s) + Complex.log (Real.pi : ℂ) / 2 -
        Complex.log ((((1 - s).im / 2 : ℝ) : ℂ) * I) / 2)) := by
    rw [lemma44_DirichletZ_logDeriv θ hθ hN ht.ne', hlog,
      ← Complex.ofReal_log Real.pi_pos.le]
    simp only [sub_im, one_im, zero_sub, neg_div, ofReal_neg]
    have hi' : Complex.log (((s.im / 2 : ℝ) : ℂ) * I) +
        Complex.log (-((s.im / 2 : ℝ) : ℂ) * I) = (2 * Real.log (s.im / 2) : ℝ) := hi
    push_cast at hi' ⊢
    linear_combination -hi' / 2
  rw [he, norm_neg]
  rw [abs_of_pos ht] at hp
  simp only [sub_im, one_im, zero_sub, neg_div, ofReal_neg] at hm ⊢
  apply (norm_add_le _ _).trans
  exact (add_le_add hp hm).trans_eq (by ring)

end ZhangLS.Spec
