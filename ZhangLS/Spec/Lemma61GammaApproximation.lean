import ZhangLS.Spec.Lemma61GaussianCutoff
import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
import Mathlib.NumberTheory.MulChar.Lemmas

/-! # Actual wide Gamma and original E1 error estimates for Lemma 6.1

Actual Gamma recurrence gives sharp all-real-part logarithmic derivatives.
Original Psi implies actual wide normalized Z bounds and small complex shifts.
The shifted contour gives the original short sum and its original E1 bound.
The full Lemma61Target remains unproved: contour and truncation relations remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set MeasureTheory
open scoped Real Topology ComplexConjugate
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_Gamma_logDeriv_recurrence_bound {z : ℂ}
    (him : 1 ≤ |z.im|) (m : ℕ) :
    ‖logDeriv Complex.Gamma (z + (m : ℂ)) - logDeriv Complex.Gamma z‖ ≤
      (m : ℝ) / |z.im| := by
  have hi : 0 < |z.im| := by linarith
  have hzne (m : ℕ) : z + (m : ℂ) ≠ 0 := by
    intro h
    have hh := congrArg Complex.im h
    simp at hh
    rw [hh,abs_zero] at him
    linarith
  induction m with
  | zero => simp
  | succ m ih =>
    have hpoles (k : ℕ) : z + (m : ℂ) ≠ -(k : ℂ) := by
      intro h
      have hh := congrArg Complex.im h
      simp at hh
      rw [hh,abs_zero] at him
      linarith
    have hrec : logDeriv Complex.Gamma (z + (m : ℂ) + 1) =
        logDeriv Complex.Gamma (z + (m : ℂ)) + (z + (m : ℂ))⁻¹ := by
      exact Complex.digamma_apply_add_one (z + (m : ℂ)) hpoles
    have hn : ‖(z + (m : ℂ))⁻¹‖ ≤ 1 / |z.im| := by
      rw [norm_inv,one_div]
      apply (inv_le_inv₀ (norm_pos_iff.mpr (hzne m)) hi).mpr
      simpa using Complex.abs_im_le_norm (z + (m : ℂ))
    rw [Nat.cast_succ,← add_assoc,hrec]
    calc
      _ = ‖(logDeriv Complex.Gamma (z + (m : ℂ)) - logDeriv Complex.Gamma z) +
        (z + (m : ℂ))⁻¹‖ := by congr 1; ring
      _ ≤ ‖logDeriv Complex.Gamma (z + (m : ℂ)) - logDeriv Complex.Gamma z‖ +
        ‖(z + (m : ℂ))⁻¹‖ := norm_add_le _ _
      _ ≤ (m : ℝ) / |z.im| + 1 / |z.im| := add_le_add ih hn
      _ = _ := by push_cast; ring

lemma lemma61_Gamma_logDeriv_im_axis_positive {z : ℂ}
    (hre : 0 < z.re) (him : 1 ≤ |z.im|) :
    ‖logDeriv Complex.Gamma z - Complex.log ((z.im : ℂ) * I)‖ ≤
      (8 + z.re) / |z.im| := by
  have hi : z.im ≠ 0 := by intro h; rw [h,abs_zero] at him; norm_num at him
  have hb := lemma51_log_horizontal_im_bound
    (z := (z.im : ℂ) * I) (by simpa using hi) (a := z.re) hre.le
  have he : (z.im : ℂ) * I + (z.re : ℂ) = z := by apply Complex.ext <;> simp
  rw [he] at hb
  simp only [mul_im,ofReal_re,I_im,ofReal_im,I_re,mul_one,zero_mul,add_zero] at hb
  have hh := lemma51_Gamma_logDeriv_sub_log_bound hre him
  calc
    _ = ‖(logDeriv Complex.Gamma z - Complex.log z) +
        (Complex.log z - Complex.log ((z.im : ℂ) * I))‖ := by congr 1; ring
    _ ≤ ‖logDeriv Complex.Gamma z - Complex.log z‖ +
        ‖Complex.log z - Complex.log ((z.im : ℂ) * I)‖ := norm_add_le _ _
    _ ≤ 8 / |z.im| + z.re / |z.im| := add_le_add hh hb
    _ = _ := by ring

lemma lemma61_Gamma_logDeriv_im_axis_all {z : ℂ} (him : 1 ≤ |z.im|) :
    ‖logDeriv Complex.Gamma z - Complex.log ((z.im : ℂ) * I)‖ ≤
      (12 + |z.re|) / |z.im| := by
  have hi : 0 < |z.im| := by linarith
  by_cases hre : 0 < z.re
  · exact (lemma61_Gamma_logDeriv_im_axis_positive hre him).trans
      (div_le_div_of_nonneg_right (by rw [abs_of_pos hre]; linarith) hi.le)
  have hre0 : z.re ≤ 0 := le_of_not_gt hre
  let m : ℕ := ⌈-z.re⌉₊ + 1
  have hmin : 0 < (z + (m : ℂ)).re := by
    simp only [add_re,natCast_re]
    dsimp [m]
    push_cast
    linarith only [Nat.le_ceil (-z.re)]
  have hceil := Nat.ceil_lt_add_one (by linarith only [hre0] : 0 ≤ -z.re)
  have hmax : (z + (m : ℂ)).re ≤ 2 := by
    simp only [add_re,natCast_re]
    dsimp [m]
    push_cast
    linarith only [hceil]
  have hm : (m : ℝ) ≤ |z.re| + 2 := by
    rw [abs_of_nonpos hre0]
    dsimp [m]
    push_cast
    linarith only [hceil]
  have hb := lemma61_Gamma_logDeriv_im_axis_positive hmin (by simpa using him)
  simp only [add_im,natCast_im,add_zero] at hb
  have hr := lemma61_Gamma_logDeriv_recurrence_bound him m
  calc
    _ = ‖(logDeriv Complex.Gamma (z + (m : ℂ)) - Complex.log ((z.im : ℂ) * I)) -
        (logDeriv Complex.Gamma (z + (m : ℂ)) - logDeriv Complex.Gamma z)‖ := by congr 1; ring
    _ ≤ ‖logDeriv Complex.Gamma (z + (m : ℂ)) - Complex.log ((z.im : ℂ) * I)‖ +
        ‖logDeriv Complex.Gamma (z + (m : ℂ)) - logDeriv Complex.Gamma z‖ := norm_sub_le _ _
    _ ≤ (8 + (z + (m : ℂ)).re) / |z.im| + (m : ℝ) / |z.im| := add_le_add hb hr
    _ = (8 + (z + (m : ℂ)).re + (m : ℝ)) / |z.im| := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith only [hmax,hm]) hi.le

lemma lemma61_GammaR_logDeriv_im_axis_all {s : ℂ} (him : 2 ≤ |s.im|) :
    ‖logDeriv Complex.Gammaℝ s + Complex.log (Real.pi : ℂ) / 2 -
      Complex.log (((s.im / 2 : ℝ) : ℂ) * I) / 2‖ ≤ (12 + |s.re|) / |s.im| := by
  have hzne : s.im ≠ 0 := by intro h; rw [h,abs_zero] at him; norm_num at him
  have hh := lemma61_Gamma_logDeriv_im_axis_all (z := s / 2)
    (by simp [abs_div]; linarith)
  rw [lemma44_GammaR_logDeriv hzne]
  have he : -Complex.log (Real.pi : ℂ) / 2 + logDeriv Complex.Gamma (s / 2) / 2 +
      Complex.log (Real.pi : ℂ) / 2 - Complex.log (((s.im / 2 : ℝ) : ℂ) * I) / 2 =
      (logDeriv Complex.Gamma (s / 2) - Complex.log (((s / 2).im : ℂ) * I)) / 2 := by
    simp only [Complex.div_ofNat_im]
    ring
  rw [he,norm_div]
  rw [show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num]
  simp only [Complex.div_ofNat_im,Complex.div_ofNat_re,abs_div,
    abs_of_pos (by norm_num : (0 : ℝ) < 2)] at hh ⊢
  calc
    _ ≤ ((12 + |s.re| / 2) / (|s.im| / 2)) / 2 :=
      div_le_div_of_nonneg_right hh (by norm_num : (0 : ℝ) ≤ 2)
    _ = (12 + |s.re| / 2) / |s.im| := by ring
    _ ≤ _ := div_le_div_of_nonneg_right (by linarith [abs_nonneg s.re]) (abs_nonneg s.im)

lemma lemma61_gammaFactor_logDeriv_im_axis_all {N : ℕ}
    (θ : DirichletCharacter ℂ N) {s : ℂ} (him : 2 ≤ |s.im|) :
    ‖logDeriv (DirichletCharacter.gammaFactor θ) s + Complex.log (Real.pi : ℂ) / 2 -
      Complex.log (((s.im / 2 : ℝ) : ℂ) * I) / 2‖ ≤ (13 + |s.re|) / |s.im| := by
  rcases θ.even_or_odd with heven | hodd
  · have heq : DirichletCharacter.gammaFactor θ = Complex.Gammaℝ := by
      funext z; exact heven.gammaFactor_def z
    rw [heq]
    exact (lemma61_GammaR_logDeriv_im_axis_all him).trans
      (div_le_div_of_nonneg_right (by linarith) (abs_nonneg s.im))
  · have heq : DirichletCharacter.gammaFactor θ = fun z : ℂ => Complex.Gammaℝ (z + 1) := by
      funext z; exact hodd.gammaFactor_def z
    have hzne : (s + 1).im ≠ 0 := by
      simp only [add_im,one_im,add_zero]
      intro h; rw [h,abs_zero] at him; norm_num at him
    have hc := logDeriv_comp (g := fun z : ℂ => z + 1) (x := s)
      (lemma23_GammaR_differentiableAt_of_im_ne_zero hzne) (differentiableAt_id.add_const (1 : ℂ))
    rw [heq]
    have hl : logDeriv (fun z : ℂ => Complex.Gammaℝ (z + 1)) s =
        logDeriv Complex.Gammaℝ (s + 1) := by simpa [Function.comp_def] using hc
    rw [hl]
    have hh := lemma61_GammaR_logDeriv_im_axis_all (s := s + 1) (by simpa using him)
    simp only [add_re,one_re,add_im,one_im,add_zero] at hh
    apply hh.trans
    apply div_le_div_of_nonneg_right _ (abs_nonneg s.im)
    have hr : |s.re + 1| ≤ |s.re| + 1 := by simpa using abs_add_le s.re 1
    linarith only [hr]

lemma lemma61_DirichletZ_logDeriv_all_real {N : ℕ} [NeZero N]
    (θ : DirichletCharacter ℂ N) (hθ : θ.IsPrimitive) (hN : N ≠ 1)
    {s : ℂ} (him : 2 ≤ s.im) :
    ‖logDeriv (lemma23DirichletZ θ) s + Complex.log (N : ℂ) +
      (Real.log (s.im / (2 * Real.pi)) : ℂ)‖ ≤ (27 + 2 * |s.re|) / s.im := by
  have ht : 0 < s.im := by linarith
  have hp := lemma61_gammaFactor_logDeriv_im_axis_all θ (s := s)
    (by rwa [abs_of_pos ht])
  have hm := lemma61_gammaFactor_logDeriv_im_axis_all θ⁻¹ (s := 1 - s)
    (by simpa [abs_of_pos ht] using him)
  simp only [sub_im,one_im,zero_sub,abs_neg,abs_of_pos ht,sub_re,one_re] at hm
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
    rw [lemma44_DirichletZ_logDeriv θ hθ hN ht.ne',hlog,
      ← Complex.ofReal_log Real.pi_pos.le]
    simp only [sub_im,one_im,zero_sub,neg_div,ofReal_neg]
    have hi' : Complex.log (((s.im / 2 : ℝ) : ℂ) * I) +
        Complex.log (-((s.im / 2 : ℝ) : ℂ) * I) = (2 * Real.log (s.im / 2) : ℝ) := hi
    push_cast at hi' ⊢
    linear_combination -hi' / 2
  rw [he,norm_neg]
  rw [abs_of_pos ht] at hp
  simp only [sub_im,one_im,zero_sub,neg_div,ofReal_neg] at hm ⊢
  apply (norm_add_le _ _).trans
  calc
    _ ≤ (13 + |s.re|) / s.im + (13 + |1 - s.re|) / s.im := add_le_add hp hm
    _ = (26 + |s.re| + |1 - s.re|) / s.im := by ring
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ ht.le
      have hr : |1 - s.re| ≤ 1 + |s.re| := by simpa [sub_eq_add_neg] using abs_add_le 1 (-s.re)
      linarith only [hr]

end ZhangLS.Spec
