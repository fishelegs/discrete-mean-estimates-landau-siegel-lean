import ZhangLS.Spec.Lemma61WideZBounds

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

lemma lemma61_complex_transport {f : ℂ → ℂ} {s w : ℂ} {c B K A : ℝ}
    (hB : 0 ≤ B) (hK : 0 ≤ K) (hA : 0 ≤ A) (ha : |c * w.re| ≤ A)
    (hf : ∀ x ∈ Icc (0 : ℝ) 1, DifferentiableAt ℂ f (s + (x : ℂ) * w))
    (hne : ∀ x ∈ Icc (0 : ℝ) 1, f (s + (x : ℂ) * w) ≠ 0)
    (hfn : ∀ x ∈ Icc (0 : ℝ) 1, ‖f (s + (x : ℂ) * w)‖ ≤ B)
    (hld : ∀ x ∈ Icc (0 : ℝ) 1,
      ‖logDeriv f (s + (x : ℂ) * w) + (c : ℂ)‖ ≤ K) :
    ‖(f (s + w) - f s * Complex.exp (-(c : ℂ) * w)) / w‖ ≤
      B * K * Real.exp (2 * A) := by
  by_cases hw0 : w = 0
  · simp [hw0]
    positivity
  let G : ℂ → ℂ := fun z => f (s + z * w) * Complex.exp ((c : ℂ) * z * w)
  let d : ℝ → ℂ := fun x =>
    (f (s + (x : ℂ) * w) * (logDeriv f (s + (x : ℂ) * w) + (c : ℂ))) * w *
      Complex.exp ((c : ℂ) * (x : ℂ) * w)
  have hexpn (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ‖Complex.exp ((c : ℂ) * (x : ℂ) * w)‖ ≤ Real.exp A := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have hxn : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
    have hh : |x * (c * w.re)| ≤ A := by
      rw [abs_mul]
      nlinarith only [hxn,ha,abs_nonneg (c * w.re),hA]
    have he : ((c : ℂ) * (x : ℂ) * w).re = x * (c * w.re) := by simp [mul_re]; ring
    rw [he]
    exact (le_abs_self _).trans hh
  have hd (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      HasDerivAt (fun x : ℝ => G (x : ℂ)) (d x) x := by
    have harg : HasDerivAt (fun z : ℂ => s + z * w) w (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).mul_const w).const_add s
    have hfd := (hf x hx).hasDerivAt.comp (x : ℂ) harg
    have hea : HasDerivAt (fun z : ℂ => (c : ℂ) * z * w) ((c : ℂ) * w) (x : ℂ) := by
      simpa using ((hasDerivAt_id (x : ℂ)).const_mul (c : ℂ)).mul_const w
    have hg := hfd.mul hea.cexp
    simp only [Function.comp_def] at hg
    have he : deriv f (s + (x : ℂ) * w) * w * Complex.exp ((c : ℂ) * (x : ℂ) * w) +
        f (s + (x : ℂ) * w) *
          (Complex.exp ((c : ℂ) * (x : ℂ) * w) * ((c : ℂ) * w)) = d x := by
      dsimp [d]
      rw [logDeriv_apply]
      field_simp [hne x hx]
    rw [he] at hg
    exact hg.comp_ofReal
  have hdn (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) :
      ‖d x‖ ≤ B * K * ‖w‖ * Real.exp A := by
    dsimp [d]
    rw [norm_mul,norm_mul,norm_mul]
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right (mul_le_mul (hfn x hx) (hld x hx) (norm_nonneg _) hB)
        (norm_nonneg w)) (hexpn x hx) (norm_nonneg _) (by positivity)
  have hb := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x hx => (hd x hx).hasDerivWithinAt) hdn (convex_Icc (0 : ℝ) 1)
    (by norm_num : (0 : ℝ) ∈ Icc (0 : ℝ) 1) (by norm_num : (1 : ℝ) ∈ Icc (0 : ℝ) 1)
  norm_num only [Complex.ofReal_one,Complex.ofReal_zero,sub_zero,norm_one,mul_one] at hb
  have he : f (s + w) - f s * Complex.exp (-(c : ℂ) * w) =
      (G 1 - G 0) * Complex.exp (-(c : ℂ) * w) := by
    dsimp [G]
    simp only [one_mul,zero_mul,mul_zero,add_zero,Complex.exp_zero,mul_one]
    rw [sub_mul,mul_assoc,← Complex.exp_add]
    simp only [show (c : ℂ) * w + -(c : ℂ) * w = 0 by ring,Complex.exp_zero,mul_one]
  have hen : ‖Complex.exp (-(c : ℂ) * w)‖ ≤ Real.exp A := by
    rw [Complex.norm_exp]
    apply Real.exp_le_exp.mpr
    have ht := (neg_le_abs (c * w.re)).trans ha
    simpa [mul_re] using ht
  have hbn : ‖f (s + w) - f s * Complex.exp (-(c : ℂ) * w)‖ ≤
      B * K * Real.exp (2 * A) * ‖w‖ := by
    rw [he,norm_mul]
    calc
      _ ≤ (B * K * ‖w‖ * Real.exp A) * Real.exp A :=
        mul_le_mul hb hen (norm_nonneg _) (by positivity)
      _ = _ := by rw [show 2 * A = A + A by ring,Real.exp_add]; ring
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hw0)).mpr hbn

lemma lemma61_shift_segment_bounds {D : ℕ} {s w : ℂ}
    (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    (hwre : |w.re| ≤ 4 * lemma44PaperAlpha D) (hwim : |w.im| ≤ lemma23PaperL D ^ 20)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    |(s + (x : ℂ) * w).re - 1 / 2| ≤ 6 * lemma44PaperAlpha D ∧
      |(s + (x : ℂ) * w).im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3 := by
  have hxn : |x| ≤ 1 := by rw [abs_of_nonneg hx.1]; exact hx.2
  have hm (a : ℝ) : |x * a| ≤ |a| := by rw [abs_mul]; nlinarith [abs_nonneg a]
  have her : (s + (x : ℂ) * w).re - 1 / 2 = (s.re - 1 / 2) + x * w.re := by simp [mul_re]; ring
  have hei : (s + (x : ℂ) * w).im - (lemma23PaperCenter D).im =
      (s.im - (lemma23PaperCenter D).im) + x * w.im := by simp [mul_im]; ring
  have hpow : lemma23PaperL D ^ 20 ≤ lemma23PaperL D ^ 405 :=
    pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  constructor
  · rw [her]
    exact (abs_add_le _ _).trans (by linarith only [hs.1,hwre,hm w.re])
  · rw [hei]
    exact (abs_add_le _ _).trans (by linarith only [hs.2,hwim,hm w.im,hpow])

lemma lemma61_actual_complex_Z_shift {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s w : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    (hwre : |w.re| ≤ 4 * lemma44PaperAlpha D) (hwim : |w.im| ≤ lemma23PaperL D ^ 20) :
    ‖(lemma23DirichletZ ψ (s + w) - lemma23DirichletZ ψ s *
      ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w)) / w‖ ≤
        (35 * Real.exp (238 * Real.pi)) * lemma23PaperL D ^ (-68 : ℤ) := by
  let c : ℝ := Real.log (lemma23PaperP D * lemma51PaperT0 D)
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hT : 0 < lemma51PaperT0 D := pow_pos hL0 519
  have hc := lemma61_PT0_log_bounds hL
  have ha : |c * w.re| ≤ 8 * Real.pi := by
    rw [abs_mul,abs_of_nonneg hc.1]
    have he : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
      simp only [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
      field_simp
    calc
      _ ≤ (2 * lemma23PaperL D ^ 9) * (4 * lemma44PaperAlpha D) :=
        mul_le_mul hc.2 hwre (abs_nonneg _) (by positivity)
      _ = _ := by nlinarith only [he]
  have hseg (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) := lemma61_shift_segment_bounds hL hs hwre hwim hx
  have ht (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : 0 < (s + (x : ℂ) * w).im :=
    hT.trans_le (lemma61_wide_height_data hL (hseg x hx).2).1
  have hb := lemma61_complex_transport (s := s) (w := w) (c := c)
    (B := Real.exp (222 * Real.pi)) (K := 35 * lemma23PaperL D ^ (-68 : ℤ))
    (A := 8 * Real.pi) (Real.exp_nonneg _) (by positivity) (by positivity) ha
    (fun x hx => lemma23DirichletZ_differentiableAt_of_im_ne_zero ψ (ht x hx).ne')
    (fun x hx => lemma23DirichletZ_ne_zero_of_im_pos ψ hψ.2.1 hψ.1.ne_one (ht x hx))
    (fun x hx => lemma61_family_Z_norm_thin ψ hψ hL (hseg x hx).1 (hseg x hx).2)
    (fun x hx => lemma61_family_Z_logDeriv_normalized_wide ψ hψ hL
      (lemma61_thin_real_in_wide hL (hseg x hx).1) (hseg x hx).2)
  have he : ((lemma23PaperP D * lemma51PaperT0 D : ℝ) : ℂ) ^ (-w) = exp (-(c : ℂ) * w) := by
    have hbase : 0 < lemma23PaperP D * lemma51PaperT0 D := mul_pos (Real.exp_pos _) hT
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hbase.ne'),
      ← Complex.ofReal_log hbase.le]
    congr 1
    ring
  rw [he]
  apply hb.trans_eq
  rw [show 238 * Real.pi = 222 * Real.pi + 2 * (8 * Real.pi) by ring,Real.exp_add]
  ring

end ZhangLS.Spec
