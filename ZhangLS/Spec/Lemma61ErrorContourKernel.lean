import ZhangLS.Spec.Lemma61ComplexZShift

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

noncomputable def lemma61ErrorContourShift (s : ℂ) (v : ℝ) : ℂ :=
  ((1 - 2 * s.re : ℝ) : ℂ) + I * (v : ℂ)

lemma lemma61_short_polynomial_conjugation {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma61ShortPolynomial D ψ⁻¹ (conj s) = conj (lemma61ShortPolynomial D ψ s) := by
  unfold lemma61ShortPolynomial
  simp only [map_sum,map_mul,← Complex.exp_conj,map_neg,Complex.conj_ofReal]
  apply Finset.sum_congr rfl
  intro n hn
  congr 1
  exact (MulChar.star_apply' ψ (n : ZMod p)).symm

lemma lemma61_error_contour_reflection (s : ℂ) (v : ℝ) :
    1 - s - lemma61ErrorContourShift s v = conj (s + I * (v : ℂ)) := by
  apply Complex.ext <;> simp [lemma61ErrorContourShift,mul_re,mul_im] <;> ring

lemma lemma61_error_contour_bounds {D : ℕ} {s : ℂ} {v : ℝ}
    (hs : Lemma61InRegion D s) (hv : |v| ≤ lemma23PaperL D ^ 20) :
    |(lemma61ErrorContourShift s v).re| ≤ 4 * lemma44PaperAlpha D ∧
      |(lemma61ErrorContourShift s v).im| ≤ lemma23PaperL D ^ 20 := by
  have he : 1 - 2 * s.re = -2 * (s.re - 1 / 2) := by ring
  simp only [lemma61ErrorContourShift,add_re,ofReal_re,mul_re,I_re,ofReal_im,
    mul_zero,I_im,zero_mul,sub_zero,add_zero,add_im,mul_im,one_mul,zero_add]
  refine ⟨?_,hv⟩
  rw [he,abs_mul]
  norm_num
  linarith only [hs.1]

lemma lemma61_error_contour_short_norm {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (s : ℂ) (v : ℝ) :
    ‖lemma61ShortPolynomial D ψ⁻¹ (1 - s - lemma61ErrorContourShift s v)‖ =
      ‖lemma61ShortPolynomial D ψ (s + I * (v : ℂ))‖ := by
  rw [lemma61_error_contour_reflection,lemma61_short_polynomial_conjugation,Complex.norm_conj]

lemma lemma61_P4_log_nonneg {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    0 ≤ Real.log (lemma61PaperP4 D) := by
  let L := lemma23PaperL D
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have h7 : (3 : ℝ) ^ 7 ≤ L ^ 7 := pow_le_pow_left₀ (by norm_num) hL 7
  have h2 : 2 * L ^ 2 ≤ L ^ 9 := by
    calc
      2 * L ^ 2 ≤ L ^ 7 * L ^ 2 := by norm_num at h7; nlinarith only [h7,sq_nonneg L]
      _ = L ^ 9 := by ring
  have hb : L ^ (11 / 10 : ℝ) ≤ L ^ 2 := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hL1
      (by norm_num : (11 / 10 : ℝ) ≤ (2 : ℕ))
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  have ht0 : 0 < lemma51PaperT0 D := pow_pos hL0 519
  have he : Real.log (lemma61PaperP4 D) =
      L ^ 9 - 2 * L ^ (11 / 10 : ℝ) + 519 * Real.log L := by
    rw [lemma61PaperP4,Real.log_mul (mul_ne_zero hP.ne' (zpow_ne_zero _ hT.ne')) ht0.ne',
      Real.log_mul hP.ne' (zpow_ne_zero _ hT.ne'),Real.log_zpow,
      lemma23PaperP,lemma56PaperT,Real.log_exp,Real.log_exp,lemma51PaperT0,Real.log_pow]
    norm_num
    rfl
  rw [he]
  have hlog : 0 ≤ Real.log L := Real.log_nonneg hL1
  nlinarith only [h2,hb,hlog]

lemma lemma61_P4_exponential_thin_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {w : ℂ} (hw : |w.re| ≤ 4 * lemma44PaperAlpha D) :
    ‖exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ ≤ Real.exp (8 * Real.pi) := by
  rw [norm_exp]
  simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
  apply Real.exp_le_exp.mpr
  have hc0 := lemma61_P4_log_nonneg hL
  have hc := lemma61_P4_log_bound hL
  have ha : 0 ≤ lemma44PaperAlpha D := (lemma44_alpha_pos_le_one hL).1.le
  have he : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
    simp only [lemma44PaperAlpha,lemma23PaperP,Real.log_exp]
    field_simp
  calc
    _ ≤ |w.re| * Real.log (lemma61PaperP4 D) := mul_le_mul_of_nonneg_right (le_abs_self _) hc0
    _ ≤ (4 * lemma44PaperAlpha D) * (2 * lemma23PaperL D ^ 9) :=
      mul_le_mul hw hc hc0 (by positivity)
    _ = _ := by nlinarith only [he]

lemma lemma61_omega_one_thin_gaussian_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {w : ℂ} (hw : |w.re| ≤ 4 * lemma44PaperAlpha D) :
    ‖lemma57OmegaOne D w‖ ≤ Real.exp 1 *
      Real.exp (-(w.im ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have hL0 : 0 < lemma23PaperL D := by linarith
  have ha := lemma61_six_alpha_le_quarter hL
  have hwr : |w.re| ≤ 1 := by linarith only [ha,hw]
  have hws : w.re ^ 2 ≤ 1 := by nlinarith only [sq_abs w.re,hwr,abs_nonneg w.re]
  have hden : 1 ≤ 4 * lemma23PaperL D ^ 30 := by nlinarith only [one_le_pow₀ (n := 30) hL1]
  have hdiv : w.re ^ 2 / (4 * lemma23PaperL D ^ 30) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : 0 < 4 * lemma23PaperL D ^ 30)).mpr
    linarith only [hws,hden]
  have he : ‖lemma57OmegaOne D w‖ = Real.exp
      (w.re ^ 2 / (4 * lemma23PaperL D ^ 30) - w.im ^ 2 / (4 * lemma23PaperL D ^ 30)) := by
    unfold lemma57OmegaOne
    have hdc : (4 : ℂ) * (Real.log (D : ℝ) : ℂ) ^ 30 =
        ((4 * lemma23PaperL D ^ 30 : ℝ) : ℂ) := by
      unfold lemma23PaperL
      push_cast
      rfl
    rw [hdc,norm_exp,Complex.div_ofReal_re]
    congr 1
    simp only [pow_two,Complex.mul_re]
    ring
  rw [he,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  rw [neg_div]
  linarith only [hdiv]

end ZhangLS.Spec
