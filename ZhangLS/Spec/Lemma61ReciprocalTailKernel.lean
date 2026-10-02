import ZhangLS.Spec.Lemma61ErrorContourKernel
import ZhangLS.Spec.Lemma44GaussianVerticalTail
import ZhangLS.Spec.Lemma61RightTruncation
import ZhangLS.Spec.Lemma61SingleResidue
import ZhangLS.Spec.Lemma44LocalRectangle

/-! # Actual reciprocal tail truncation for Lemma 6.1

The original n<T^3 finite sum and its n>=T^3 tail are split exactly.
Actual Gamma conductor growth cancels with actual P4, uniformly on the
wide high rectangle. Far-left and both horizontal tail integrals, the
actual local Cauchy relation and the original-left tail error are proved.
The full Lemma61Target remains unproved: finite polynomial error-line
shift, full horizontal edges and final constants/thresholds remain.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_region_quarter_bounds {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma61InRegion D s) : 1 / 4 < s.re ∧ s.re < 3 / 4 := by
  have ha := lemma61_six_alpha_le_quarter hL
  have hp := (lemma44_alpha_pos_le_one hL).1.le
  have hr := abs_lt.mp hs.1
  constructor <;> linarith only [ha,hp,hr.1,hr.2]

lemma lemma61_large_shift_rectangle_bounds {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {s w : ℂ} (hs : Lemma61InRegion D s)
    (hwre : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2)
    (hwim : |w.im| ≤ lemma23PaperL D ^ 20) :
    |(s + w).re| ≤ 2 * lemma23PaperL D ^ 9 ∧
      |(s + w).im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3 ∧
      |(s + w).re - 1 / 2| ≤ 3 * lemma23PaperL D ^ 9 := by
  have hr := lemma61_region_real_parts hL hs
  have h9 : 3 ≤ lemma23PaperL D ^ 9 := hL.trans (le_self_pow₀ (by linarith) (by norm_num))
  have h20 : lemma23PaperL D ^ 20 ≤ lemma23PaperL D ^ 405 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hreal : |(s + w).re| ≤ 2 * lemma23PaperL D ^ 9 := by
    rw [add_re]
    exact abs_le.mpr ⟨by linarith only [hr.1,hwre.1,h9],by linarith only [hr.2,hwre.2,h9]⟩
  refine ⟨hreal,?_,?_⟩
  · have he : (s + w).im - (lemma23PaperCenter D).im =
      (s.im - (lemma23PaperCenter D).im) + w.im := by simp; ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith only [hs.2,hwim,h20])
  · have hre := hreal
    simp only [add_re] at hre
    exact (abs_sub _ _).trans (by norm_num; linarith only [hre,h9])

lemma lemma61_wide_log_modulus_error_le_one {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {a : ℝ} (ha : |a| ≤ 3 * lemma23PaperL D ^ 9) :
    35 * lemma23PaperL D ^ (-68 : ℤ) * |a| ≤ 1 := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h5 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 5
  have h59 := pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num : 5 ≤ 59)
  have hpow : 105 ≤ lemma23PaperL D ^ 59 := by norm_num at h5; linarith only [h5,h59]
  calc
    _ ≤ 35 * lemma23PaperL D ^ (-68 : ℤ) * (3 * lemma23PaperL D ^ 9) :=
      mul_le_mul_of_nonneg_left ha (by positivity)
    _ = 105 / lemma23PaperL D ^ 59 := by
      simp only [zpow_neg,zpow_natCast]
      field_simp <;> norm_num
    _ ≤ 1 := (div_le_one (pow_pos h0 59)).mpr hpow

lemma lemma61_P4_PT0_log_identity {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    Real.log (lemma61PaperP4 D) =
      Real.log (lemma23PaperP D * lemma51PaperT0 D) - 2 * Real.log (lemma56PaperT D) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  have hT : 0 < lemma56PaperT D := Real.exp_pos _
  have hT0 : 0 < lemma51PaperT0 D := pow_pos h0 519
  unfold lemma61PaperP4
  rw [Real.log_mul (mul_ne_zero hP.ne' (zpow_ne_zero _ hT.ne')) hT0.ne',
    Real.log_mul hP.ne' (zpow_ne_zero _ hT.ne'),Real.log_zpow,
    Real.log_mul hP.ne' hT0.ne']
  norm_num
  ring

lemma lemma61_actual_Z_P4_cancellation {D p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : Lemma23InPsi (D := D) ψ)
    {s w : ℂ} (hL : 3 ≤ lemma23PaperL D) (hs : Lemma61InRegion D s)
    (hwre : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2)
    (hwim : |w.im| ≤ lemma23PaperL D ^ 20) :
    ‖lemma23DirichletZ ψ (s + w) * exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ ≤
      Real.exp (1 + 4 * Real.pi) * Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) := by
  have hd := lemma61_large_shift_rectangle_bounds hL hs hwre hwim
  have hz := lemma61_family_Z_norm_model_wide ψ hψ hL hd.1 hd.2.1
  have he := lemma61_wide_log_modulus_error_le_one hL hd.2.2
  let c := Real.log (lemma23PaperP D * lemma51PaperT0 D)
  have hc := lemma61_PT0_log_bounds hL
  have ha : |c * (s.re - 1 / 2)| ≤ 4 * Real.pi := by
    rw [abs_mul,abs_of_nonneg hc.1]
    have hh : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
      unfold lemma44PaperAlpha lemma23PaperP
      rw [Real.log_exp]
      field_simp
    calc
      _ ≤ (2 * lemma23PaperL D ^ 9) * (2 * lemma44PaperAlpha D) :=
        mul_le_mul hc.2 hs.1.le (abs_nonneg _) (by positivity)
      _ = _ := by nlinarith only [hh]
  have ha' : -c * (s.re - 1 / 2) ≤ 4 * Real.pi := by
    have h := (neg_le_abs (c * (s.re - 1 / 2))).trans ha
    linarith only [h]
  rw [norm_mul,norm_exp]
  simp only [mul_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
  calc
    _ ≤ Real.exp (-c * ((s + w).re - 1 / 2) +
        35 * lemma23PaperL D ^ (-68 : ℤ) * |(s + w).re - 1 / 2|) *
        Real.exp (w.re * Real.log (lemma61PaperP4 D)) :=
      mul_le_mul_of_nonneg_right hz (Real.exp_nonneg _)
    _ = Real.exp (-c * (s.re - 1 / 2) +
        35 * lemma23PaperL D ^ (-68 : ℤ) * |(s + w).re - 1 / 2| -
        2 * w.re * Real.log (lemma56PaperT D)) := by
      rw [← Real.exp_add]
      congr 1
      rw [lemma61_P4_PT0_log_identity hL]
      dsimp [c]
      ring
    _ ≤ _ := by
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith only [ha',he])

lemma lemma61_large_shift_gaussian_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {w : ℂ} (hwre : -(lemma23PaperL D ^ 9) ≤ w.re ∧ w.re ≤ 2) :
    ‖lemma57OmegaOne D w‖ ≤ Real.exp 1 *
      Real.exp (-(w.im ^ 2) / (4 * lemma23PaperL D ^ 30)) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have h9 : 3 ≤ lemma23PaperL D ^ 9 := hL.trans (le_self_pow₀ (by linarith) (by norm_num))
  have ha : |w.re| ≤ lemma23PaperL D ^ 9 := abs_le.mpr ⟨hwre.1,by linarith only [hwre.2,h9]⟩
  have hsq : w.re ^ 2 ≤ lemma23PaperL D ^ 18 := by
    have hh := mul_self_le_mul_self (abs_nonneg w.re) ha
    nlinarith only [hh,sq_abs w.re]
  have h18 : lemma23PaperL D ^ 18 ≤ lemma23PaperL D ^ 30 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have he : w = (w.re : ℂ) + (w.im : ℂ) * I := by apply Complex.ext <;> simp
  rw [he,lemma44_Omega_norm_vertical,← Real.exp_add]
  apply Real.exp_le_exp.mpr
  simp only [add_im,ofReal_im,mul_im,I_im,ofReal_re,I_re,mul_one,mul_zero,add_zero,zero_add]
  field_simp
  nlinarith only [hsq,h18,pow_pos h0 30]

lemma lemma61_large_shift_denominator_bound {w : ℂ} (hwre : w.re ≤ -1) : ‖w‖⁻¹ ≤ 1 := by
  have hn : 1 ≤ ‖w‖ := by
    have h := Complex.abs_re_le_norm w
    have hl := neg_le_abs w.re
    linarith only [h,hl,hwre]
  exact inv_le_one_of_one_le₀ hn

lemma lemma61_T_log_bounds {D : ℕ} (hL : 3 ≤ lemma23PaperL D) :
    lemma23PaperL D ≤ Real.log (lemma56PaperT D) ∧
      Real.log (lemma56PaperT D) ≤ lemma23PaperL D ^ 9 := by
  unfold lemma56PaperT
  rw [Real.log_exp]
  constructor
  · simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ lemma23PaperL D) (by norm_num : (1 : ℝ) ≤ 11 / 10)
  · simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le
      (by linarith : 1 ≤ lemma23PaperL D) (by norm_num : (11 / 10 : ℝ) ≤ (9 : ℕ))

end ZhangLS.Spec
