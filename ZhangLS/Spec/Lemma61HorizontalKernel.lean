import ZhangLS.Spec.Lemma61LeftApproximation
import ZhangLS.Spec.Lemma56AbelContinuation

/-! # Faithful original Lemma 6.1

Finite short-polynomial Gaussian inversion, actual original-left integral
decomposition and N approximation, actual full horizontal L edges and
uniform constants/thresholds yield lemma61_proved : Lemma61Target.
Original Psi, strict region and actual L/K/N/E1 are retained.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

lemma lemma61_family_modulus_bound {D p : ℕ} (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ) :
    (p : ℝ) ≤ 2 * lemma23PaperP D := by
  have hpow : 1 ≤ lemma23PaperL D ^ 68 := one_le_pow₀ (by linarith)
  have hinv : lemma23PaperL D ^ (-68 : ℤ) ≤ 1 := by
    simp only [zpow_neg,zpow_natCast]
    exact inv_le_one_of_one_le₀ hpow
  have hP : 0 < lemma23PaperP D := Real.exp_pos _
  nlinarith only [hψ.2.2.2.le,mul_le_mul_of_nonneg_left hinv hP.le]

lemma lemma61_shifted_argument_norm_bounds {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {s w : ℂ} (hs : Lemma61InRegion D s)
    (hwr : -1 ≤ w.re ∧ w.re ≤ 2) (hwi : |w.im| ≤ lemma23PaperL D ^ 20) :
    ‖s + w‖ ≤ 16 * lemma23PaperL D ^ 519 ∧
      ‖1 - (s + w)‖ ≤ 17 * lemma23PaperL D ^ 519 := by
  have h1 : 1 ≤ lemma23PaperL D := by linarith
  have hp : 1 ≤ lemma23PaperL D ^ 519 := one_le_pow₀ h1
  have h405 : lemma23PaperL D ^ 405 ≤ lemma23PaperL D ^ 519 :=
    pow_le_pow_right₀ h1 (by norm_num)
  have h9 : 1 ≤ lemma23PaperL D ^ 9 := one_le_pow₀ h1
  have hr := lemma61_region_quarter_bounds hL hs
  have hwide := lemma61_large_shift_rectangle_bounds hL hs
    ⟨by linarith only [hwr.1,h9],hwr.2⟩ hwi
  have hre : |(s + w).re| ≤ 3 := by
    rw [add_re]
    exact abs_le.mpr ⟨by linarith only [hwr.1,hr.1],by linarith only [hwr.2,hr.2]⟩
  have hc : |(lemma23PaperCenter D).im| ≤ 8 * lemma23PaperL D ^ 519 := by
    simp only [lemma23PaperCenter,add_im,ofReal_im,zero_add,mul_im,I_re,I_im,
      ofReal_re,mul_zero,mul_one,zero_mul,add_zero]
    rw [abs_of_nonneg (by positivity)]
    nlinarith only [Real.pi_le_four,pow_nonneg (by linarith : 0 ≤ lemma23PaperL D) 519]
  have him : |(s + w).im| ≤ 2 * lemma23PaperL D ^ 405 + 3 + 8 * lemma23PaperL D ^ 519 := by
    have h := abs_add_le ((s + w).im - (lemma23PaperCenter D).im) (lemma23PaperCenter D).im
    rw [sub_add_cancel] at h
    linarith only [h,hwide.2.1,hc]
  have hn : ‖s + w‖ ≤ 16 * lemma23PaperL D ^ 519 := by
    have h := Complex.norm_le_abs_re_add_abs_im (s + w)
    linarith only [h,hre,him,h405,hp]
  refine ⟨hn,?_⟩
  have h := norm_sub_le (1 : ℂ) (s + w)
  norm_num only [norm_one] at h
  linarith only [h,hn,hp]

lemma lemma61_actual_L_quarter_plane_bound {p : ℕ} [NeZero p]
    (ψ : DirichletCharacter ℂ p) (hψ : ψ ≠ 1) {z : ℂ} (hz : 1 / 4 ≤ z.re) :
    ‖DirichletCharacter.LFunction ψ z‖ ≤ 4 * (p : ℝ) * ‖z‖ := by
  have hpos : 0 < z.re := by linarith
  have h := lemma56_actual_LFunction_bound_re_pos ψ hψ hpos
  have hd : (p : ℝ) / z.re ≤ 4 * (p : ℝ) := by
    apply (div_le_iff₀ hpos).mpr
    nlinarith only [mul_le_mul_of_nonneg_left hz (by positivity : 0 ≤ (p : ℝ))]
  exact h.trans ((mul_le_mul_of_nonneg_left hd (norm_nonneg _)).trans_eq (by ring))

lemma lemma61_P4_exponential_rectangle_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {w : ℂ} (hw : w.re ≤ 2) :
    ‖exp (w * (Real.log (lemma61PaperP4 D) : ℂ))‖ ≤ Real.exp (4 * lemma23PaperL D ^ 9) := by
  rw [norm_exp,mul_re]
  simp only [ofReal_re,ofReal_im,mul_zero,sub_zero]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_right hw (lemma61_P4_log_nonneg hL)
  linarith only [h,lemma61_P4_log_bound hL]

lemma lemma61_T_left_rectangle_exponential_bound {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {w : ℂ} (hw : -1 ≤ w.re) :
    Real.exp (-2 * w.re * Real.log (lemma56PaperT D)) ≤ Real.exp (2 * lemma23PaperL D ^ 9) := by
  apply Real.exp_le_exp.mpr
  have ht := lemma61_T_log_bounds hL
  have hn : 0 ≤ Real.log (lemma56PaperT D) := by linarith only [hL,ht.1]
  have h := mul_le_mul_of_nonneg_right hw hn
  linarith only [h,ht.2]

end ZhangLS.Spec
