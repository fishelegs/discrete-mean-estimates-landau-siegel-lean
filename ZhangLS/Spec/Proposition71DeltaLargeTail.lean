import ZhangLS.Spec.Lemma53
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # A genuine exponentially small, integrable large-x envelope for Δ

This is deduced from the actual two-term Lemma5.3 bound for every
x>t₀^(51/50). No tail cancellation or localization statement is assumed.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
set_option maxHeartbeats 2000000

lemma proposition71_large_log_exponent {L x : ℝ} (hL : 2000≤L) (hx : L^500≤x) :
    L^10/2+2*Real.log x≤(L^400*Real.log x/100)^2 := by
  have hL1 : 1≤L := by linarith
  have hLp : 0<L := by linarith
  have hx4 : 4≤x := by
    have hh := pow_le_pow_right₀ hL1 (by norm_num : 1≤(500:ℕ))
    simp only [pow_one] at hh
    linarith
  have hy : 1≤Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ)<4) hx4
    have he : Real.log (4 : ℝ)=2*Real.log 2 := by
      rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
    rw [he] at hh
    linarith [Real.log_two_gt_d9]
  have h790 : 10000≤L^790 := by
    have hh := pow_le_pow_right₀ hL1 (by norm_num : 2≤(790:ℕ))
    nlinarith only [hL,hh]
  have h800 : 40000≤L^800 := by
    have hh := pow_le_pow_right₀ hL1 (by norm_num : 2≤(800:ℕ))
    nlinarith only [hL,hh]
  let A : ℝ := L^800/10000
  have hA10 : L^10≤A := by
    have hh := mul_le_mul_of_nonneg_left h790 (pow_nonneg hLp.le 10)
    rw [←pow_add] at hh
    norm_num only at hh
    dsimp [A]
    nlinarith only [hh]
  have hA4 : 4≤A := by dsimp [A]; linarith only [h800]
  have hy2 : 1≤(Real.log x)^2 := one_le_pow₀ hy
  have hyy : Real.log x≤(Real.log x)^2 := by nlinarith only [hy]
  have hE1 : L^10≤A*(Real.log x)^2 := by
    calc
      _≤L^10*(Real.log x)^2 := le_mul_of_one_le_right (pow_nonneg hLp.le 10) hy2
      _≤_ := mul_le_mul_of_nonneg_right hA10 (sq_nonneg _)
  have hE2 : 4*Real.log x≤A*(Real.log x)^2 := by
    calc
      _≤4*(Real.log x)^2 := by linarith only [hyy]
      _≤_ := mul_le_mul_of_nonneg_right hA4 (sq_nonneg _)
  have he : A*(Real.log x)^2=(L^400*Real.log x/100)^2 := by dsimp [A]; ring
  rw [he] at hE1 hE2
  linarith only [hE1,hE2]

lemma proposition71_large_power_exponent {L x : ℝ} (hL : 2000≤L) (hx : L^500≤x) :
    L^10/2+2*Real.log x≤x^(99/100 : ℝ)/L^400 := by
  have hL1 : 1≤L := by linarith
  have hLp : 0<L := by linarith
  have hxp : 0<x := (pow_pos hLp 500).trans_le hx
  have h495 : L^495≤x^(99/100 : ℝ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hLp.le 500) hx (by norm_num : (0:ℝ)≤99/100)
    rw [←Real.rpow_natCast L 500,←Real.rpow_mul hLp.le] at hh
    norm_num only [show (500 : ℝ)*(99/100)=495 by norm_num,Real.rpow_natCast,Real.rpow_ofNat] at hh
    exact hh
  have hE1 : L^10≤x^(99/100 : ℝ)/L^400 := by
    apply (le_div_iff₀ (pow_pos hLp 400)).mpr
    rw [←pow_add]
    exact (pow_le_pow_right₀ hL1 (by norm_num : 410≤(495:ℕ))).trans h495
  have h445 : L^445≤x^(89/100 : ℝ) := by
    have hh := Real.rpow_le_rpow (pow_nonneg hLp.le 500) hx (by norm_num : (0:ℝ)≤89/100)
    rw [←Real.rpow_natCast L 500,←Real.rpow_mul hLp.le] at hh
    norm_num only [show (500 : ℝ)*(89/100)=445 by norm_num,Real.rpow_natCast,Real.rpow_ofNat] at hh
    exact hh
  have h45 : 40≤L^45 := by
    have hh := pow_le_pow_right₀ hL1 (by norm_num : 1≤(45:ℕ))
    simp only [pow_one] at hh
    linarith only [hh,hL]
  have hfactor : 40*L^400≤x^(89/100 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right h45 (pow_nonneg hLp.le 400)
    rw [←pow_add] at hh
    exact hh.trans h445
  have hlog : Real.log x≤10*x^(1/10 : ℝ) := by
    have hh := Real.log_le_rpow_div hxp.le (by norm_num : (0:ℝ)<1/10)
    convert hh using 1 <;> ring
  have hprod : 40*L^400*x^(1/10 : ℝ)≤x^(99/100 : ℝ) := by
    have hh := mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hxp.le (1/10 : ℝ))
    rw [←Real.rpow_add hxp] at hh
    norm_num only [show (89/100 : ℝ)+1/10=99/100 by norm_num] at hh
    exact hh
  have hE2 : 4*Real.log x≤x^(99/100 : ℝ)/L^400 := by
    apply (le_div_iff₀ (pow_pos hLp 400)).mpr
    have hh := mul_le_mul_of_nonneg_right hlog (pow_nonneg hLp.le 400)
    nlinarith only [hh,hprod]
  linarith only [hE1,hE2]

lemma proposition71_tail_exp_factor {L x : ℝ} (hx : 0<x) :
    Real.exp (-(L^10/2+2*Real.log x))=
      Real.exp (-L^10/2)*x^(-2 : ℝ) := by
  rw [Real.rpow_def_of_pos hx,←Real.exp_add]
  congr 1
  ring

noncomputable def proposition71LargeDeltaTailConstant : ℝ :=
  2+Real.exp 1+Real.sqrt Real.pi*Real.exp 2

lemma proposition71_large_delta_tail_constant_pos : 0<proposition71LargeDeltaTailConstant := by
  unfold proposition71LargeDeltaTailConstant
  positivity

/-- A genuine integrable large-x envelope for the original Δ. -/
theorem proposition71_actual_large_delta_tail {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {x : ℝ}
    (hxhi : lemma51PaperT0 D^(51/50 : ℝ)<x) :
    ‖lemma53PaperDelta D x‖≤proposition71LargeDeltaTailConstant*
      Real.exp (-lemma23PaperL D^10/2)*x^(-2 : ℝ) := by
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hLp : 0<lemma23PaperL D := by linarith
  have h500 : lemma23PaperL D^500≤lemma51PaperT0 D^(51/50 : ℝ) := by
    unfold lemma51PaperT0
    rw [←Real.rpow_natCast (lemma23PaperL D) 519,←Real.rpow_mul hLp.le,
      ←Real.rpow_natCast (lemma23PaperL D) 500]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
  have hx500 := h500.trans hxhi.le
  have hx : 0<x := (pow_pos hLp 500).trans_le hx500
  have he1 : Real.exp (-((lemma53PaperScale D*Real.log x/100)^2))≤
      Real.exp (-lemma23PaperL D^10/2)*x^(-2 : ℝ) := by
    exact (Real.exp_le_exp.mpr (neg_le_neg (proposition71_large_log_exponent hL hx500))).trans_eq
      (proposition71_tail_exp_factor hx)
  have he2 : Real.exp (-(x^(99/100 : ℝ))/lemma53PaperScale D)≤
      Real.exp (-lemma23PaperL D^10/2)*x^(-2 : ℝ) := by
    rw [lemma53PaperScale,neg_div]
    exact (Real.exp_le_exp.mpr (neg_le_neg (proposition71_large_power_exponent hL hx500))).trans_eq
      (proposition71_tail_exp_factor hx)
  apply (lemma53_large_range_estimate hD hL hx hxhi).trans
  calc
    _≤(2+Real.exp 1)*(Real.exp (-lemma23PaperL D^10/2)*x^(-2 : ℝ))+
      (Real.sqrt Real.pi*Real.exp 2)*(Real.exp (-lemma23PaperL D^10/2)*x^(-2 : ℝ)) := by
      exact add_le_add (mul_le_mul_of_nonneg_left he1 (by positivity))
        (mul_le_mul_of_nonneg_left he2 (by positivity))
    _=_ := by unfold proposition71LargeDeltaTailConstant; ring

end ZhangLS.Spec
