import ZhangLS.Spec.Proposition71DeltaLargeTail
import ZhangLS.Spec.Lemma44LongSum
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Genuine off-center localization bounds for the original Δ kernel -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

lemma proposition71_gaussian_clearance_budget {D : ℕ} (hL : 2000≤lemma23PaperL D)
    {x : ℝ} (hx : lemma51PaperT0 D/3≤|x-lemma51PaperT0 D|) :
    lemma23PaperL D^10/2≤
      Real.pi^2*(x-lemma51PaperT0 D)^2/lemma53PaperScale D^2 := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hL1 : 1≤lemma23PaperL D := by linarith
  have hT : 0≤lemma51PaperT0 D := by unfold lemma51PaperT0; positivity
  have hB : 0<lemma53PaperScale D := by unfold lemma53PaperScale; positivity
  have h228 : 5≤lemma23PaperL D^228 := by
    have hh := pow_le_pow_right₀ hL1 (by norm_num : 1≤(228:ℕ))
    simp only [pow_one] at hh
    linarith
  have ht : (9/2 : ℝ)*lemma23PaperL D^10*lemma53PaperScale D^2≤lemma51PaperT0 D^2 := by
    have hh := mul_le_mul_of_nonneg_right h228 (pow_nonneg hLp.le 810)
    rw [←pow_add] at hh
    unfold lemma53PaperScale lemma51PaperT0
    simp only [←pow_mul]
    norm_num only at hh
    have he : lemma23PaperL D^10*lemma23PaperL D^800=lemma23PaperL D^810 := by rw [←pow_add]
    rw [mul_assoc,he]
    nlinarith only [hh,pow_nonneg hLp.le 810]
  have hs := (sq_le_sq₀ (div_nonneg hT (by norm_num) : 0≤lemma51PaperT0 D/3) (abs_nonneg _)).mpr hx
  rw [sq_abs] at hs
  have hp : 1≤Real.pi^2 := by nlinarith [Real.pi_gt_three]
  have hmul := mul_le_mul_of_nonneg_right hp (sq_nonneg (x-lemma51PaperT0 D))
  apply (le_div_iff₀ (pow_pos hB 2)).mpr
  nlinarith only [hs,ht,hmul]

/-- The actual Gaussian center is s₀=1/2+2πit₀. -/
theorem proposition71_actual_gaussian_offcenter {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {x : ℝ}
    (hx : lemma51PaperT0 D/3≤|x-lemma51PaperT0 D|) :
    ‖lemma53PaperOmega D ((1/2 : ℂ)+(2*Real.pi : ℂ)*I*(x : ℂ))‖≤
      Real.sqrt Real.pi*Real.exp (-lemma23PaperL D^10/2) := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hB : 0<lemma53PaperScale D := by unfold lemma53PaperScale; positivity
  have hB1 : 1≤lemma53PaperScale D := one_le_pow₀ (by linarith : 1≤lemma23PaperL D)
  have hs : (1/2 : ℂ)+(2*Real.pi : ℂ)*I*(x : ℂ)=
      (1/2 : ℂ)+((2*Real.pi*x : ℝ) : ℂ)*I := by push_cast; ring
  rw [hs]
  have hform := lemma53_omega_norm_vertical hD (1/2) (2*Real.pi*x)
  norm_num only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] at hform
  rw [hform]
  have hex : ((0 : ℝ)-(2*Real.pi*x-(lemma23PaperCenter D).im)^2)/
      (4*lemma53PaperScale D^2)=
        -(Real.pi^2*(x-lemma51PaperT0 D)^2/lemma53PaperScale D^2) := by
    simp only [lemma23PaperCenter,lemma51PaperT0]
    field_simp
    <;> ring
  rw [hex]
  exact mul_le_mul (div_le_self (Real.sqrt_nonneg _) hB1)
    (Real.exp_le_exp.mpr (by linarith only [proposition71_gaussian_clearance_budget hL hx]))
    (Real.exp_nonneg _) (Real.sqrt_nonneg _)

noncomputable def proposition71OffCenterDeltaConstant : ℝ :=
  2*Real.sqrt Real.pi+lemma53SmallErrorConstant+proposition71LargeDeltaTailConstant

lemma proposition71_offcenter_delta_constant_pos : 0<proposition71OffCenterDeltaConstant := by
  have hC := proposition71_large_delta_tail_constant_pos
  have hS : 0≤lemma53SmallErrorConstant := by unfold lemma53SmallErrorConstant; positivity
  unfold proposition71OffCenterDeltaConstant
  positivity

/-- A true uniform localization envelope for all positive x, including the
large-x branch of Lemma5.3. It is an estimate for Δ itself, not a remainder
defined by subtracting a desired conclusion. -/
theorem proposition71_actual_delta_offcenter {D : ℕ} (hD : 1<D)
    (hL : 2000≤lemma23PaperL D) {x : ℝ} (hx : 0<x)
    (hclear : lemma51PaperT0 D/3≤|x-lemma51PaperT0 D|) :
    ‖lemma53PaperDelta D x‖≤proposition71OffCenterDeltaConstant*
      Real.exp (-lemma23PaperL D^10/2) := by
  have hG := proposition71_actual_gaussian_offcenter hD hL hclear
  have he : 0<Real.exp (-lemma23PaperL D^10/2) := Real.exp_pos _
  have hS : 0≤lemma53SmallErrorConstant := by unfold lemma53SmallErrorConstant; positivity
  have hC := proposition71_large_delta_tail_constant_pos
  by_cases hsmall : x≤lemma51PaperT0 D^(51/50 : ℝ)
  · have ha := (lemma44_alpha_pos_le_one (by linarith : 3≤lemma23PaperL D)).2
    have hδ := lemma53_small_range_estimate hD hL hx hsmall
    have hn := norm_add_le (lemma53PaperDelta D x-
      lemma53PaperOmega D ((1/2 : ℂ)+(2*Real.pi : ℂ)*I*(x : ℂ)))
      (lemma53PaperOmega D ((1/2 : ℂ)+(2*Real.pi : ℂ)*I*(x : ℂ)))
    rw [sub_add_cancel] at hn
    have hα := mul_le_mul_of_nonneg_right ha
      (norm_nonneg (lemma53PaperOmega D ((1/2 : ℂ)+(2*Real.pi : ℂ)*I*(x : ℂ))))
    unfold proposition71OffCenterDeltaConstant
    nlinarith only [hδ,hn,hα,hG,mul_nonneg hC.le he.le]
  · have hhi := lt_of_not_ge hsmall
    have hT : 1≤lemma51PaperT0 D := one_le_pow₀ (by linarith : 1≤lemma23PaperL D)
    have hx1 : 1≤x := (Real.one_le_rpow hT (by norm_num : (0:ℝ)≤51/50)).trans hhi.le
    have hp : x^(-2 : ℝ)≤1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have hb := proposition71_actual_large_delta_tail hD hL hhi
    have hlast := mul_le_mul_of_nonneg_left hp
      (mul_nonneg hC.le he.le)
    apply hb.trans
    apply hlast.trans
    unfold proposition71OffCenterDeltaConstant
    have hg : 0≤2*Real.sqrt Real.pi := by positivity
    nlinarith only [hg,hS,he.le]

end ZhangLS.Spec
