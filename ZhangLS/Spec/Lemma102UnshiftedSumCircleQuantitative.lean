import ZhangLS.Spec.Lemma102CircleObjects
import ZhangLS.Spec.Lemma102UnshiftedActualBoundaryBounds
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
set_option maxHeartbeats 2000000

lemma lemma102_paper_left_exponential {D : ℕ} (hL : 0 < lemma23PaperL D)
    {x : ℝ} (hxT : lemma56PaperT D ≤ x) :
    Real.exp (-Real.log x/lemma23PaperL D) ≤
      Real.exp (-(lemma23PaperL D^(1/10:ℝ))) := by
  have hT : 0 < lemma56PaperT D := by unfold lemma56PaperT; positivity
  have hxlog := Real.log_le_log hT hxT
  unfold lemma56PaperT at hxlog
  rw [Real.log_exp] at hxlog
  have he : lemma23PaperL D^(11/10:ℝ)/lemma23PaperL D = lemma23PaperL D^(1/10:ℝ) := by
    simpa only [show (11/10:ℝ)-1 = 1/10 by norm_num,Real.rpow_one] using
      (Real.rpow_sub hL (11/10) 1).symm
  apply Real.exp_le_exp.mpr
  have hh := div_le_div_of_nonneg_right hxlog hL.le
  change lemma23PaperL D^(11/10:ℝ)/lemma23PaperL D ≤ Real.log x/lemma23PaperL D at hh
  rw [he] at hh
  rw [neg_div]
  linarith only [hh]


/-- Actual quantitative Perron-to-circle transfer, before asymptotic absorption.
All five boundary pieces have been integrated with their true kernels. -/
lemma lemma102_unshifted_actual_sum_circle_quantitative {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D) {ρ : ℝ}
    (hρ : 0 < 1-ρ) (hclose : 1-ρ ≤ 64*lemma23PaperL D^(-2022 : ℤ))
    (hzero : dirichletLFunction χ (ρ:ℂ)=0) (hsimple : deriv (dirichletLFunction χ) (ρ:ℂ) ≠ 0)
    (hunique : ∀ z : ℂ, Lemma55InZeroRegion D z → dirichletLFunction χ z=0 → z=(ρ:ℂ))
    (c : ℝ) (j : Fin 3) (d r : ℕ) (hd : 0 < d) (hr : 0 < r)
    {x M : ℝ} (hxT : lemma56PaperT D ≤ x) (hxP : x < lemma23PaperP D) (hM : 0 ≤ M)
    (hnum : ∀ s : ℂ, Lemma102UnshiftedContourPoint D s → ‖lemma102_unshiftedContourNumerator χ c j d r s‖ ≤ M) :
    ‖lemma102LogSum χ c j d r x-lemma102PaperCircle χ c j d r x‖ ≤
      M*Real.pi*lemma23PaperL D*Real.exp (-(lemma23PaperL D^(1/10:ℝ))) +
      8*M*Real.exp (6*Real.pi)*(6*lemma44PaperAlpha D+1/lemma23PaperL D)/(D:ℝ)^2 +
      8*lemma102_unshiftedRightLineMajorant (6*lemma44PaperAlpha D) d r*Real.exp (6*Real.pi)/(D:ℝ) := by
  have hLp : 0 < lemma23PaperL D := by linarith
  have hT : 1 ≤ lemma56PaperT D := by unfold lemma56PaperT; exact Real.one_le_exp_iff.mpr (Real.rpow_nonneg hLp.le _)
  have hx : 1 ≤ x := hT.trans hxT
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hDpos : (1:ℝ) < D := by exact_mod_cast hD
  have hα := lemma83_alpha_small (by linarith only [hL] : 100 ≤ lemma23PaperL D)
  have hb : 0 < 6*lemma44PaperAlpha D := by positivity [hα.1]
  have hm := lemma102_zero_shift_norm hα.1
  have hmi : |((0:ℂ)).im| ≤ (D:ℝ)/2 := by
    have hh := (Complex.abs_im_le_norm _).trans hm.2
    linarith only [hh,hα.2,hDpos]
  have hleft := lemma102_unshifted_actual_left_bound χ hLp c j d r hxp hM hnum
  have he := mul_le_mul_of_nonneg_left (lemma102_paper_left_exponential hLp hxT)
    (show 0 ≤ M*Real.pi*lemma23PaperL D by positivity)
  have hleft' : ‖∫ t : ℝ in -(D:ℝ)..D, lemma102_unshiftedPaperIntegrand χ c j d r x
      ((-1/lemma23PaperL D:ℝ)+I*(t:ℂ))‖ ≤
        M*Real.pi*lemma23PaperL D*Real.exp (-(lemma23PaperL D^(1/10:ℝ))) := by
    apply hleft.trans
    nlinarith only [he]
  have hhor := lemma102_unshifted_actual_horizontal_bounds χ hD hL c j d r hx hxP hM hnum
  have htail := lemma102_unshifted_actual_right_tails χ hD c j d r hb hxp (by linarith only [hDpos]) hmi
  dsimp only at htail
  have hscale : (6*lemma44PaperAlpha D)*Real.log x ≤ 6*Real.pi := by
    have hh := lemma102_unshifted_alpha_log_x_le_pi hLp hxp hxP
    linarith only [hh]
  have hMR := lemma102_unshifted_right_line_majorant_nonneg hb d r
  have hbound := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hscale)
      (show 0 ≤ 8*lemma102_unshiftedRightLineMajorant (6*lemma44PaperAlpha D) d r by positivity))
    (show 0 ≤ (D:ℝ) by positivity)
  have htail' := htail.trans hbound
  have hmain := lemma102_unshifted_actual_sum_circle_boundary_error χ hD hL hρ hclose hzero hsimple hunique c j d r hd hr hxp
  dsimp only at hmain
  change _ ≤ _ at hmain
  change _ ≤ _ at htail'
  simp only [lemma102_unshiftedPaperIntegrand] at hleft' hhor
  have htail'' : _ ≤ 8*lemma102_unshiftedRightLineMajorant (6*lemma44PaperAlpha D) d r*Real.exp (6*Real.pi)/(D:ℝ) :=
    htail'.trans_eq (by ring)
  linarith only [hmain,hleft',hhor,htail'']

end ZhangLS.Spec
