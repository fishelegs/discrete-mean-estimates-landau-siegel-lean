import ZhangLS.Spec.Lemma84BoundaryHarmonic
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
set_option maxHeartbeats 2000000

/-- The displayed G is bounded uniformly on the entire positive x<P range,
including x=1. The smoothing denominator is bounded below explicitly. -/
theorem lemma84_boundary_g_main_bound {D : ℕ} {c : ℝ}
    (hL : 100≤lemma23PaperL D) (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    (j : Fin 3) (μ : ℕ) {x : ℝ} (hx : 1≤x) (hxP : x<lemma23PaperP D) :
    ‖lemma84MainTerm D c j μ x‖≤33+49*Real.pi := by
  let α := lemma44PaperAlpha D
  let a := lemma83PaperBeta D c (j+1)
  let b := lemma83PaperBeta D c (j+2)
  let m := lemma84SmoothingBeta D μ
  have hα : 0<α := (lemma83_alpha_small hL).1
  have hab := lemma83_paper_beta_norm (by linarith : 3≤lemma23PaperL D) hc hsmall
  have ha : ‖a‖≤4*α := by dsimp [a,α]; linarith [hab (j+1)]
  have hb : ‖b‖≤4*α := by dsimp [b,α]; linarith [hab (j+2)]
  have hm := lemma84_smoothing_beta_norm μ hα
  have hmlo : α≤‖m‖ := by
    dsimp [m]
    unfold lemma84SmoothingBeta
    have hapos : 0< lemma44PaperAlpha D := hα
    split_ifs <;>
      norm_num [norm_div,norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hapos] <;>
      dsimp [α] <;> linarith
  have hmhi : ‖m‖≤3*α := hm.2
  have hmp : 0<‖m‖ := hα.trans_le hmlo
  have hxp : 0<x := by linarith
  have hlx : 0≤Real.log x := Real.log_nonneg hx
  have hscale : α*Real.log x≤Real.pi := by
    have hh := Real.log_lt_log hxp hxP
    rw [lemma23PaperP,Real.log_exp] at hh
    have hLp : 0< lemma23PaperL D := by linarith
    have he : α*lemma23PaperL D^9=Real.pi := by
      dsimp [α]
      rw [lemma44PaperAlpha,lemma23PaperP,Real.log_exp,div_mul_cancel₀ _ (pow_ne_zero _ hLp.ne')]
    nlinarith only [mul_le_mul_of_nonneg_left hh.le hα.le,he]
  have hratio : ‖a*b/m^2‖≤16 := by
    rw [norm_div,norm_mul,norm_pow]
    apply (div_le_iff₀ (pow_pos hmp 2)).mpr
    have hh := mul_le_mul ha hb (norm_nonneg _) (by positivity)
    nlinarith [sq_nonneg (‖m‖-α)]
  have hdiffa : ‖a-m‖≤7*α := (norm_sub_le _ _).trans (by linarith)
  have hdiffb : ‖b-m‖≤7*α := (norm_sub_le _ _).trans (by linarith)
  have hsecond : ‖(a-m)*(b-m)/m‖≤49*α := by
    rw [norm_div,norm_mul]
    apply (div_le_iff₀ hmp).mpr
    have hh := mul_le_mul hdiffa hdiffb (norm_nonneg _) (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hmlo hα.le]
  have hpower : ‖(x:ℂ)^(-m)‖=1 := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxp]
    simp only [m,Complex.neg_re,lemma84_smoothing_beta_re,neg_zero,Real.rpow_zero]
  change ‖a*b/m^2+(1-a*b/m^2-(a-m)*(b-m)/m*(Real.log x:ℂ))*(x:ℂ)^(-m)‖≤_
  apply (norm_add_le _ _).trans
  rw [norm_mul,hpower,mul_one]
  have hmiddle := norm_sub_le (1-a*b/m^2) ((a-m)*(b-m)/m*(Real.log x:ℂ))
  rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hlx] at hmiddle
  have hfirst := norm_sub_le (1:ℂ) (a*b/m^2)
  rw [norm_one] at hfirst
  have hh := mul_le_mul_of_nonneg_right hsecond hlx
  nlinarith only [hfirst,hmiddle,hratio,hh,hscale]

end ZhangLS.Spec
