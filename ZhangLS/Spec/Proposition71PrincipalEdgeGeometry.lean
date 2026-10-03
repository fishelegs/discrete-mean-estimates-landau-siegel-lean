import ZhangLS.Spec.Proposition71PrincipalShortGeometry
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Set
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_short_rectangle_real_bounds {D : ℕ} (hL : 2000≤lemma23PaperL D)
    {s : ℂ} (hs : s.re∈Icc (1-1/lemma23PaperL D) (1+lemma44PaperAlpha D)) :
    1/2≤s.re ∧ s.re≤2 := by
  have hi : 1/lemma23PaperL D≤1/2000 := one_div_le_one_div_of_le (by norm_num) hL
  have ha := (proposition71_zeta_paper_alpha_budget (by linarith : 3≤lemma23PaperL D)).2.1
  constructor <;> linarith [hs.1,hs.2]

lemma proposition71_short_rectangle_width {D : ℕ} (hL : 2000≤lemma23PaperL D) :
    |(1+lemma44PaperAlpha D)-(1-1/lemma23PaperL D)|≤1 := by
  have hi : 1/lemma23PaperL D≤1/2000 := one_div_le_one_div_of_le (by norm_num) hL
  have ha := proposition71_zeta_paper_alpha_budget (by linarith : 3≤lemma23PaperL D)
  have hlogpos : 0<lemma23PaperL D := by linarith
  have hLp : 0<1/lemma23PaperL D := by positivity
  rw [abs_of_nonneg (by linarith [ha.1])]
  linarith [ha.2.1]

lemma proposition71_principal_left_pole_separation {D : ℕ} (hL : 2000≤lemma23PaperL D)
    (c : ℝ) {s : ℂ} (hs : s.re=1-1/lemma23PaperL D) (j : Fin 3) :
    s≠1 ∧ 1/lemma23PaperL D≤‖s+lemma83PaperBeta D c j-1‖ := by
  have hLp : 0<lemma23PaperL D := by linarith
  have hi : 0<1/lemma23PaperL D := by positivity
  constructor
  · intro he
    have hre := congrArg Complex.re he
    rw [hs] at hre
    simp only [one_re] at hre
    linarith
  · have hr : (s+lemma83PaperBeta D c j-1).re= -1/lemma23PaperL D := by
      simp only [sub_re,add_re,one_re,lemma83_beta_re,add_zero,hs]
      ring
    have he := Complex.abs_re_le_norm (s+lemma83PaperBeta D c j-1)
    rw [hr,neg_div,abs_neg,abs_of_pos hi] at he
    exact he

lemma proposition71_principal_horizontal_pole_separation {D : ℕ}
    (hL : 2000≤lemma23PaperL D) {c : ℝ} (hc : 0<c)
    (hsmall : c*lemma44PaperAlpha D*lemma23PaperL D≤1/10)
    {s : ℂ} (hs : |s.im|=proposition71ZetaAuxHeight D/2) (j : Fin 3) :
    s≠1 ∧ 1/lemma23PaperL D≤‖s+lemma83PaperBeta D c j-1‖ := by
  have hm := proposition71_short_height_beta_margin hL hc hsmall
  have hH := proposition71_zeta_aux_height_pos D
  have hi : 1/lemma23PaperL D≤1/2000 := one_div_le_one_div_of_le (by norm_num) hL
  have hb := (Complex.abs_im_le_norm (lemma83PaperBeta D c j)).trans (hm.2 j)
  constructor
  · intro he
    rw [he,one_im,abs_zero] at hs
    linarith
  · have ha : |s.im|≤|(s+lemma83PaperBeta D c j-1).im|+|(lemma83PaperBeta D c j).im| := by
      have hh := norm_sub_le (s+lemma83PaperBeta D c j-1).im (lemma83PaperBeta D c j).im
      simpa only [Real.norm_eq_abs,sub_im,add_im,one_im,sub_zero,add_sub_cancel_right] using hh
    have hn := Complex.abs_im_le_norm (s+lemma83PaperBeta D c j-1)
    rw [hs] at ha
    linarith [hm.1]

end ZhangLS.Spec
