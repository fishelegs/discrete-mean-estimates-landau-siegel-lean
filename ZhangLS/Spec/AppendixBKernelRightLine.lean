import ZhangLS.Spec.AppendixBKernelZetaCircle
import ZhangLS.Spec.Lemma84ContourKernelBounds
import ZhangLS.Spec.Proposition71ZetaRightAnchor

/-! The initial Perron line and both infinite tails are controlled by genuine
absolutely convergent zeta/Möbius series. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Complex MeasureTheory Set

lemma appendixB_integrand_eq_log_kernel {x : ℝ} (hx : 0<x)
    (β γ : ℂ) (hγ : γ.re=0) (b t : ℝ) :
    appendixBZetaIntegrand x β γ ((b : ℂ)+I*(t : ℂ)) =
      (riemannZeta (1+((b : ℂ)+I*(t : ℂ)))/riemannZeta (1+((b : ℂ)+I*(t : ℂ))-β))*
        lemma84LogKernel b (Real.log x) (-γ).im t := by
  unfold appendixBZetaIntegrand
  rw [mul_div_assoc]
  simp only [sub_eq_add_neg]
  rw [lemma84_original_kernel_eq_log hx b (-γ) (by simp [hγ])]

lemma appendixB_right_ratio_bound {b : ℝ} (hb : 0<b) {β : ℂ} (hβ : β.re=0) (t : ℝ) :
    ‖riemannZeta (1+((b : ℂ)+I*(t : ℂ)))/riemannZeta (1+((b : ℂ)+I*(t : ℂ))-β)‖≤(2+1/b)^2 := by
  have h₁ := (proposition71_zeta_right_half_bounds
    (s := 1+((b : ℂ)+I*(t : ℂ))) (by simp; linarith)).1
  have h₂ := (proposition71_zeta_right_half_bounds
    (s := 1+((b : ℂ)+I*(t : ℂ))-β) (by simp [hβ]; linarith)).2
  simp only [add_re,one_re,ofReal_re,mul_re,I_re,ofReal_im,zero_mul,mul_zero,sub_self,
    add_zero,add_sub_cancel_left,sub_re,hβ,sub_zero] at h₁ h₂
  rw [div_eq_mul_inv,norm_mul]
  exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq (by ring)

lemma appendixB_right_line_integrable {b x : ℝ} (hb : 0<b) (hx : 0<x)
    {β γ : ℂ} (hβ : β.re=0) (hγ : γ.re=0) :
    Integrable (fun t : ℝ => appendixBZetaIntegrand x β γ ((b : ℂ)+I*(t : ℂ))) := by
  let q : ℝ → ℂ := fun t => riemannZeta (1+((b : ℂ)+I*(t : ℂ)))/
    riemannZeta (1+((b : ℂ)+I*(t : ℂ))-β)
  have hnum : Continuous (fun t : ℝ => riemannZeta (1+((b : ℂ)+I*(t : ℂ)))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hn : 1+((b : ℂ)+I*(t : ℂ))≠1 := by
      intro h; have h' := congrArg Complex.re h; simp at h'; linarith
    exact (differentiableAt_riemannZeta hn).continuousAt.comp
      (f := fun v : ℝ => 1+((b : ℂ)+I*(v : ℂ))) (by fun_prop)
  have hden : Continuous (fun t : ℝ => riemannZeta (1+((b : ℂ)+I*(t : ℂ))-β)) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hn : 1+((b : ℂ)+I*(t : ℂ))-β≠1 := by
      intro h; have h' := congrArg Complex.re h; simp [hβ] at h'; linarith
    exact (differentiableAt_riemannZeta hn).continuousAt.comp
      (f := fun v : ℝ => 1+((b : ℂ)+I*(v : ℂ))-β) (by fun_prop)
  have hq : Continuous q := hnum.div hden (fun t => riemannZeta_ne_zero_of_one_lt_re (by simp [hβ]; linarith))
  have hK : Continuous (lemma84LogKernel b (Real.log x) (-γ).im) := by
    unfold lemma84LogKernel
    exact Continuous.div (by fun_prop) (by fun_prop)
      (fun t => pow_ne_zero _ (lemma84_vertical_ne_zero hb _))
  have he : (fun t : ℝ => appendixBZetaIntegrand x β γ ((b : ℂ)+I*(t : ℂ))) =
      fun t => q t*lemma84LogKernel b (Real.log x) (-γ).im t := by
    funext t
    exact appendixB_integrand_eq_log_kernel hx β γ hγ b t
  rw [he]
  apply ((lemma84_log_kernel_integrable hb (Real.log x) (-γ).im).norm.const_mul ((2+1/b)^2)).mono'
    (hq.mul hK).aestronglyMeasurable
  filter_upwards [] with t
  simp only [Pi.mul_apply,norm_mul]
  exact mul_le_mul_of_nonneg_right (appendixB_right_ratio_bound hb hβ t) (norm_nonneg _)

lemma appendixB_right_tails {b x Y : ℝ} (hb : 0<b) (hx : 0<x) (hY : 0<Y)
    {β γ : ℂ} (hβ : β.re=0) (hγ : γ.re=0) (hγY : |γ.im|≤Y/2) :
    let f := fun t : ℝ => appendixBZetaIntegrand x β γ ((b : ℂ)+I*(t : ℂ))
    ‖∫ t : ℝ in Ioi Y, f t‖+‖∫ t : ℝ in Iic (-Y), f t‖≤
      8*(2+1/b)^2*Real.exp (b*Real.log x)/Y := by
  dsimp only
  let f := fun t : ℝ => appendixBZetaIntegrand x β γ ((b : ℂ)+I*(t : ℂ))
  let K := lemma84LogKernel b (Real.log x) (-γ).im
  let M := (2+1/b)^2
  have hM : 0≤M := sq_nonneg _
  have hi : Integrable f := appendixB_right_line_integrable hb hx hβ hγ
  have hKi : Integrable K := lemma84_log_kernel_integrable hb _ _
  have hbound (S : Set ℝ) (hS : MeasurableSet S) : ‖∫ t : ℝ in S, f t‖≤M*(∫ t : ℝ in S, ‖K t‖) := by
    apply (norm_integral_le_integral_norm _).trans
    have hh := setIntegral_mono_on hi.norm.integrableOn (hKi.norm.const_mul M).integrableOn hS (by
      intro t _
      dsimp [f,K,M]
      rw [appendixB_integrand_eq_log_kernel hx β γ hγ b t,norm_mul]
      exact mul_le_mul_of_nonneg_right (appendixB_right_ratio_bound hb hβ t) (norm_nonneg _))
    simpa only [integral_const_mul] using hh
  have hm : |(-γ).im|≤Y/2 := by simpa using hγY
  have hu := (hbound (Ioi Y) measurableSet_Ioi).trans
    (mul_le_mul_of_nonneg_left (lemma84_log_kernel_positive_tail hb hY (Real.log x) _ hm) hM)
  have hl := (hbound (Iic (-Y)) measurableSet_Iic).trans
    (mul_le_mul_of_nonneg_left (lemma84_log_kernel_negative_tail hb hY (Real.log x) _ hm) hM)
  exact (add_le_add hu hl).trans_eq (by dsimp [M]; ring)

end ZhangLS.Spec
