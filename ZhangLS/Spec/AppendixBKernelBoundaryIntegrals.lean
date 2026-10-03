import ZhangLS.Spec.AppendixBKernelStripBoundary
import ZhangLS.Spec.Lemma84BoundaryIntegralBounds

/-! Integrated bounds for all three displaced sides, preserving the true
logarithmic kernel and the actual auxiliary height. -/
set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ZhangLS.Spec
open Complex MeasureTheory Set

lemma appendixB_left_boundary_bound {D : ℕ} (hL : 0<lemma23PaperL D)
    {x M : ℝ} (hx : 0<x) (hM : 0≤M) (β γ : ℂ) (hγ : γ.re=0)
    (hnum : ∀ s : ℂ, AppendixBContourPoint D s →
      ‖riemannZeta (1+s)/riemannZeta (1+s-β)‖≤M) :
    ‖∫ t : ℝ in -appendixBContourHeight D..appendixBContourHeight D,
      appendixBZetaIntegrand x β γ ((-1/lemma23PaperL D : ℝ)+I*(t : ℂ))‖≤
      M*Real.exp (-Real.log x/lemma23PaperL D)*Real.pi*lemma23PaperL D := by
  have hY : 0≤appendixBContourHeight D := by
    unfold appendixBContourHeight
    positivity [proposition71_zeta_aux_height_pos D]
  have hh := lemma84_left_vertical_integral_bound
    (fun t : ℝ => appendixBZetaIntegrand x β γ ((-1/lemma23PaperL D : ℝ)+I*(t : ℂ)))
    (δ := 1/lemma23PaperL D) (H := appendixBContourHeight D) (M := M)
    (by positivity) hY hM (Real.log x) (-γ).im (by
      intro t ht
      have hs : AppendixBContourPoint D ((-1/lemma23PaperL D : ℝ)+I*(t : ℂ)) := by
        apply Or.inl
        exact ⟨by simp,by simpa using abs_le.mpr ⟨ht.1.le,ht.2⟩⟩
      dsimp only
      rw [appendixB_integrand_eq_log_kernel hx β γ hγ _ t,norm_mul]
      simpa only [neg_div] using mul_le_mul_of_nonneg_right (hnum _ hs)
        (norm_nonneg (lemma84LogKernel (-1/lemma23PaperL D) (Real.log x) (-γ).im t)))
  apply hh.trans_eq
  rw [show -(1/lemma23PaperL D)*Real.log x= -Real.log x/lemma23PaperL D by ring]
  field_simp

lemma appendixB_horizontal_bound {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D)
    {x M : ℝ} (hx : 1≤x) (hscale : lemma44PaperAlpha D*Real.log x≤Real.pi)
    (hM : 0≤M) (β γ : ℂ) (hγ : ‖γ‖≤3*lemma44PaperAlpha D)
    (hnum : ∀ s : ℂ, AppendixBContourPoint D s →
      ‖riemannZeta (1+s)/riemannZeta (1+s-β)‖≤M) :
    ‖∫ σ : ℝ in (-1/lemma23PaperL D)..(6*lemma44PaperAlpha D),
      appendixBZetaIntegrand x β γ ((σ : ℂ)-I*(appendixBContourHeight D : ℂ))‖+
    ‖∫ σ : ℝ in (-1/lemma23PaperL D)..(6*lemma44PaperAlpha D),
      appendixBZetaIntegrand x β γ ((σ : ℂ)+I*(appendixBContourHeight D : ℂ))‖≤
      8*M*Real.exp (6*Real.pi)*(6*lemma44PaperAlpha D+1/lemma23PaperL D)/(appendixBContourHeight D)^2 := by
  have hLp : 0<lemma23PaperL D := by linarith
  have ha := lemma83_alpha_small (by linarith only [hL] : 100≤lemma23PaperL D)
  have hxp : 0<x := lt_of_lt_of_le zero_lt_one hx
  have hH1 : 1≤proposition71ZetaAuxHeight D :=
    Real.one_le_exp (Real.rpow_nonneg (by change 0≤lemma23PaperL D; linarith) _)
  have hY : 0<appendixBContourHeight D := by unfold appendixBContourHeight; linarith
  have hγY : ‖-γ‖≤appendixBContourHeight D/2 := by
    rw [norm_neg]
    unfold appendixBContourHeight
    linarith [ha.2]
  have hscale' : (6*lemma44PaperAlpha D)*Real.log x≤6*Real.pi := by linarith
  have hpoint (s : ℂ) (hs : AppendixBContourPoint D s)
      (him : |s.im|=appendixBContourHeight D) (hre : s.re≤6*lemma44PaperAlpha D) :
      ‖appendixBZetaIntegrand x β γ s‖≤4*M*Real.exp (6*Real.pi)/(appendixBContourHeight D)^2 := by
    have hk := lemma84_horizontal_kernel_bound s (-γ) hY (Real.log_nonneg hx) him hγY hre hscale'
    unfold appendixBZetaIntegrand
    rw [mul_div_assoc,lemma84_positive_cpow_eq_exp hxp,norm_mul]
    have hh := mul_le_mul (hnum s hs) (by simpa only [sub_eq_add_neg] using hk) (norm_nonneg _) hM
    exact hh.trans_eq (by ring)
  have hab : -1/lemma23PaperL D≤6*lemma44PaperAlpha D := by
    have hi : 0<1/lemma23PaperL D := by positivity
    simp only [neg_div]
    linarith [ha.1]
  have hlo (σ : ℝ) (hσ : σ∈Icc (-1/lemma23PaperL D) (6*lemma44PaperAlpha D)) :
      ‖appendixBZetaIntegrand x β γ ((σ : ℂ)-I*(appendixBContourHeight D : ℂ))‖≤
        4*M*Real.exp (6*Real.pi)/(appendixBContourHeight D)^2 := by
    have him : |((σ : ℂ)-I*(appendixBContourHeight D : ℂ)).im|=appendixBContourHeight D := by
      simp [abs_of_pos hY]
    exact hpoint _ (Or.inr ⟨him,by simpa using hσ.1,by simpa using hσ.2⟩) him (by simpa using hσ.2)
  have hhi (σ : ℝ) (hσ : σ∈Icc (-1/lemma23PaperL D) (6*lemma44PaperAlpha D)) :
      ‖appendixBZetaIntegrand x β γ ((σ : ℂ)+I*(appendixBContourHeight D : ℂ))‖≤
        4*M*Real.exp (6*Real.pi)/(appendixBContourHeight D)^2 := by
    have him : |((σ : ℂ)+I*(appendixBContourHeight D : ℂ)).im|=appendixBContourHeight D := by
      simp [abs_of_pos hY]
    exact hpoint _ (Or.inr ⟨him,by simpa using hσ.1,by simpa using hσ.2⟩) him (by simpa using hσ.2)
  have hh := lemma84_horizontal_integrals_bound (appendixBZetaIntegrand x β γ) hab
    (by positivity : 0≤4*M*Real.exp (6*Real.pi)/(appendixBContourHeight D)^2) hlo hhi
  exact hh.trans_eq (by ring)

end ZhangLS.Spec
