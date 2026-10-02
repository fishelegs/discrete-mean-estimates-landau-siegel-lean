import ZhangLS.Spec.Lemma102CircleObjects
import ZhangLS.Spec.Lemma84LogPerronSeries
import ZhangLS.Spec.Lemma84UContourBound
import ZhangLS.Spec.ChiEulerAnchor
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Finset
set_option maxHeartbeats 1500000

lemma lemma102_unshifted_actual_ratio_right_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (a b s : ℂ) (ha : a.re = 0) (hb : b.re = 0) (hs : 0 < s.re) :
    ‖dirichletLFunction χ (1+s+a)*dirichletLFunction χ (1+s+b)/dirichletLFunction χ (1+s)‖ ≤
      (1+s.re⁻¹)^3 := by
  have h1 := chi_actual_L_right_bound χ (s := 1+s+a) (by simp only [Complex.add_re,Complex.one_re,ha]; linarith)
  have h2 := chi_actual_L_right_bound χ (s := 1+s+b) (by simp only [Complex.add_re,Complex.one_re,hb]; linarith)
  have h0 := chi_actual_L_inverse_right_bound χ (s := 1+s) (by simp only [Complex.add_re,Complex.one_re]; linarith)
  simp only [Complex.add_re,Complex.one_re,ha,hb,add_zero,add_sub_cancel_left] at h1 h2 h0
  rw [div_eq_mul_inv,norm_mul,norm_mul]
  calc
    _ ≤ (1+s.re⁻¹)*(1+s.re⁻¹)*(1+s.re⁻¹) :=
      mul_le_mul (mul_le_mul h1 h2 (norm_nonneg _) (by positivity)) h0 (norm_nonneg _) (by positivity)
    _ = _ := by ring

noncomputable def lemma102_unshiftedRightLineMajorant (b : ℝ) (d r : ℕ) : ℝ :=
  (1+b⁻¹)^3 * (lemma84UGrowthConstant*
    ∏ q ∈ (d*r).primeFactors, (1+lemma84UGrowthConstant*(q:ℝ)^(-(1+b))))

lemma lemma102_unshifted_right_line_majorant_nonneg {b : ℝ} (hb : 0 < b) (d r : ℕ) :
    0 ≤ lemma102_unshiftedRightLineMajorant b d r := by
  unfold lemma102_unshiftedRightLineMajorant
  positivity [lemma84_u_growth_constant_pos]

lemma lemma102_unshifted_actual_right_line_numerator_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (d r : ℕ) {b : ℝ} (hb : 0 < b) (t : ℝ) :
    ‖(dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ))+lemma83PaperBeta D c (j+1))*
      dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ))+lemma83PaperBeta D c (j+2))/
        dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ)))) *
      lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r (1+((b:ℂ)+I*(t:ℂ)))‖ ≤
        lemma102_unshiftedRightLineMajorant b d r := by
  have hQ := lemma102_unshifted_actual_ratio_right_bound χ (lemma83PaperBeta D c (j+1))
    (lemma83PaperBeta D c (j+2)) ((b:ℂ)+I*(t:ℂ))
    (lemma83_beta_re D c (j+1)) (lemma83_beta_re D c (j+2)) (by simpa using hb)
  have hU := lemma83_uniform_growth χ (lemma83PaperBeta D c) (lemma83_beta_re D c) j d r
    lemma84UGrowthConstant
    (by unfold lemma84UGrowthConstant; linarith only [lemma83_exceptional_constant_pos])
    (by unfold lemma84UGrowthConstant; linarith only [lemma83_regular_product_bound_pos])
    (1+((b:ℂ)+I*(t:ℂ))) (by simp; linarith)
  simp only [Complex.add_re,Complex.one_re,Complex.ofReal_re,Complex.mul_re,
    Complex.I_re,Complex.I_im,Complex.ofReal_im,zero_mul,one_mul,sub_zero,add_zero] at hQ hU
  rw [norm_mul]
  exact mul_le_mul hQ hU.le (norm_nonneg _) (by positivity)

/-- The entire initial α-line integrand is genuinely integrable, before any
contour cutting or limiting step. -/
lemma lemma102_unshifted_actual_right_line_integrable {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (c : ℝ) (j : Fin 3) (d r : ℕ) {b x : ℝ}
    (hb : 0 < b) (hx : 0 < x) :
    Integrable (fun t : ℝ => lemma84AnalyticCircleIntegrand χ
      (lemma83PaperBeta D c (j+1)) (lemma83PaperBeta D c (j+2)) ((0:ℂ))
      (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x ((b:ℂ)+I*(t:ℂ))) := by
  let F := fun t : ℝ => lemma84AnalyticCircleIntegrand χ
    (lemma83PaperBeta D c (j+1)) (lemma83PaperBeta D c (j+2)) ((0:ℂ))
    (lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r) x ((b:ℂ)+I*(t:ℂ))
  have hLcont := (differentiable_dirichletLFunction_of_one_lt_modulus χ hD).continuous
  have hden (t : ℝ) : dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ))) ≠ 0 :=
    lemma84_actual_L_ne_zero_right χ (by simp; linarith)
  have hUcont : Continuous (fun t : ℝ => lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r
      (1+((b:ℂ)+I*(t:ℂ)))) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    have hu := lemma83_euler_correction_analyticOnNhd χ _ (lemma83_beta_re D c) j d r
      (1+((b:ℂ)+I*(t:ℂ))) (by simp; linarith)
    exact hu.continuousAt.comp (f := fun v : ℝ => 1+((b:ℂ)+I*(v:ℂ))) (show ContinuousAt (fun v : ℝ => 1+((b:ℂ)+I*(v:ℂ))) t by fun_prop)
  have hkernelcont : Continuous (fun t : ℝ => lemma84LogKernel b (Real.log x)
      ((0:ℂ)).im t) := by
    unfold lemma84LogKernel
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    exact pow_ne_zero _ (lemma84_vertical_ne_zero hb _)
  have he (t : ℝ) : F t =
      (dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ))+lemma83PaperBeta D c (j+1))*
      dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ))+lemma83PaperBeta D c (j+2))/
        dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ)))) *
      lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r (1+((b:ℂ)+I*(t:ℂ))) *
        lemma84LogKernel b (Real.log x) ((0:ℂ)).im t := by
    dsimp [F,lemma84AnalyticCircleIntegrand]
    rw [mul_div_assoc,lemma84_original_kernel_eq_log hx b _ (by simp)]
    <;> simp only [Complex.zero_im]
  have hcont : Continuous F := by
    have hf : F = fun t : ℝ => (dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ))+lemma83PaperBeta D c (j+1))*
      dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ))+lemma83PaperBeta D c (j+2))/
        dirichletLFunction χ (1+((b:ℂ)+I*(t:ℂ)))) *
      lemma83EulerCorrection χ (lemma83PaperBeta D c) j d r (1+((b:ℂ)+I*(t:ℂ))) *
        lemma84LogKernel b (Real.log x) ((0:ℂ)).im t := funext he
    rw [hf]
    exact (((show Continuous (fun t : ℝ => dirichletLFunction χ
      (1+((b:ℂ)+I*(t:ℂ))+lemma83PaperBeta D c (j+1))*dirichletLFunction χ
      (1+((b:ℂ)+I*(t:ℂ))+lemma83PaperBeta D c (j+2))) by fun_prop).div
      (by fun_prop) hden).mul hUcont).mul hkernelcont
  have hi := (lemma84_log_kernel_integrable hb (Real.log x) ((0:ℂ)).im).norm.const_mul
    (lemma102_unshiftedRightLineMajorant b d r)
  apply hi.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  rw [he,norm_mul]
  exact mul_le_mul_of_nonneg_right (lemma102_unshifted_actual_right_line_numerator_bound χ c j d r hb t) (norm_nonneg _)

end ZhangLS.Spec
