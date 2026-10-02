import ZhangLS.Spec.Lemma84LogPerronLaplace
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform
set_option maxHeartbeats 1500000

lemma lemma84_inverse_square_vertical_norm (c t : ℝ) :
    ‖((c:ℂ)+I*(t:ℂ))⁻¹^2‖ = (c^2+t^2)⁻¹ := by
  rw [norm_pow,norm_inv,inv_pow,Complex.sq_norm]
  simp only [Complex.normSq_apply,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,
    zero_mul,one_mul,mul_zero,sub_zero,add_zero,zero_add]
  congr 1
  ring

lemma lemma84_inverse_quadratic_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (fun t : ℝ => (c^2+t^2)⁻¹) := by
  have hh := (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hc.ne')).const_mul (c^2)⁻¹
  convert hh using 1
  funext t
  rw [← mul_inv]
  congr 1
  field_simp

lemma lemma84_positive_laplace_fourier_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (𝓕 (lemma84PositiveLaplaceKernel c)) := by
  have heq : 𝓕 (lemma84PositiveLaplaceKernel c) =
      fun y : ℝ => ((c:ℂ)+I*((2*Real.pi*y : ℝ):ℂ))⁻¹^2 := by
    funext y
    rw [lemma84_positive_laplace_kernel_fourier hc y]
    congr 3
    push_cast
    ring
  rw [heq]
  have hh := (lemma84_inverse_quadratic_integrable hc).comp_mul_left'
    (R := 2*Real.pi) (by positivity)
  have hne (t : ℝ) : (c:ℂ)+I*(2*Real.pi*t : ℝ) ≠ 0 := by
    intro he
    have hre := congrArg Complex.re he
    simp at hre
    linarith only [hre,hc]
  have hcont : Continuous (fun t : ℝ => ((c:ℂ)+I*(2*Real.pi*t : ℝ))⁻¹^2) :=
    ((show Continuous (fun t : ℝ => (c:ℂ)+I*(2*Real.pi*t : ℝ)) by fun_prop).inv₀ hne).pow 2
  apply hh.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  rw [lemma84_inverse_square_vertical_norm]

/-- Exact inverse transform of the logarithmic Perron kernel; max(u,0)
retains the zero value at the strict cutoff u=0. -/
lemma lemma84_log_perron_fourier_kernel {c : ℝ} (hc : 0 < c) (u : ℝ) :
    (∫ t : ℝ, exp (I*(2*Real.pi*t*u : ℝ)) *
      (((c:ℂ)+I*(2*Real.pi*t : ℝ))⁻¹^2)) =
        (max u 0 : ℝ)*exp (-(c:ℂ)*(u:ℂ)) := by
  have hi := (lemma84_positive_laplace_kernel_integrable hc).fourierInv_fourier_eq
    (lemma84_positive_laplace_fourier_integrable hc)
    (lemma84_positive_laplace_kernel_continuous c).continuousAt (v := u)
  rw [Real.fourierInv_eq'] at hi
  simp only [Real.inner_apply,smul_eq_mul,lemma84_positive_laplace_kernel_fourier hc,
    lemma84PositiveLaplaceKernel] at hi
  convert hi using 1
  congr 1
  funext t
  congr 2 <;> push_cast <;> ring

lemma lemma84_log_perron_kernel {c : ℝ} (hc : 0 < c) (u : ℝ) :
    (2*Real.pi : ℂ)⁻¹ * (∫ t : ℝ, exp (((c:ℂ)+I*(t:ℂ))*(u:ℂ)) /
      ((c:ℂ)+I*(t:ℂ))^2) = (max u 0 : ℝ) := by
  have hi := lemma84_log_perron_fourier_kernel hc u
  have hscale := MeasureTheory.Measure.integral_comp_mul_left
    (fun t : ℝ => exp (I*(t:ℂ)*(u:ℂ))*(((c:ℂ)+I*(t:ℂ))⁻¹^2)) (2*Real.pi)
  have heq : (∫ t : ℝ, exp (I*(2*Real.pi*t*u : ℝ))*(((c:ℂ)+I*(2*Real.pi*t : ℝ))⁻¹^2)) =
      (2*Real.pi : ℂ)⁻¹ * ∫ t : ℝ, exp (I*(t:ℂ)*(u:ℂ))*(((c:ℂ)+I*(t:ℂ))⁻¹^2) := by
    simpa only [Complex.real_smul,abs_inv,abs_of_pos Real.two_pi_pos,Complex.ofReal_inv,
      Complex.ofReal_mul,Complex.ofReal_ofNat,mul_assoc] using hscale
  rw [heq] at hi
  have hintegral : (∫ t : ℝ, exp (((c:ℂ)+I*(t:ℂ))*(u:ℂ)) / ((c:ℂ)+I*(t:ℂ))^2) =
      exp ((c:ℂ)*(u:ℂ)) * ∫ t : ℝ,
        exp (I*(t:ℂ)*(u:ℂ))*(((c:ℂ)+I*(t:ℂ))⁻¹^2) := by
    rw [← integral_const_mul]
    congr 1
    funext t
    rw [add_mul,Complex.exp_add]
    simp only [div_eq_mul_inv,inv_pow,mul_assoc]
  rw [hintegral]
  calc
    _ = exp ((c:ℂ)*(u:ℂ))*((2*Real.pi:ℂ)⁻¹ * ∫ t : ℝ,
      exp (I*(t:ℂ)*(u:ℂ))*(((c:ℂ)+I*(t:ℂ))⁻¹^2)) := by ring
    _ = exp ((c:ℂ)*(u:ℂ))*((max u 0:ℝ)*exp (-(c:ℂ)*(u:ℂ))) := by rw [hi]
    _ = _ := by rw [neg_mul,Complex.exp_neg]; field_simp

end ZhangLS.Spec
