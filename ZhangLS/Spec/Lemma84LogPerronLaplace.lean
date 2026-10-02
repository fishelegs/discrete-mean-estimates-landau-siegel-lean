import ZhangLS.Spec.Lemma84Definitions
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Topology FourierTransform
set_option maxHeartbeats 1500000

lemma lemma84_laplace_moment_integrable {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => (t:ℂ)*exp (-z*(t:ℂ))) (Ioi 0) := by
  have hmaj : IntegrableOn (fun t : ℝ => t*Real.exp (-z.re*t)) (Ioi 0) := by
    simpa using integrableOn_rpow_mul_exp_neg_mul_rpow (s := 1) (p := 1) (by norm_num) (by norm_num) hz
  apply hmaj.mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,
    Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,mul_zero,sub_zero,
    abs_of_pos (mem_Ioi.mp ht)]
  rfl

lemma lemma84_laplace_moment_tendsto {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun t : ℝ => (t:ℂ)*exp (-z*(t:ℂ))) atTop (nhds 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  have hh := tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 z.re hz
  simp only [Real.rpow_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht
  simp only [norm_mul,Complex.norm_real,Real.norm_eq_abs,Complex.norm_exp,Complex.mul_re,
    Complex.neg_re,Complex.ofReal_re,Complex.neg_im,Complex.ofReal_im,mul_zero,sub_zero,
    abs_of_nonneg ht]

/-- The actual complex Laplace transform of t on the positive half-line. -/
lemma lemma84_laplace_moment_integral {z : ℂ} (hz : 0 < z.re) :
    (∫ t : ℝ in Ioi 0, (t:ℂ)*exp (-z*(t:ℂ))) = z⁻¹^2 := by
  have hz0 : z ≠ 0 := by intro he; simp only [he,Complex.zero_re] at hz; linarith
  let F : ℝ → ℂ := fun t => -(exp (-z*(t:ℂ))*(z*(t:ℂ)+1))/z^2
  have hder (t : ℝ) : HasDerivAt F ((t:ℂ)*exp (-z*(t:ℂ))) t := by
    have he := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul (-z)).cexp
    have hl := ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul z).add_const 1
    have hh := (he.mul hl).neg.div_const (z^2)
    convert hh using 1
    simp only [Complex.ofRealCLM_apply,Complex.ofReal_one,mul_one]
    field_simp
    ring
  have hexp : Tendsto (fun t : ℝ => exp (-z*(t:ℂ))) atTop (nhds 0) := by
    rw [Complex.tendsto_exp_nhds_zero_iff]
    simpa only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.neg_im,
      Complex.ofReal_im,mul_zero,sub_zero] using
      tendsto_const_nhds.neg_mul_atTop (by linarith : -z.re < 0) tendsto_id
  have hlim : Tendsto F atTop (nhds 0) := by
    have hh := (((lemma84_laplace_moment_tendsto hz).const_mul z).add hexp).neg.div_const (z^2)
    simpa only [mul_zero,add_zero,neg_zero,zero_div] using hh.congr
      (fun t => by dsimp [F]; ring)
  have hi := integral_Ioi_of_hasDerivAt_of_tendsto' (fun t _ => hder t)
    (lemma84_laplace_moment_integrable hz) hlim
  simpa [F,inv_pow,neg_div] using hi

/-- A continuous integrable kernel, including the exact zero endpoint. -/
noncomputable def lemma84PositiveLaplaceKernel (c t : ℝ) : ℂ :=
  (max t 0 : ℝ)*exp (-(c:ℂ)*(t:ℂ))

lemma lemma84_positive_laplace_kernel_continuous (c : ℝ) :
    Continuous (lemma84PositiveLaplaceKernel c) := by
  unfold lemma84PositiveLaplaceKernel
  fun_prop

lemma lemma84_positive_laplace_kernel_eq_indicator (c : ℝ) :
    lemma84PositiveLaplaceKernel c =
      (Ioi 0).indicator (fun t : ℝ => (t:ℂ)*exp (-(c:ℂ)*(t:ℂ))) := by
  funext t
  by_cases ht : 0 < t
  · simp [lemma84PositiveLaplaceKernel,ht,max_eq_left ht.le]
  · simp [lemma84PositiveLaplaceKernel,ht,max_eq_right (le_of_not_gt ht)]

lemma lemma84_positive_laplace_kernel_integrable {c : ℝ} (hc : 0 < c) :
    Integrable (lemma84PositiveLaplaceKernel c) := by
  rw [lemma84_positive_laplace_kernel_eq_indicator]
  exact (integrable_indicator_iff measurableSet_Ioi).mpr
    (lemma84_laplace_moment_integrable (by simpa using hc : 0 < (c:ℂ).re))

lemma lemma84_positive_laplace_kernel_fourier {c : ℝ} (hc : 0 < c) (y : ℝ) :
    𝓕 (lemma84PositiveLaplaceKernel c) y = ((c:ℂ)+2*Real.pi*I*(y:ℂ))⁻¹^2 := by
  rw [Real.fourier_eq']
  simp only [Real.inner_apply]
  rw [lemma84_positive_laplace_kernel_eq_indicator]
  have heq : (fun t : ℝ => exp ((↑(-2*Real.pi*(t*y)):ℂ)*I) •
      (Ioi 0).indicator (fun t : ℝ => (t:ℂ)*exp (-(c:ℂ)*(t:ℂ))) t) =
      (Ioi 0).indicator (fun t : ℝ => (t:ℂ)*exp (-((c:ℂ)+2*Real.pi*I*(y:ℂ))*(t:ℂ))) := by
    funext t
    by_cases ht : t ∈ Ioi (0:ℝ)
    · simp only [indicator_of_mem ht,smul_eq_mul,Real.inner_apply]
      rw [show exp ((↑(-2*Real.pi*(t*y)):ℂ)*I)*((t:ℂ)*exp (-(c:ℂ)*(t:ℂ))) =
        (t:ℂ)*(exp ((↑(-2*Real.pi*(t*y)):ℂ)*I)*exp (-(c:ℂ)*(t:ℂ))) by ring,
        ← Complex.exp_add]
      congr 2
      push_cast
      ring
    · simp only [indicator_of_notMem ht,smul_zero]
  rw [heq,integral_indicator measurableSet_Ioi]
  apply lemma84_laplace_moment_integral
  simpa using hc

end ZhangLS.Spec
