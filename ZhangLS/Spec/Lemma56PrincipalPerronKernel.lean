import ZhangLS.Spec.Lemma56PrincipalPerronResidue
import ZhangLS.Spec.Lemma56PerronKernel

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Metric
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

noncomputable def lemma56PerronComplexKernel (B x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ) ^ s * Complex.exp (s ^ 2 / (4 * (B : ℂ) ^ 2)) / s

lemma lemma56_perron_complex_kernel_at_line (B x σ t : ℝ) :
    lemma56PerronComplexKernel B x ((σ : ℂ) + (t : ℂ) * I) =
      lemma56PerronKernel B σ x t := rfl

lemma lemma56_perron_complex_kernel_analytic {x : ℝ} (hx : 0 < x) (B : ℝ)
    {s : ℂ} (hs : s ≠ 0) : AnalyticAt ℂ (lemma56PerronComplexKernel B x) s := by
  have hpower : AnalyticAt ℂ (fun z : ℂ => (x : ℂ) ^ z) s := by
    have he : (fun z : ℂ => (x : ℂ) ^ z) = fun z => Complex.exp (Complex.log (x : ℂ) * z) := by
      funext z
      exact Complex.cpow_def_of_ne_zero (ofReal_ne_zero.mpr hx.ne') z
    rw [he]
    fun_prop
  have hExp : AnalyticAt ℂ (fun z : ℂ => Complex.exp (z ^ 2 / (4 * (B : ℂ) ^ 2))) s := by
    fun_prop
  exact (hpower.mul hExp).div analyticAt_id hs

lemma lemma56_perron_complex_kernel_at_one (B x : ℝ) :
    lemma56PerronComplexKernel B x 1 =
      ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ) := by
  unfold lemma56PerronComplexKernel
  rw [Complex.cpow_one, one_pow, div_one]
  have he : (1 : ℂ) / (4 * (B : ℂ) ^ 2) = ((1 / (4 * B ^ 2) : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [he, ← Complex.ofReal_exp, ← Complex.ofReal_mul]

lemma lemma56_rectangle_translation_one (f : ℂ → ℂ) (a H : ℝ) :
    lemma44GeneralRectangleBoundaryIntegral (fun w => f (w + 1)) (a - 1) 1 H =
      lemma44GeneralRectangleBoundaryIntegral f a 2 H := by
  have hp (u : ℝ) : ((u : ℂ) + (H : ℂ) * I) + 1 = ((u + 1 : ℝ) : ℂ) + (H : ℂ) * I := by
    push_cast
    ring
  have hm (u : ℝ) : ((u : ℂ) - (H : ℂ) * I) + 1 = ((u + 1 : ℝ) : ℂ) - (H : ℂ) * I := by
    push_cast
    ring
  have hv (u t : ℝ) : (((u - 1 : ℝ) : ℂ) + (t : ℂ) * I) + 1 = (u : ℂ) + (t : ℂ) * I := by
    push_cast
    ring
  have hb := intervalIntegral.integral_comp_add_right (fun u : ℝ => f ((u : ℂ) - (H : ℂ) * I))
    (a := a - 1) (b := 1) 1
  have ht := intervalIntegral.integral_comp_add_right (fun u : ℝ => f ((u : ℂ) + (H : ℂ) * I))
    (a := a - 1) (b := 1) 1
  norm_num only [sub_add_cancel, one_add_one_eq_two] at hb ht
  unfold lemma44GeneralRectangleBoundaryIntegral
  have hright (t : ℝ) : (((1 : ℝ) : ℂ) + (t : ℂ) * I) + 1 = ((2 : ℝ) : ℂ) + (t : ℂ) * I := by
    push_cast
    ring
  simp only [hm, hp, hright, hv]
  rw [hb, ht]

lemma lemma56_actual_perron_pole_rectangle {x a H : ℝ} (hx : 0 < x)
    (ha0 : 0 < a) (ha1 : a < 1) (hH : 0 < H) (B : ℝ) :
    lemma44GeneralRectangleBoundaryIntegral
      (fun s => lemma56PerronComplexKernel B x s / (s - 1)) a 2 H =
        2 * (Real.pi : ℂ) * I * ((x * Real.exp (1 / (4 * B ^ 2)) : ℝ) : ℂ) := by
  let N : ℂ → ℂ := fun w => lemma56PerronComplexKernel B x (w + 1)
  have hN : DifferentiableOn ℂ N (lemma44ClosedRectangle (a - 1) 1 H) := by
    intro w hw
    have hp : 0 < (w + 1).re := by
      have hre := hw.1.1
      simp only [add_re, one_re]
      linarith only [hre, ha0]
    have hn : w + 1 ≠ 0 := by intro he; simp [he] at hp
    have ha := (lemma56_perron_complex_kernel_analytic hx B hn).differentiableAt
    exact (ha.comp w (differentiableAt_id.add_const 1)).differentiableWithinAt
  have hr := lemma56_positive_right_simple_pole_rectangle N
    (by linarith only [ha1] : a - 1 < 0) (by norm_num : (1 : ℝ) ≤ 1) hH hN
  have hf : (fun w : ℂ => N w / w) =
      fun w => (lemma56PerronComplexKernel B x (w + 1) / ((w + 1) - 1)) := by
    funext w
    simp [N]
  rw [hf] at hr
  rw [lemma56_rectangle_translation_one (fun s : ℂ => lemma56PerronComplexKernel B x s / (s - 1)) a H] at hr
  simpa only [N, zero_add, lemma56_perron_complex_kernel_at_one] using hr

end ZhangLS.Spec
