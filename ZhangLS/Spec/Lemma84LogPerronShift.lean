import ZhangLS.Spec.Lemma84LogPerronKernel
import ZhangLS.Spec.Lemma84PaperResidue
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set Filter
open scoped Topology
set_option maxHeartbeats 1500000

noncomputable def lemma84LogKernel (c u v t : ℝ) : ℂ :=
  exp (((c:ℂ)+I*(t:ℂ))*(u:ℂ))/((c:ℂ)+I*((t+v:ℝ):ℂ))^2

lemma lemma84_vertical_ne_zero {c : ℝ} (hc : 0 < c) (t : ℝ) :
    (c:ℂ)+I*(t:ℂ) ≠ 0 := by
  intro he
  have hh := congrArg Complex.re he
  simp at hh
  linarith only [hh,hc]

lemma lemma84_log_kernel_norm (c u v t : ℝ) :
    ‖lemma84LogKernel c u v t‖ = Real.exp (c*u)*(c^2+(t+v)^2)⁻¹ := by
  unfold lemma84LogKernel
  rw [div_eq_mul_inv,norm_mul,← inv_pow,lemma84_inverse_square_vertical_norm]
  rw [Complex.norm_exp]
  congr 2
  simp

lemma lemma84_log_kernel_integrable {c : ℝ} (hc : 0 < c) (u v : ℝ) :
    Integrable (lemma84LogKernel c u v) := by
  have hcont : Continuous (lemma84LogKernel c u v) := by
    unfold lemma84LogKernel
    apply Continuous.div (by fun_prop) (by fun_prop)
    intro t
    exact pow_ne_zero _ (lemma84_vertical_ne_zero hc _)
  have hi := ((lemma84_inverse_quadratic_integrable hc).comp_add_right v).const_mul (Real.exp (c*u))
  apply hi.mono' hcont.aestronglyMeasurable
  filter_upwards [] with t
  rw [lemma84_log_kernel_norm]

lemma lemma84_log_kernel_translate (c u v t : ℝ) :
    lemma84LogKernel c u v t = exp (-I*(v:ℂ)*(u:ℂ))*lemma84LogKernel c u 0 (t+v) := by
  unfold lemma84LogKernel
  simp only [add_zero]
  rw [← mul_div_assoc,← Complex.exp_add]
  congr 2
  push_cast
  simp <;> ring

/-- Exact imaginary translation of the double-pole Perron kernel. -/
lemma lemma84_shifted_log_perron_kernel {c : ℝ} (hc : 0 < c) (u v : ℝ) :
    (2*Real.pi : ℂ)⁻¹*(∫ t : ℝ, lemma84LogKernel c u v t) =
      exp (-I*(v:ℂ)*(u:ℂ))*(max u 0 : ℝ) := by
  simp_rw [lemma84_log_kernel_translate c u v]
  rw [integral_const_mul,integral_add_right_eq_self]
  have hh : (2*Real.pi : ℂ)⁻¹*(∫ t : ℝ, lemma84LogKernel c u 0 t) = (max u 0 : ℝ) := by
    simpa only [lemma84LogKernel,add_zero] using lemma84_log_perron_kernel hc u
  calc
    _ = exp (-I*(v:ℂ)*(u:ℂ))*((2*Real.pi : ℂ)⁻¹*(∫ t : ℝ, lemma84LogKernel c u 0 t)) := by ring
    _ = _ := by rw [hh]

lemma lemma84_pure_imaginary_eq {m : ℂ} (hm : m.re = 0) : m = I*(m.im:ℂ) := by
  apply Complex.ext <;> simp [hm]

/-- The source logarithmic kernel, including the strict endpoint at y=1. -/
lemma lemma84_original_log_perron_kernel {c y : ℝ} (hc : 0 < c) (hy : 0 < y)
    (m : ℂ) (hm : m.re = 0) :
    (2*Real.pi : ℂ)⁻¹*(∫ t : ℝ,
      (y:ℂ)^((c:ℂ)+I*(t:ℂ))/((c:ℂ)+I*(t:ℂ)+m)^2) =
        if 1 < y then (y:ℂ)^(-m)*(Real.log y : ℂ) else 0 := by
  have hid (t : ℝ) : (y:ℂ)^((c:ℂ)+I*(t:ℂ))/((c:ℂ)+I*(t:ℂ)+m)^2 =
      lemma84LogKernel c (Real.log y) m.im t := by
    rw [lemma84_positive_cpow_eq_exp hy]
    unfold lemma84LogKernel
    rw [lemma84_pure_imaginary_eq hm]
    push_cast
    congr 2
    simp <;> ring
  simp_rw [hid]
  rw [lemma84_shifted_log_perron_kernel hc]
  by_cases h1 : 1 < y
  · rw [if_pos h1,max_eq_left (Real.log_pos h1).le,lemma84_positive_cpow_eq_exp hy,
      lemma84_pure_imaginary_eq hm]
    congr 2
    simp <;> ring
  · rw [if_neg h1,max_eq_right (Real.log_nonpos hy.le (le_of_not_gt h1))]
    simp

end ZhangLS.Spec
