import ZhangLS.Spec.Lemma84LogPerronShift
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex MeasureTheory Set
set_option maxHeartbeats 1500000

lemma lemma84_inverse_quadratic_integral {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, (c^2+t^2)⁻¹) = Real.pi/c := by
  have he (t : ℝ) : (c^2+t^2)⁻¹ = (c^2)⁻¹*(1+(c⁻¹*t)^2)⁻¹ := by
    rw [←mul_inv]
    congr 1
    field_simp
  simp_rw [he]
  rw [integral_const_mul,MeasureTheory.Measure.integral_comp_mul_left (fun t : ℝ => (1+t^2)⁻¹) (c⁻¹),
    integral_univ_inv_one_add_sq]
  simp only [smul_eq_mul,inv_inv,abs_of_pos hc]
  field_simp

lemma lemma84_log_kernel_norm_integral {c : ℝ} (hc : 0 < c) (u v : ℝ) :
    (∫ t : ℝ, ‖lemma84LogKernel c u v t‖) = Real.exp (c*u)*Real.pi/c := by
  simp_rw [lemma84_log_kernel_norm]
  rw [integral_const_mul,integral_add_right_eq_self (fun t : ℝ => (c^2+t^2)⁻¹) v,lemma84_inverse_quadratic_integral hc]
  ring

lemma lemma84_log_kernel_tail_point_bound (c u v t : ℝ) {H : ℝ}
    (hH : 0 < H) (hv : |v| ≤ H/2) (ht : H ≤ |t|) :
    ‖lemma84LogKernel c u v t‖ ≤ 4*Real.exp (c*u)*((|t|)^2)⁻¹ := by
  have htp : 0 < |t| := hH.trans_le ht
  have habs : |t| ≤ |t+v|+|v| := by
    simpa using abs_add_le (t+v) (-v)
  have hgap : |t|/2 ≤ |t+v| := by linarith only [habs,hv,ht]
  have hsq : (|t|)^2 ≤ 4*(c^2+(t+v)^2) := by
    have hh := pow_le_pow_left₀ (by positivity : 0 ≤ |t|/2) hgap 2
    rw [sq_abs] at hh
    nlinarith only [hh,sq_nonneg c]
  have hden : 0 < c^2+(t+v)^2 := by nlinarith only [hsq,sq_pos_of_pos htp]
  have hinv : (c^2+(t+v)^2)⁻¹ ≤ 4*((|t|)^2)⁻¹ := by
    rw [inv_eq_one_div,←div_eq_mul_inv]
    exact (div_le_div_iff₀ hden (sq_pos_of_pos htp)).mpr (by linarith only [hsq])
  rw [lemma84_log_kernel_norm]
  have hh := mul_le_mul_of_nonneg_left hinv (Real.exp_pos (c*u)).le
  nlinarith only [hh]

lemma lemma84_log_kernel_positive_tail {c H : ℝ} (hc : 0 < c) (hH : 0 < H)
    (u v : ℝ) (hv : |v| ≤ H/2) :
    (∫ t : ℝ in Ioi H, ‖lemma84LogKernel c u v t‖) ≤ 4*Real.exp (c*u)/H := by
  have hi : IntegrableOn (fun t : ℝ => t^(-2 : ℝ)) (Ioi H) :=
    integrableOn_Ioi_rpow_of_lt (by norm_num) hH
  have hmajor : IntegrableOn (fun t : ℝ => 4*Real.exp (c*u)*t^(-2 : ℝ)) (Ioi H) :=
    hi.const_mul _
  have hh := setIntegral_mono_on (lemma84_log_kernel_integrable hc u v).norm.integrableOn
    hmajor measurableSet_Ioi (by
      intro t ht
      have htp : 0 < t := hH.trans (mem_Ioi.mp ht)
      have hp := lemma84_log_kernel_tail_point_bound c u v t hH hv
        (by rw [abs_of_pos htp]; exact (mem_Ioi.mp ht).le)
      simpa only [abs_of_pos htp,Real.rpow_neg htp.le,Real.rpow_two] using hp)
  apply hh.trans_eq
  rw [integral_const_mul,integral_Ioi_rpow_of_lt (by norm_num : (-2:ℝ) < -1) hH]
  norm_num
  rw [Real.rpow_neg_one]
  ring

lemma lemma84_log_kernel_negative_tail {c H : ℝ} (hc : 0 < c) (hH : 0 < H)
    (u v : ℝ) (hv : |v| ≤ H/2) :
    (∫ t : ℝ in Iic (-H), ‖lemma84LogKernel c u v t‖) ≤ 4*Real.exp (c*u)/H := by
  rw [← integral_comp_neg_Ioi H]
  have he (t : ℝ) : ‖lemma84LogKernel c u v (-t)‖ = ‖lemma84LogKernel c u (-v) t‖ := by
    simp only [lemma84_log_kernel_norm]
    congr 2
    ring
  simp_rw [he]
  exact lemma84_log_kernel_positive_tail hc hH u (-v) (by simpa using hv)

end ZhangLS.Spec
