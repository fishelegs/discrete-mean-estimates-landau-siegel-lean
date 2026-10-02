import ZhangLS.Spec.Lemma54EighthHeightTail
set_option autoImplicit false
open ZhangLS.Spec Complex MeasureTheory Set

example (D n : ℕ) (x : ℝ) :
    lemma54EighthIntegral D n x =
      ∫ u : ℝ, (-(2*Real.pi:ℂ)*I*(Complex.exp (u:ℂ)-1))^n*
        lemma53OscillatoryKernel D x (u:ℂ) := rfl

example : lemma54EighthMomentConstant =
    2*(4*Real.pi)^8*Real.sqrt Real.pi*Real.exp 19 +
      ((4*Real.pi)^8*(4+2*Real.exp 1))*(100*Real.sqrt Real.pi*Real.exp 6) +
      (2*(4*Real.pi)^8*Real.sqrt Real.pi*Real.exp 20)*(2*(Nat.factorial 17:ℝ)) := rfl

example {D : ℕ} (hD : 1<D) (hL : 2000≤lemma23PaperL D) (t : ℝ) :
    ‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖ ≤
      lemma54EighthMomentConstant*lemma23PaperL D^7200/(1+t^2)^4 :=
  lemma54_eighth_mellin_frequency_bound hD hL t

example (D : ℕ) (hD : ⌈Real.exp 2000⌉₊+2≤D) (t : ℝ) :
    ‖lemma54PaperDeltaMellin D (1+I*(t:ℂ))‖ ≤
      lemma54EighthMomentConstant*lemma23PaperL D^7200/(1+t^2)^4 :=
  lemma54_eighth_mellin_explicit_threshold D hD t
-- GENERATED AXIOM CHECKS
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_majorant_tendsto_zero
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_right_vertical_tendsto_zero
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_infinite_contour_shift
#print axioms ZhangLS.Spec.lemma54EighthDerivativeTail
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_large_range_estimate
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_kernel_norm_left
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_left_tail_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_vertical_point_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_vertical_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_left_vertical_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_ray_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_right_ray_bound
#print axioms ZhangLS.Spec.lemma54_eighth_arctan_le_self
#print axioms ZhangLS.Spec.lemma54_eighth_positive_cauchy_tail
#print axioms ZhangLS.Spec.lemma54_eighth_negative_cauchy_tail
#print axioms ZhangLS.Spec.lemma54_eighth_weight_le_cauchy
#print axioms ZhangLS.Spec.lemma54_eighth_weight_tail_point
#print axioms ZhangLS.Spec.lemma54_eighth_bounded_weight_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_window_and_tail
#print axioms ZhangLS.Spec.lemma54EighthIntegral
#print axioms ZhangLS.Spec.lemma54_eighth_integral_zero
#print axioms ZhangLS.Spec.lemma54_eighth_integral_zero_actual
#print axioms ZhangLS.Spec.lemma54_eighth_kernel_hasDerivAt
#print axioms ZhangLS.Spec.lemma54_eighth_integral_hasDerivAt
#print axioms ZhangLS.Spec.lemma54_eighth_integral_continuous
#print axioms ZhangLS.Spec.lemma54_eighth_integral_norm_bound
#print axioms ZhangLS.Spec.lemma54_eighth_integral_large_range
#print axioms ZhangLS.Spec.lemma54_eighth_integral_isBigO_atTop
#print axioms ZhangLS.Spec.lemma54_eighth_integral_isBigO_at_zero
#print axioms ZhangLS.Spec.lemma54_eighth_integral_mellin_convergent
#print axioms ZhangLS.Spec.lemma54_eighth_integral_boundary_products
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_step
#print axioms ZhangLS.Spec.lemma54_eighth_zero_mellin_actual
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_iteration
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_integral_identity
#print axioms ZhangLS.Spec.lemma54_eighth_norm_shift_le
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_bound_by_moment
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_line_bound
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_frequency_bound
#print axioms ZhangLS.Spec.lemma54_eighth_mellin_explicit_threshold
#print axioms ZhangLS.Spec.lemma54EighthMoment
#print axioms ZhangLS.Spec.lemma54EighthGlobalConstant
#print axioms ZhangLS.Spec.lemma54EighthLogConstant
#print axioms ZhangLS.Spec.lemma54EighthExpConstant
#print axioms ZhangLS.Spec.lemma54EighthMomentConstant
#print axioms ZhangLS.Spec.lemma54_eighth_constants_pos
#print axioms ZhangLS.Spec.lemma54_eighth_moment_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_global_norm_bound
#print axioms ZhangLS.Spec.lemma54_eighth_small_moment_bound
#print axioms ZhangLS.Spec.lemma54EighthMomentEnvelope
#print axioms ZhangLS.Spec.lemma54_eighth_envelope_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_envelope_nonneg
#print axioms ZhangLS.Spec.lemma54_eighth_envelope_bound
#print axioms ZhangLS.Spec.lemma54_eighth_envelope_integral_bound
#print axioms ZhangLS.Spec.lemma54_eighth_moment_uniform_bound
#print axioms ZhangLS.Spec.lemma54EighthConstant
#print axioms ZhangLS.Spec.lemma54EighthMajorant
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_constant_pos
#print axioms ZhangLS.Spec.lemma54_eighth_contour_factor_pow_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_majorant_factorization
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_majorant_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_kernel_norm_real
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_kernel_integrable
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_majorant_integral_bound
#print axioms ZhangLS.Spec.lemma54_eighth_weighted_ray_norm_bound

#print ZhangLS.Spec.lemma54_eighth_mellin_frequency_bound
#print ZhangLS.Spec.lemma54_eighth_window_and_tail
