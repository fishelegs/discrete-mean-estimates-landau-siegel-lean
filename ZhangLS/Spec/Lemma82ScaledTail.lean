import ZhangLS.Spec.Lemma82FiniteAbel

namespace ZhangLS.Spec
open Complex Finset MeasureTheory Set Metric
open scoped Real
set_option maxHeartbeats 1000000

/-- Scaling before differentiation removes the otherwise artificial log x
loss in the Abel tail. -/
noncomputable def lemma82ScaledRemainder {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (s : ℂ) : ℂ :=
  (x : ℂ)^s * (dirichletLFunction χ s - lemma82FinitePolynomial χ x s)

lemma lemma82_scaled_remainder_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {x : ℝ} (hx : 1 ≤ x) {s : ℂ} (hs : 0 < s.re) :
    ‖lemma82ScaledRemainder χ x s‖ ≤ (D : ℝ) * (‖s‖ / s.re + 1) := by
  have hxp : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hp : 0 < x^s.re := Real.rpow_pos_of_pos hxp _
  unfold lemma82ScaledRemainder
  rw [norm_mul, norm_cpow_eq_rpow_re_of_pos hxp,
    lemma82_actual_abel_remainder χ hD hx hs]
  apply (mul_le_mul_of_nonneg_left (norm_sub_le _ _) hp.le).trans
  rw [norm_mul, norm_mul, norm_cpow_eq_rpow_re_of_pos hxp, Complex.neg_re]
  have hh := mul_le_mul_of_nonneg_left
    (add_le_add
      (mul_le_mul_of_nonneg_left (lemma82_abel_tail_norm χ hD hx hs) (norm_nonneg s))
      (mul_le_mul_of_nonneg_left (χ.norm_sum_Icc_evalNat_le_modulus hD ⌊x⌋₊)
        (Real.rpow_nonneg hxp.le (-s.re)))) hp.le
  apply hh.trans_eq
  rw [Real.rpow_neg hxp.le]
  field_simp [hp.ne', hs.ne']
  <;> ring

lemma lemma82_finite_polynomial_differentiable {D : ℕ}
    (χ : RealPrimitiveCharacter D) (x : ℝ) :
    Differentiable ℂ (lemma82FinitePolynomial χ x) := by
  unfold lemma82FinitePolynomial
  apply Differentiable.fun_sum
  intro n hn
  apply Differentiable.const_mul
  apply Differentiable.const_cpow (differentiable_id.neg)
  exact Or.inl (by exact_mod_cast (show n ≠ 0 by have := (Finset.mem_Icc.mp hn).1; omega))

lemma lemma82_scaled_remainder_differentiable {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) {x : ℝ} (hx : 0 < x) :
    Differentiable ℂ (lemma82ScaledRemainder χ x) := by
  exact (Differentiable.const_cpow differentiable_id
    (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))).mul
      ((differentiable_dirichletLFunction_of_one_lt_modulus χ hD).sub
        (lemma82_finite_polynomial_differentiable χ x))

/-- The derivative of the scaled actual tail is O(D), uniformly in x.
This is a Cauchy estimate on radius 1/4, whose entire circle has Re z≥3/4. -/
lemma lemma82_scaled_remainder_deriv_norm {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) {x : ℝ} (hx : 1 ≤ x) {s : ℂ}
    (hs : s.re = 1) (hsnorm : ‖s‖ ≤ 2) :
    ‖deriv (lemma82ScaledRemainder χ x) s‖ ≤ 16 * (D : ℝ) := by
  have hd := lemma82_scaled_remainder_differentiable χ hD (lt_of_lt_of_le zero_lt_one hx)
  have hb (z : ℂ) (hz : z ∈ Metric.sphere s (1/4)) :
      ‖lemma82ScaledRemainder χ x z‖ ≤ 4 * (D : ℝ) := by
    have hdist : ‖z-s‖ = (1:ℝ)/4 := mem_sphere_iff_norm.mp hz
    have hzn : ‖z‖ ≤ 9/4 := by
      have hh := norm_add_le (z-s) s
      rw [sub_add_cancel, hdist] at hh
      linarith
    have hzr : 3/4 ≤ z.re := by
      have hh := (Complex.abs_re_le_norm (z-s)).trans_eq hdist
      rw [Complex.sub_re, hs] at hh
      have := (abs_le.mp hh).1
      linarith
    apply (lemma82_scaled_remainder_norm χ hD hx (by linarith : 0 < z.re)).trans
    have hquot : ‖z‖ / z.re ≤ 3 := by
      apply (div_le_iff₀ (by linarith : 0 < z.re)).mpr
      linarith
    nlinarith [Nat.cast_nonneg (α := ℝ) D]
  have hh := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le
    (by norm_num : (0:ℝ) < 1/4) hd.diffContOnCl hb
  linarith

end ZhangLS.Spec
