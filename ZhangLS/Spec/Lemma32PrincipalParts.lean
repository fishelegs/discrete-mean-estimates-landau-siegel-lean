import ZhangLS.Spec.Lemma32ActualResidue
import ZhangLS.Spec.Lemma44LocalRectangle
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Filter
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32DividedRemainder {D : ℕ} (χ : RealPrimitiveCharacter D) : ℕ → ℂ → ℂ
  | 0 => lemma32RegularNumerator χ
  | n+1 => dslope (lemma32DividedRemainder χ n) 0

lemma lemma32_divided_remainder_differentiableOn {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (n : ℕ) :
    DifferentiableOn ℂ (lemma32DividedRemainder χ n) {w : ℂ | -1/2 < w.re} := by
  induction n with
  | zero => exact (lemma32_regular_numerator_analyticOnNhd χ hD).differentiableOn
  | succ n ih =>
    change DifferentiableOn ℂ (dslope (lemma32DividedRemainder χ n) 0) _
    exact (Complex.differentiableOn_dslope
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num))).mpr ih

lemma lemma32_divided_remainder_analyticOnNhd {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (n : ℕ) :
    AnalyticOnNhd ℂ (lemma32DividedRemainder χ n) {w : ℂ | -1/2 < w.re} :=
  (lemma32_divided_remainder_differentiableOn χ hD n).analyticOnNhd
    (isOpen_lt continuous_const Complex.continuous_re)

lemma lemma32_divided_remainder_recurrence {D : ℕ} (χ : RealPrimitiveCharacter D)
    (n : ℕ) (w : ℂ) :
    lemma32DividedRemainder χ n w = lemma32DividedRemainder χ n 0+
      w*lemma32DividedRemainder χ (n+1) w := by
  have hs := sub_smul_dslope (lemma32DividedRemainder χ n) 0 w
  simp only [sub_zero,smul_eq_mul] at hs
  change lemma32DividedRemainder χ n w = lemma32DividedRemainder χ n 0+
    w*dslope (lemma32DividedRemainder χ n) 0 w
  linear_combination -hs

lemma lemma32_regular_numerator_finite_expansion {D : ℕ} (χ : RealPrimitiveCharacter D)
    (n : ℕ) (w : ℂ) :
    lemma32RegularNumerator χ w =
      (∑ k ∈ Finset.range n, lemma32DividedRemainder χ k 0*w^k)+
        w^n*lemma32DividedRemainder χ n w := by
  induction n with
  | zero => simp [lemma32DividedRemainder]
  | succ n ih =>
    calc
      _ = (∑ k ∈ Finset.range n, lemma32DividedRemainder χ k 0*w^k)+
        w^n*lemma32DividedRemainder χ n w := ih
      _ = (∑ k ∈ Finset.range n, lemma32DividedRemainder χ k 0*w^k)+
        lemma32DividedRemainder χ n 0*w^n+w^(n+1)*lemma32DividedRemainder χ (n+1) w := by
          rw [lemma32_divided_remainder_recurrence χ n w,pow_succ]
          ring
      _ = _ := by rw [Finset.sum_range_succ]

noncomputable def lemma32PrincipalPart {D : ℕ} (χ : RealPrimitiveCharacter D) (w : ℂ) : ℂ :=
  ∑ k ∈ Finset.range 8, lemma32DividedRemainder χ k 0*w^k/w^8

lemma lemma32_actual_integrand_principal_decomposition {D : ℕ} (χ : RealPrimitiveCharacter D)
    (w : ℂ) (hw : -1/2 < w.re) (h0 : w ≠ 0) :
    lemma32CircleIntegrand χ w = lemma32PrincipalPart χ w+lemma32DividedRemainder χ 8 w := by
  have h := lemma32_regular_numerator_finite_expansion χ 8 w
  rw [lemma32_regular_numerator_eq χ w hw h0] at h
  unfold lemma32PrincipalPart
  rw [← Finset.sum_div]
  apply (mul_left_cancel₀ (pow_ne_zero 8 h0))
  field_simp
  linear_combination h

lemma lemma32_actual_regular_remainder_rectangle_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (hD : 1 < D) (a b T : ℝ) (ha : -1/2 < a) (hab : a ≤ b) (hT : 0 ≤ T) :
    lemma44GeneralRectangleBoundaryIntegral (lemma32DividedRemainder χ 8) a b T = 0 := by
  apply lemma44_local_rectangle_cauchy _ hab hT
  apply (lemma32_divided_remainder_differentiableOn χ hD 8).mono
  intro w hw
  exact lt_of_lt_of_le ha hw.1.1

end ZhangLS.Spec
