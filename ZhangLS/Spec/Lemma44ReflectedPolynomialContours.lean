import ZhangLS.Spec.Lemma44PolynomialGrowth
import ZhangLS.Spec.Lemma44HorizontalIntegrals

/-!
# The actual finite reflected polynomial contours

The short contour crosses the pole at zero; the middle contour remains
strictly to its left. Both exact identities use only local analyticity.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

noncomputable def lemma44ReflectedPolynomialNumerator {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (f : ℂ → ℂ) (w : ℂ) : ℂ :=
  lemma44ActualZtilde χ ψ (s + w) * f (1 - s - w) *
    exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ)) * lemma57OmegaOne D w

noncomputable def lemma44TruncatedReflectedPolynomial {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (f : ℂ → ℂ) (σ T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ v : ℝ in -T..T,
      lemma44ReflectedPolynomialNumerator χ ψ s f ((σ : ℂ) + (v : ℂ) * I) /
        ((σ : ℂ) + (v : ℂ) * I) * I)

theorem lemma44_reflected_numerator_differentiableAt {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) {w : ℂ} (him : (s + w).im ≠ 0) :
    DifferentiableAt ℂ (lemma44ReflectedPolynomialNumerator χ ψ s f) w := by
  have hZ : DifferentiableAt ℂ (fun z => lemma44ActualZtilde χ ψ (s + z)) w :=
    (lemma44ActualZtilde_differentiableAt χ ψ him).comp w (by fun_prop)
  have hF : DifferentiableAt ℂ (fun z => f (1 - s - z)) w := (hf _).comp w (by fun_prop)
  unfold lemma44ReflectedPolynomialNumerator lemma57OmegaOne
  fun_prop

theorem lemma44_reflected_numerator_rectangle_differentiable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma44InOmega3 D s)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) {a b : ℝ} (ha : -3 ≤ a) (hb : b ≤ 10) :
    DifferentiableOn ℂ (lemma44ReflectedPolynomialNumerator χ ψ s f)
      (lemma44ClosedRectangle a b (lemma23PaperL D ^ 20)) := by
  intro w hw
  have hwr : |w.re| ≤ 15 := by
    have hr := hw.1
    apply abs_le.mpr
    constructor <;> linarith only [hr.1, hr.2, ha, hb]
  have hwi : |w.im| ≤ lemma23PaperL D ^ 20 := abs_le.mpr hw.2
  have hregion := lemma44_truncated_shift_in_extended_gamma_region hL hs hwr hwi
  exact (lemma44_reflected_numerator_differentiableAt χ ψ s f hf
    (ne_of_gt (lemma44_extended_gamma_region_height hL hregion).2.2.1)).differentiableWithinAt

theorem lemma44_reflected_polynomial_intervalIntegrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma44InOmega3 D s)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) {σ : ℝ} (hσ : |σ| ≤ 15) (hσ0 : σ ≠ 0) :
    IntervalIntegrable (fun v : ℝ =>
      lemma44ReflectedPolynomialNumerator χ ψ s f ((σ : ℂ) + (v : ℂ) * I) /
        ((σ : ℂ) + (v : ℂ) * I)) volume
      (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) := by
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20)]
  intro v hv
  let w : ℂ := (σ : ℂ) + (v : ℂ) * I
  have hr := lemma44_truncated_shift_in_extended_gamma_region hL hs (w := w)
    (by simpa [w] using hσ) (by simpa [w] using abs_le.mpr hv)
  have hd := lemma44_reflected_numerator_differentiableAt χ ψ s f hf
    (ne_of_gt (lemma44_extended_gamma_region_height hL hr).2.2.1)
  have hc : ContinuousAt (fun u : ℝ => lemma44ReflectedPolynomialNumerator χ ψ s f
      ((σ : ℂ) + (u : ℂ) * I)) v := hd.continuousAt.comp
        (f := fun u : ℝ => (σ : ℂ) + (u : ℂ) * I) (by fun_prop)
  apply (hc.div (by fun_prop) _).continuousWithinAt
  intro he
  have hre := congrArg Complex.re he
  simp at hre
  exact hσ0 hre

theorem lemma44_reflected_polynomial_residue_shift {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma44InOmega3 D s)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    lemma44TruncatedReflectedPolynomial χ ψ s f 10 (lemma23PaperL D ^ 20) =
      lemma44ActualZtilde χ ψ s * f (1 - s) +
        lemma44TruncatedReflectedPolynomial χ ψ s f (-s.re - 1 / 2) (lemma23PaperL D ^ 20) +
          lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s f w / w)
            (-s.re - 1 / 2) 10 (lemma23PaperL D ^ 20) := by
  have hre := lemma44_omega3_re_pos hL hs
  have ha := lemma44_alpha_pos_le_one hL
  have hT : 0 < lemma23PaperL D ^ 20 := pow_pos (by linarith) 20
  have hN := lemma44_reflected_numerator_rectangle_differentiable χ ψ hL hs f hf
    (a := -s.re - 1 / 2) (b := 10) (by linarith only [hs.2.1, ha.2]) (by rfl)
  have hres := lemma44_local_simple_pole_rectangle _
    (show -s.re - 1 / 2 ≤ -1 / 2 by linarith only [hre]) (by norm_num : (1 : ℝ) ≤ 10) hT hN
  have hzero : lemma44ReflectedPolynomialNumerator χ ψ s f 0 =
      lemma44ActualZtilde χ ψ s * f (1 - s) := by
    simp [lemma44ReflectedPolynomialNumerator, lemma57OmegaOne]
  rw [hzero] at hres
  unfold lemma44TruncatedReflectedPolynomial lemma44HorizontalError
  simp_rw [intervalIntegral.integral_mul_const]
  field_simp [two_pi_I_ne_zero]
  unfold lemma44GeneralRectangleBoundaryIntegral at hres
  ring_nf at hres ⊢
  simp only [sub_eq_add_neg, add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc] at hres ⊢
  linear_combination hres

theorem lemma44_reflected_polynomial_middle_shift {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma44InOmega3 D s)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    lemma44TruncatedReflectedPolynomial χ ψ s f (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20) =
      lemma44TruncatedReflectedPolynomial χ ψ s f (-s.re - 1 / 2) (lemma23PaperL D ^ 20) +
        lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s f w / w)
          (-s.re - 1 / 2) (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20) := by
  have hre := lemma44_omega3_re_pos hL hs
  have ha := lemma44_alpha_pos_le_one hL
  have hab : -s.re - 1 / 2 ≤ -lemma44PaperAlpha D := by
    have hL0 : 0 < lemma23PaperL D := by linarith
    have hL1 : 1 ≤ lemma23PaperL D := by linarith
    have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 3
    have h39 := pow_le_pow_right₀ hL1 (show 3 ≤ 9 by norm_num)
    have ha4 : lemma44PaperAlpha D ≤ 1 / 4 := by
      unfold lemma44PaperAlpha lemma23PaperP
      rw [Real.log_exp]
      apply (div_le_iff₀ (pow_pos hL0 9)).mpr
      norm_num at h3
      nlinarith only [h3, h39, Real.pi_le_four]
    linarith only [hre, ha4]
  have hN := lemma44_reflected_numerator_rectangle_differentiable χ ψ hL hs f hf
    (a := -s.re - 1 / 2) (b := -lemma44PaperAlpha D)
    (by linarith only [hs.2.1, ha.2]) (by linarith only [ha.1])
  have hc := lemma44_local_rectangle_cauchy
    (fun w => lemma44ReflectedPolynomialNumerator χ ψ s f w / w)
    hab (by positivity : 0 ≤ lemma23PaperL D ^ 20) (by
      intro w hw
      have hwr : w.re ≤ -lemma44PaperAlpha D := hw.1.2
      have hw0 : w ≠ 0 := by
        intro he
        rw [he] at hwr
        simp only [zero_re] at hwr
        linarith only [hwr, ha.1]
      exact (hN w hw).div differentiableWithinAt_id hw0)
  unfold lemma44TruncatedReflectedPolynomial lemma44HorizontalError
  simp_rw [intervalIntegral.integral_mul_const]
  field_simp [two_pi_I_ne_zero]
  unfold lemma44GeneralRectangleBoundaryIntegral at hc
  ring_nf at hc ⊢
  simp only [sub_eq_add_neg, add_comm, add_left_comm, mul_comm, mul_left_comm, mul_assoc] at hc ⊢
  linear_combination hc

end ZhangLS.Spec
