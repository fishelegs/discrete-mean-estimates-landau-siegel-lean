import ZhangLS.Spec.Lemma59ExtendedFiniteContours

/-! # Full original actual L-function quotient for Lemma 5.9

Original Psi1, actual objects, original closed boundaries and all-zero
separation are retained. The final module proves the unchanged Lemma59Target.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Complex MeasureTheory Set in
theorem lemma59_ext44_short_right_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44ReflectedPolynomialNumerator χ ψ s
      (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)))
        ((10 : ℂ) + (v : ℂ) * I) / ((10 : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp 1 * Real.exp (52 * lemma23PaperL D - lemma23PaperL D ^ 9) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL0 : 0 ≤ lemma23PaperL D := by linarith
  have hre := lemma59_ext44_omega3_re_pos hL hs
  have ha := lemma44_alpha_pos_le_one hL
  let w : ℂ := (10 : ℂ) + (v : ℂ) * I
  have hr := lemma59_ext44_truncated_shift_in_extended_gamma_region hL hs (w := w)
    (by norm_num [w]) (by simpa [w] using hv)
  have hz := lemma44ActualZtilde_norm_le_right χ ψ hD hψ hr (by simp [w]; linarith only [hre])
  simp only [lemma23PaperP, Real.log_exp] at hz
  have hzre : (s + w).re = s.re + 10 := by simp [w]
  rw [hzre] at hz
  have hf := lemma44_short_polynomial_coarse_bound χ ψ⁻¹
    (z := 1 - s - w) (by simp [w]; linarith only [hs.2.1, ha.2])
  have hb := lemma44_horizontal_scale_bound hL (show (10 : ℝ) ≤ 10 by rfl) v
  norm_num only [ofReal_ofNat] at hb
  have hg : ‖lemma57OmegaOne D w‖ ≤ Real.exp 1 := by
    change ‖lemma57OmegaOne D (((10 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ _
    rw [lemma44_Omega_norm_vertical]
    apply Real.exp_le_exp.mpr
    apply (div_le_one (by positivity : 0 < 4 * lemma23PaperL D ^ 30)).mpr
    have h6 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 6
    have h630 := pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (show 6 ≤ 30 by norm_num)
    norm_num at h6 ⊢
    nlinarith only [h6, h630, sq_nonneg v]
  have hi : ‖w‖⁻¹ ≤ 1 := by
    have hn := Complex.abs_re_le_norm w
    norm_num [w] at hn
    exact inv_le_one_of_one_le₀ (by linarith only [hn])
  unfold lemma44ReflectedPolynomialNumerator
  simp only [norm_mul, norm_inv, div_eq_mul_inv]
  calc
    _ ≤ Real.exp ((1 - 2 * (s.re + 10)) * lemma23PaperL D ^ 9) *
        Real.exp (52 * lemma23PaperL D) * Real.exp (18 * lemma23PaperL D ^ 9) * Real.exp 1 * 1 := by
      gcongr
    _ ≤ _ := by
      rw [mul_one]
      have he : Real.exp ((1 - 2 * (s.re + 10)) * lemma23PaperL D ^ 9) *
          Real.exp (52 * lemma23PaperL D) * Real.exp (18 * lemma23PaperL D ^ 9) =
          Real.exp ((-1 - 2 * s.re) * lemma23PaperL D ^ 9 + 52 * lemma23PaperL D) := by
        simp only [← Real.exp_add]
        congr 1
        ring
      rw [he, mul_comm _ (Real.exp 1)]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg 1)
      apply Real.exp_le_exp.mpr
      nlinarith only [mul_nonneg hre.le (pow_nonneg hL0 9)]

open Complex in
theorem lemma59_ext44_initial_left_gamma_region {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma59ExtendedOmega3 D s)
    {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    Lemma44InExtendedGammaRegion D (s + lemma44InitialLeftShift s v) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  apply lemma59_ext44_truncated_shift_in_extended_gamma_region hL hs
  · exact (lemma59_ext44_initial_left_shift_abs_re hL hs v).trans (by norm_num)
  · simpa using hv

open Complex in
theorem lemma59_ext44_initial_left_omega_bound {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) (v : ℝ) :
    ‖lemma57OmegaOne D (lemma44InitialLeftShift s v)‖ ≤ Real.exp 1 := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have habs := lemma59_ext44_initial_left_shift_abs_re hL hs v
  have hL1 : 1 ≤ lemma23PaperL D := by linarith
  have h30 : 9 ≤ lemma23PaperL D ^ 30 := by
    have h2 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 2
    have h230 := pow_le_pow_right₀ hL1 (show 2 ≤ 30 by norm_num)
    norm_num at h2
    exact h2.trans h230
  have hsquare : (-s.re - 1 / 2) ^ 2 ≤ 9 := by
    rw [lemma44_initial_left_shift_re] at habs
    have h := sq_le_sq₀ (abs_nonneg (-s.re - 1 / 2)) (by norm_num : (0 : ℝ) ≤ 3) |>.mpr habs
    norm_num only [sq_abs] at h
    exact h
  change ‖lemma57OmegaOne D (((-s.re - 1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)‖ ≤ _
  rw [lemma44_Omega_norm_vertical]
  apply Real.exp_le_exp.mpr
  apply (div_le_one (by positivity : 0 < 4 * lemma23PaperL D ^ 30)).mpr
  nlinarith only [hsquare, h30, sq_nonneg v]

open Complex MeasureTheory Set in
theorem lemma59_ext44_long_horizontal_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {x v : ℝ}
    (hx : -s.re - 1 / 2 ≤ x) (hx10 : |x| ≤ 10) (hx0 : x ≤ 0)
    (hv : |v| = lemma23PaperL D ^ 20) :
    ‖lemma44ReflectedPolynomialNumerator χ ψ s (lemma44LongDirichletSum χ ψ⁻¹)
      ((x : ℂ) + (v : ℂ) * I) / ((x : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  apply lemma59_ext44_reflected_horizontal_point_bound χ ψ hD hψ hs _ hx hx10 hv
    (E := 26 * lemma23PaperL D ^ 9) (H := 0)
  · apply lemma44_long_polynomial_coarse_bound χ ψ⁻¹ hL
    simp only [sub_re, one_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hs.2.1, ha.2, hx0]
  · rw [norm_exp, mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero, add_re, mul_re,
      I_re, I_im, zero_mul, add_zero, lemma44_paper_gaussian_scale_log]
    apply Real.exp_le_exp.mpr
    have hL0 : 0 ≤ lemma23PaperL D := by linarith
    exact mul_nonpos_of_nonpos_of_nonneg hx0 (by positivity)
  · have hL0 : 0 ≤ lemma23PaperL D := by linarith
    nlinarith only [hL0, pow_nonneg hL0 9]

open Complex ComplexConjugate in
theorem lemma59_ext44_middle_product_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44ActualZtilde χ ψ
        (s + (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I)) *
      lemma44LongDirichletSum χ ψ⁻¹
        (1 - s - (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I))‖ ≤
      5 * Real.exp (2 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hz := lemma59_ext44_middle_Z_norm_bound χ ψ hD hψ.1 hs hv
  have hf := lemma59_ext44_reflected_long_sum_bound χ ψ hL hψ hs hv
  rw [norm_mul]
  have hp := mul_le_mul hz hf (norm_nonneg _) (Real.exp_nonneg _)
  apply hp.trans
  have hmax : (1 / 2 - s.re + lemma44PaperAlpha D) +
      max 0 (s.re - 1 / 2 - lemma44PaperAlpha D) ≤ 2 * lemma44PaperAlpha D := by
    rcases le_total 0 (s.re - 1 / 2 - lemma44PaperAlpha D) with h | h
    · rw [max_eq_right h]
      linarith [ha.1]
    · rw [max_eq_left h]
      linarith [hs.1]
  have halpha : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
    simp only [lemma44PaperAlpha, lemma23PaperP, Real.log_exp]
    field_simp
  have he : Real.exp (2 + 2 * lemma23PaperL D ^ 9 *
      (1 / 2 - s.re + lemma44PaperAlpha D)) *
      Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (s.re - 1 / 2 - lemma44PaperAlpha D)) ≤
        Real.exp (2 + 4 * Real.pi) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hmax (by positivity : 0 ≤ lemma23PaperL D ^ 9)
    nlinarith only [hm, halpha]
  have hm := mul_le_mul_of_nonneg_right he (by positivity : 0 ≤ 5 * lemma23PaperL D ^ (-180 : ℤ))
  nlinarith only [hm]

open Complex MeasureTheory in
theorem lemma59_ext44_paper_gaussian_long_sum_on_omega3 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖lemma44GaussianLongDirichletSum χ ψ s (lemma44PaperGaussianScale D)‖ ≤
      5 * Real.exp (2 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) :=
  lemma59_ext44_gaussian_long_sum_on_omega3 χ ψ hL hψ hs
    (Real.rpow_pos_of_pos (Real.exp_pos _) _)

open Complex MeasureTheory Set in
theorem lemma59_ext44_product_horizontal_error_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖lemma44ProductHorizontalError χ ψ s (lemma44PaperGaussianScale D)
      (-s.re - 1 / 2) (lemma23PaperL D ^ 20)‖ ≤
      2097152 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hre := lemma59_ext44_omega3_re_pos hL hs
  have ha := lemma44_alpha_pos_le_one hL
  have hpoint (x : ℝ) (hx : x ∈ uIcc (-s.re - 1 / 2) 1)
      (v : ℝ) (hv : |v| = lemma23PaperL D ^ 20) :
      ‖lemma44ProductMellinNumerator χ ψ s (lemma44PaperGaussianScale D)
        ((x : ℂ) + (v : ℂ) * I) / ((x : ℂ) + (v : ℂ) * I)‖ ≤
      262144 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
    rw [uIcc_of_le (by linarith : -s.re - 1 / 2 ≤ 1)] at hx
    apply lemma59_ext44_product_horizontal_point_bound χ ψ hD hψ hs hx.1 _ hv
    apply abs_le.mpr
    constructor <;> linarith only [hx.1, hx.2, hs.2.1, ha.2]
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  have he := lemma44_horizontal_error_bound
    (fun w => lemma44ProductMellinNumerator χ ψ s (lemma44PaperGaussianScale D) w / w)
    (a := -s.re - 1 / 2) (b := 1) (T := lemma23PaperL D ^ 20)
    (K := 262144 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ)) (by positivity)
    (fun x hx => hpoint x hx _ (abs_of_nonneg hT))
    (by
      intro x hx
      simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using
        hpoint x hx (-(lemma23PaperL D ^ 20)) (by rw [abs_neg, abs_of_nonneg hT]))
  change ‖lemma44ProductHorizontalError χ ψ s (lemma44PaperGaussianScale D)
    (-s.re - 1 / 2) (lemma23PaperL D ^ 20)‖ ≤ _ at he
  apply he.trans
  have hwidth : |1 - (-s.re - 1 / 2)| ≤ 4 := by
    rw [abs_of_pos (by linarith : 0 < 1 - (-s.re - 1 / 2))]
    linarith only [hs.2.1, ha.2]
  calc
    _ ≤ 2 * (262144 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ)) * 4 :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = _ := by ring

open Complex MeasureTheory Set in
theorem lemma59_ext44_reflected_polynomial_middle_shift {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma59ExtendedOmega3 D s)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    lemma44TruncatedReflectedPolynomial χ ψ s f (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20) =
      lemma44TruncatedReflectedPolynomial χ ψ s f (-s.re - 1 / 2) (lemma23PaperL D ^ 20) +
        lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s f w / w)
          (-s.re - 1 / 2) (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have hre := lemma59_ext44_omega3_re_pos hL hs
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
  have hN := lemma59_ext44_reflected_numerator_rectangle_differentiable χ ψ hL hs f hf
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

open Complex MeasureTheory Set in
theorem lemma59_ext44_reflected_polynomial_residue_shift {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma59ExtendedOmega3 D s)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) :
    lemma44TruncatedReflectedPolynomial χ ψ s f 10 (lemma23PaperL D ^ 20) =
      lemma44ActualZtilde χ ψ s * f (1 - s) +
        lemma44TruncatedReflectedPolynomial χ ψ s f (-s.re - 1 / 2) (lemma23PaperL D ^ 20) +
          lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s f w / w)
            (-s.re - 1 / 2) 10 (lemma23PaperL D ^ 20) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have hre := lemma59_ext44_omega3_re_pos hL hs
  have ha := lemma44_alpha_pos_le_one hL
  have hT : 0 < lemma23PaperL D ^ 20 := pow_pos (by linarith) 20
  have hN := lemma59_ext44_reflected_numerator_rectangle_differentiable χ ψ hL hs f hf
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

open Complex MeasureTheory Set in
theorem lemma59_ext44_short_horizontal_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {x v : ℝ}
    (hx : -s.re - 1 / 2 ≤ x) (hx10 : |x| ≤ 10) (hv : |v| = lemma23PaperL D ^ 20) :
    ‖lemma44ReflectedPolynomialNumerator χ ψ s
      (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)))
        ((x : ℂ) + (v : ℂ) * I) / ((x : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  apply lemma59_ext44_reflected_horizontal_point_bound χ ψ hD hψ hs _ hx hx10 hv
    (E := 52 * lemma23PaperL D) (H := 18 * lemma23PaperL D ^ 9)
  · apply lemma44_short_polynomial_coarse_bound
    simp only [sub_re, one_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hs.2.1, ha.2, (abs_le.mp hx10).2]
  · exact lemma44_horizontal_scale_bound hL (abs_le.mp hx10).2 v
  · have hL0 : 0 ≤ lemma23PaperL D := by linarith
    nlinarith only [hL0, pow_nonneg hL0 9]

open Complex MeasureTheory Set in
theorem lemma59_ext44_short_right_contour_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖lemma44TruncatedReflectedPolynomial χ ψ s
      (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) 10 (lemma23PaperL D ^ 20)‖ ≤
      2 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL0 : 0 < lemma23PaperL D := by linarith
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -(lemma23PaperL D ^ 20)) (b := lemma23PaperL D ^ 20)
    (C := Real.exp 1 * Real.exp (52 * lemma23PaperL D - lemma23PaperL D ^ 9))
    (f := fun v : ℝ => lemma44ReflectedPolynomialNumerator χ ψ s
      (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)))
        ((10 : ℂ) + (v : ℂ) * I) / ((10 : ℂ) + (v : ℂ) * I) * I)
    (by
      intro v hv
      rw [uIoc_of_le (by linarith : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20)] at hv
      rw [norm_mul, norm_I, mul_one]
      exact lemma59_ext44_short_right_point_bound χ ψ hD hψ hs (abs_le.mpr ⟨hv.1.le, hv.2⟩))
  have hb : lemma23PaperL D ^ 20 * Real.exp (52 * lemma23PaperL D - lemma23PaperL D ^ 9) ≤
      lemma23PaperL D ^ (-180 : ℤ) := by
    have h9 : 6561 * lemma23PaperL D ≤ lemma23PaperL D ^ 9 := by
      have h8 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 8
      have hm := mul_le_mul_of_nonneg_right h8 hL0.le
      norm_num at hm
      nlinarith only [hm]
    apply le_trans _ (lemma44_initial_left_exponential_budget hL)
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hL0.le 20)
    apply Real.exp_le_exp.mpr
    nlinarith only [h9, hL0]
  unfold lemma44TruncatedReflectedPolynomial
  rw [norm_mul]
  apply le_trans (mul_le_mul_of_nonneg_right lemma44_mellin_normalization_norm_le_one (norm_nonneg _))
  simp only [one_mul]
  apply hi.trans
  rw [abs_of_nonneg (by linarith only [hT])]
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ 2 * Real.exp 1 by positivity)
  nlinarith only [hm]

open Complex MeasureTheory in
theorem lemma59_ext44_full_gaussian_series_approximation {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖lemma44FullGaussianSeries χ ψ s -
      lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ ≤
        (1 + 5 * Real.exp (2 * Real.pi) + lemma44InverseSquareMass) *
          lemma23PaperL D ^ (-180 : ℤ) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have hre := (lemma59_ext44_omega3_re_pos hL hs).le
  rw [lemma44_full_gaussian_series_decomposition χ ψ hD hL hre]
  have hshort := lemma44_short_smoothing_error χ ψ hD hL hre
  have hmiddle := lemma59_ext44_paper_gaussian_long_sum_on_omega3 χ ψ hL hψ hs
  have htail := (lemma44_gaussian_tail_summable_and_bound χ ψ hD hL hre).2
  calc
    _ = ‖(lemma44GaussianShortDirichletSum χ ψ s -
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s) +
          lemma44GaussianLongDirichletSum χ ψ s (lemma44PaperGaussianScale D) +
            ∑' n : ℕ, lemma44GaussianTailTerm χ ψ s n‖ := by congr 1; ring
    _ ≤ ‖lemma44GaussianShortDirichletSum χ ψ s -
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ +
          ‖lemma44GaussianLongDirichletSum χ ψ s (lemma44PaperGaussianScale D)‖ +
            ‖∑' n : ℕ, lemma44GaussianTailTerm χ ψ s n‖ := norm_add₃_le
    _ ≤ _ := by linarith only [hshort, hmiddle, htail]

open Complex in
theorem lemma59_ext44_initial_left_Z_scale_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44ActualZtilde χ ψ (s + lemma44InitialLeftShift s v)‖ *
      ‖exp (lemma44InitialLeftShift s v * (Real.log (lemma44PaperGaussianScale D) : ℂ))‖ ≤
        Real.exp (3 * lemma23PaperL D + (9 / 5 : ℝ) * Real.pi + lemma23PaperL D ^ 9 / 5) := by
  let L := lemma23PaperL D
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL0 : 0 < L := by linarith
  have hregion := lemma59_ext44_initial_left_gamma_region hL hs hv
  have hre : (s + lemma44InitialLeftShift s v).re = -1 / 2 := by simp; ring
  have hz := lemma44ActualZtilde_norm_le_left χ ψ hD hψ hregion
    (by rw [hre]; norm_num)
  rw [hre] at hz
  have hz' : ‖lemma44ActualZtilde χ ψ (s + lemma44InitialLeftShift s v)‖ ≤
      Real.exp (2 * L ^ 9 + 3 * L) := by
    convert hz using 1 <;> norm_num [lemma23PaperP, Real.log_exp, L]
  have hscale : ‖exp (lemma44InitialLeftShift s v *
      (Real.log (lemma44PaperGaussianScale D) : ℂ))‖ =
      Real.exp ((-s.re - 1 / 2) * ((9 / 5 : ℝ) * L ^ 9)) := by
    rw [norm_exp, mul_re]
    simp only [ofReal_re, ofReal_im, mul_zero, sub_zero,
      lemma44_initial_left_shift_re, lemma44_paper_gaussian_scale_log]
    rfl
  have halpha : L ^ 9 * lemma44PaperAlpha D = Real.pi := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    dsimp [L]
    field_simp
  have hgap := mul_nonneg (pow_nonneg hL0.le 9)
    (show 0 ≤ s.re - (1 / 2 - lemma44PaperAlpha D) by linarith only [hs.1])
  rw [hscale]
  calc
    _ ≤ Real.exp (2 * L ^ 9 + 3 * L) *
        Real.exp ((-s.re - 1 / 2) * ((9 / 5 : ℝ) * L ^ 9)) :=
      mul_le_mul_of_nonneg_right hz' (Real.exp_pos _).le
    _ = Real.exp (2 * L ^ 9 + 3 * L + (-s.re - 1 / 2) * ((9 / 5 : ℝ) * L ^ 9)) :=
      (Real.exp_add _ _).symm
    _ ≤ _ := Real.exp_le_exp.mpr (by nlinarith only [hgap, halpha])

end ZhangLS.Spec
