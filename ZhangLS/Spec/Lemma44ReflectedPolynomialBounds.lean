import ZhangLS.Spec.Lemma44ReflectedPolynomialContours

/-! # Quantitative errors for the short and middle reflected contours -/

namespace ZhangLS.Spec

open Complex MeasureTheory Set

set_option maxHeartbeats 1000000

theorem lemma44_horizontal_exponential_budget {D : ℕ}
    (hD : lemma23SectionFourModulusThreshold ≤ D) {A : ℝ}
    (hA : A ≤ 30 * lemma23PaperL D ^ 9 + 100 * lemma23PaperL D) :
    Real.exp (A - lemma23PaperL D ^ 10 / 4) ≤ lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hp : 1 ≤ lemma23PaperL D ^ 2000 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  apply le_trans _ (lemma44_horizontal_decay_budget (lemma44_log_large_at_threshold hD))
  calc
    _ ≤ Real.exp (30 * lemma23PaperL D ^ 9 + 100 * lemma23PaperL D - lemma23PaperL D ^ 10 / 4) :=
      Real.exp_le_exp.mpr (by linarith only [hA])
    _ ≤ _ := by
      have hm := mul_le_mul_of_nonneg_right hp
        (Real.exp_nonneg (30 * lemma23PaperL D ^ 9 + 100 * lemma23PaperL D - lemma23PaperL D ^ 10 / 4))
      simpa only [one_mul] using hm

theorem lemma44_reflected_horizontal_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) (f : ℂ → ℂ) {x v E H : ℝ}
    (hx : -s.re - 1 / 2 ≤ x) (hx10 : |x| ≤ 10) (hv : |v| = lemma23PaperL D ^ 20)
    (hf : ‖f (1 - s - ((x : ℂ) + (v : ℂ) * I))‖ ≤ Real.exp E)
    (hscale : ‖exp (((x : ℂ) + (v : ℂ) * I) *
      (Real.log (lemma44PaperGaussianScale D) : ℂ))‖ ≤ Real.exp H)
    (hbudget : E + H + 2 * lemma23PaperL D ^ 9 + 3 * lemma23PaperL D ≤
      30 * lemma23PaperL D ^ 9 + 100 * lemma23PaperL D) :
    ‖lemma44ReflectedPolynomialNumerator χ ψ s f ((x : ℂ) + (v : ℂ) * I) /
      ((x : ℂ) + (v : ℂ) * I)‖ ≤ Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  let w : ℂ := (x : ℂ) + (v : ℂ) * I
  have hr := lemma44_truncated_shift_in_extended_gamma_region hL hs
    (w := w) (by simpa [w] using hx10.trans (by norm_num : (10 : ℝ) ≤ 15))
    (by simpa [w] using hv.le)
  have hre : -1 / 2 ≤ (s + w).re := by simp [w]; linarith only [hx]
  have hz := lemma44_Z_coarse_bound χ ψ hD hψ hr hre
  have hg := lemma44_horizontal_gaussian_bound hL hx10 hv
  have hi := lemma44_horizontal_denominator_bound hL x hv
  have hb := lemma44_horizontal_exponential_budget hD hbudget
  unfold lemma44ReflectedPolynomialNumerator
  simp only [norm_mul, norm_inv, div_eq_mul_inv]
  calc
    _ ≤ Real.exp (2 * lemma23PaperL D ^ 9 + 3 * lemma23PaperL D) * Real.exp E * Real.exp H *
        (Real.exp 1 * Real.exp (-(lemma23PaperL D ^ 10 / 4))) * 1 := by gcongr
    _ = Real.exp 1 * Real.exp (E + H + 2 * lemma23PaperL D ^ 9 +
        3 * lemma23PaperL D - lemma23PaperL D ^ 10 / 4) := by
      rw [mul_one]
      have he : Real.exp (E + H + 2 * lemma23PaperL D ^ 9 +
          3 * lemma23PaperL D - lemma23PaperL D ^ 10 / 4) =
          Real.exp (2 * lemma23PaperL D ^ 9 + 3 * lemma23PaperL D) *
            Real.exp E * Real.exp H * Real.exp (-(lemma23PaperL D ^ 10 / 4)) := by
        simp only [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hb (Real.exp_nonneg 1)

theorem lemma44_short_horizontal_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {x v : ℝ}
    (hx : -s.re - 1 / 2 ≤ x) (hx10 : |x| ≤ 10) (hv : |v| = lemma23PaperL D ^ 20) :
    ‖lemma44ReflectedPolynomialNumerator χ ψ s
      (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)))
        ((x : ℂ) + (v : ℂ) * I) / ((x : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  apply lemma44_reflected_horizontal_point_bound χ ψ hD hψ hs _ hx hx10 hv
    (E := 52 * lemma23PaperL D) (H := 18 * lemma23PaperL D ^ 9)
  · apply lemma44_short_polynomial_coarse_bound
    simp only [sub_re, one_re, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hs.2.1, ha.2, (abs_le.mp hx10).2]
  · exact lemma44_horizontal_scale_bound hL (abs_le.mp hx10).2 v
  · have hL0 : 0 ≤ lemma23PaperL D := by linarith
    nlinarith only [hL0, pow_nonneg hL0 9]

theorem lemma44_long_horizontal_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {x v : ℝ}
    (hx : -s.re - 1 / 2 ≤ x) (hx10 : |x| ≤ 10) (hx0 : x ≤ 0)
    (hv : |v| = lemma23PaperL D ^ 20) :
    ‖lemma44ReflectedPolynomialNumerator χ ψ s (lemma44LongDirichletSum χ ψ⁻¹)
      ((x : ℂ) + (v : ℂ) * I) / ((x : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  apply lemma44_reflected_horizontal_point_bound χ ψ hD hψ hs _ hx hx10 hv
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

theorem lemma44_short_horizontal_error_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s
      (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) w / w)
        (-s.re - 1 / 2) 10 (lemma23PaperL D ^ 20)‖ ≤
      26 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hre := lemma44_omega3_re_pos hL hs
  have ha := lemma44_alpha_pos_le_one hL
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  have hpoint (x : ℝ) (hx : x ∈ uIcc (-s.re - 1 / 2) 10)
      (v : ℝ) (hv : |v| = lemma23PaperL D ^ 20) := by
    rw [uIcc_of_le (by linarith : -s.re - 1 / 2 ≤ 10)] at hx
    exact lemma44_short_horizontal_point_bound χ ψ hD hψ hs hx.1
      (abs_le.mpr ⟨by linarith only [hx.1, hs.2.1, ha.2], hx.2⟩) hv
  have he := lemma44_horizontal_error_bound
    (fun w => lemma44ReflectedPolynomialNumerator χ ψ s
      (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) w / w)
    (a := -s.re - 1 / 2) (b := 10) (T := lemma23PaperL D ^ 20)
    (K := Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ)) (by positivity)
    (fun x hx => hpoint x hx _ (abs_of_nonneg hT))
    (by intro x hx; simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using
      hpoint x hx (-(lemma23PaperL D ^ 20)) (by rw [abs_neg, abs_of_nonneg hT]))
  apply he.trans
  have hwidth : |10 - (-s.re - 1 / 2)| ≤ 13 := by
    rw [abs_of_pos (by linarith only [hre] : 0 < 10 - (-s.re - 1 / 2))]
    linarith only [hs.2.1, ha.2]
  calc
    _ ≤ 2 * (Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ)) * 13 :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = _ := by ring

theorem lemma44_long_horizontal_error_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
    ‖lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s
      (lemma44LongDirichletSum χ ψ⁻¹) w / w)
        (-s.re - 1 / 2) (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20)‖ ≤
      6 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hre := lemma44_omega3_re_pos hL hs
  have ha := lemma44_alpha_pos_le_one hL
  have ha4 : lemma44PaperAlpha D ≤ 1 / 4 := by
    unfold lemma44PaperAlpha lemma23PaperP
    rw [Real.log_exp]
    apply (div_le_iff₀ (pow_pos (by linarith : 0 < lemma23PaperL D) 9)).mpr
    have h3 := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hL 3
    have h39 := pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (show 3 ≤ 9 by norm_num)
    norm_num at h3
    nlinarith only [h3, h39, Real.pi_le_four]
  have hab : -s.re - 1 / 2 ≤ -lemma44PaperAlpha D := by linarith only [hs.1, ha4]
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  have hpoint (x : ℝ) (hx : x ∈ uIcc (-s.re - 1 / 2) (-lemma44PaperAlpha D))
      (v : ℝ) (hv : |v| = lemma23PaperL D ^ 20) := by
    rw [uIcc_of_le hab] at hx
    exact lemma44_long_horizontal_point_bound χ ψ hD hψ hs hx.1
      (abs_le.mpr ⟨by linarith only [hx.1, hs.2.1, ha.2], by linarith only [hx.2, ha.1]⟩)
      (by linarith only [hx.2, ha.1]) hv
  have he := lemma44_horizontal_error_bound
    (fun w => lemma44ReflectedPolynomialNumerator χ ψ s (lemma44LongDirichletSum χ ψ⁻¹) w / w)
    (a := -s.re - 1 / 2) (b := -lemma44PaperAlpha D) (T := lemma23PaperL D ^ 20)
    (K := Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ)) (by positivity)
    (fun x hx => hpoint x hx _ (abs_of_nonneg hT))
    (by intro x hx; simpa only [ofReal_neg, neg_mul, sub_eq_add_neg] using
      hpoint x hx (-(lemma23PaperL D ^ 20)) (by rw [abs_neg, abs_of_nonneg hT]))
  apply he.trans
  have hwidth : |-lemma44PaperAlpha D - (-s.re - 1 / 2)| ≤ 3 := by
    rw [abs_of_nonneg (by linarith only [hab])]
    linarith only [hs.2.1, ha.1, ha.2]
  calc
    _ ≤ 2 * (Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ)) * 3 :=
      mul_le_mul_of_nonneg_left hwidth (by positivity)
    _ = _ := by ring

theorem lemma44_short_right_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44ReflectedPolynomialNumerator χ ψ s
      (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)))
        ((10 : ℂ) + (v : ℂ) * I) / ((10 : ℂ) + (v : ℂ) * I)‖ ≤
      Real.exp 1 * Real.exp (52 * lemma23PaperL D - lemma23PaperL D ^ 9) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL0 : 0 ≤ lemma23PaperL D := by linarith
  have hre := lemma44_omega3_re_pos hL hs
  have ha := lemma44_alpha_pos_le_one hL
  let w : ℂ := (10 : ℂ) + (v : ℂ) * I
  have hr := lemma44_truncated_shift_in_extended_gamma_region hL hs (w := w)
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

theorem lemma44_short_right_contour_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) :
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
      exact lemma44_short_right_point_bound χ ψ hD hψ hs (abs_le.mpr ⟨hv.1.le, hv.2⟩))
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

end ZhangLS.Spec
