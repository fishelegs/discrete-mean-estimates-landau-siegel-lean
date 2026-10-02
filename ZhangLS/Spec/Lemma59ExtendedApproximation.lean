import ZhangLS.Spec.Lemma59ExtendedContourBudgets

/-! # Full original actual L-function quotient for Lemma 5.9

Original Psi1, actual objects, original closed boundaries and all-zero
separation are retained. The final module proves the unchanged Lemma59Target.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Complex MeasureTheory in
private theorem lemma59_ext44_norm_eight_terms (a b c d e f g h : ℂ) :
    ‖a - b - c - d + e + f - g - h‖ ≤
      ‖a‖ + ‖b‖ + ‖c‖ + ‖d‖ + ‖e‖ + ‖f‖ + ‖g‖ + ‖h‖ := by
  calc
    _ ≤ ‖a - b - c - d + e + f - g‖ + ‖h‖ := norm_sub_le _ _
    _ ≤ (‖a - b - c - d + e + f‖ + ‖g‖) + ‖h‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ ((‖a - b - c - d + e‖ + ‖f‖) + ‖g‖) + ‖h‖ := by gcongr; exact norm_add_le _ _
    _ ≤ (((‖a - b - c - d‖ + ‖e‖) + ‖f‖) + ‖g‖) + ‖h‖ := by gcongr; exact norm_add_le _ _
    _ ≤ ((((‖a - b - c‖ + ‖d‖) + ‖e‖) + ‖f‖) + ‖g‖) + ‖h‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ (((((‖a - b‖ + ‖c‖) + ‖d‖) + ‖e‖) + ‖f‖) + ‖g‖) + ‖h‖ := by gcongr; exact norm_sub_le _ _
    _ ≤ _ := by gcongr; exact norm_sub_le _ _

open Complex MeasureTheory Set in
theorem lemma59_ext44_long_horizontal_error_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s
      (lemma44LongDirichletSum χ ψ⁻¹) w / w)
        (-s.re - 1 / 2) (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20)‖ ≤
      6 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hre := lemma59_ext44_omega3_re_pos hL hs
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
    exact lemma59_ext44_long_horizontal_point_bound χ ψ hD hψ hs hx.1
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

open Complex MeasureTheory Set in
theorem lemma59_ext44_middle_integrand_norm_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44MiddleContourIntegrand χ ψ s v‖ ≤
      (5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ)) *
        ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖⁻¹ := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  have hprod := lemma59_ext44_middle_product_bound χ ψ hD hψ hs hv
  have hlogB : 0 ≤ Real.log (lemma44PaperGaussianScale D) := by
    have hP : 0 < lemma23PaperP D := Real.exp_pos _
    rw [lemma44PaperGaussianScale, Real.log_rpow hP, lemma23PaperP, Real.log_exp]
    positivity
  have hpower : ‖Complex.exp ((-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I) *
      (Real.log (lemma44PaperGaussianScale D) : ℂ))‖ ≤ 1 := by
    rw [Complex.norm_exp]
    apply Real.exp_le_one_iff.mpr
    simp only [Complex.mul_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.1.le) hlogB
  have homega : ‖lemma57OmegaOne D (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I)‖ ≤
      Real.exp 1 := by
    have h := lemma44_Omega_norm_vertical D (-lemma44PaperAlpha D) v
    simp only [Complex.ofReal_neg, neg_sq] at h
    rw [h]
    apply Real.exp_le_exp.mpr
    apply (div_le_iff₀ (by positivity : 0 < 4 * lemma23PaperL D ^ 30)).mpr
    have hp : 1 ≤ lemma23PaperL D ^ 30 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
    nlinarith only [ha.1, ha.2, hp, sq_nonneg v]
  dsimp only [lemma44MiddleContourIntegrand]
  rw [norm_div, norm_mul, norm_mul]
  have hm := mul_le_mul (mul_le_mul hprod hpower (norm_nonneg _) (by positivity)) homega
    (norm_nonneg _) (by positivity)
  have hc : (5 * Real.exp (2 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) * 1) *
      Real.exp 1 = 5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) := by
    rw [show (5 * Real.exp (2 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) * 1) *
      Real.exp 1 = 5 * (Real.exp (2 + 4 * Real.pi) * Real.exp 1) *
        lemma23PaperL D ^ (-180 : ℤ) by ring, ← Real.exp_add]
    rw [show 2 + 4 * Real.pi + 1 = 3 + 4 * Real.pi by ring]
  rw [hc] at hm
  have hd := div_le_div_of_nonneg_right hm
    (norm_nonneg (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I))
  simpa only [div_eq_mul_inv] using hd

open Complex MeasureTheory in
theorem lemma59_ext44_reflected_tail_contour_continuousOn {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ContinuousOn (lemma44ReflectedTailContourIntegrand χ ψ s)
      (Set.Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hshift : Continuous (fun v : ℝ => lemma44InitialLeftShift s v) := by
    unfold lemma44InitialLeftShift
    fun_prop
  have hz : ContinuousOn (fun v : ℝ => lemma44ActualZtilde χ ψ (s + lemma44InitialLeftShift s v))
      (Set.Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)) := by
    intro v hv
    have hr := lemma59_ext44_initial_left_gamma_region hL hs (abs_le.mpr hv)
    have him := (lemma44_extended_gamma_region_height hL hr).2.2.1
    have hc : Continuous (fun v : ℝ => s + lemma44InitialLeftShift s v) :=
      continuous_const.add hshift
    exact (ContinuousAt.comp (f := fun v : ℝ => s + lemma44InitialLeftShift s v)
      (lemma44ActualZtilde_differentiableAt χ ψ him.ne').continuousAt
      hc.continuousAt).continuousWithinAt
  have htail := lemma44_reflected_tail_vertical_continuous χ ψ⁻¹ s
  have hB : Continuous (fun v : ℝ => exp (lemma44InitialLeftShift s v *
      (Real.log (lemma44PaperGaussianScale D) : ℂ))) := by fun_prop
  have hO : Continuous (fun v : ℝ => lemma57OmegaOne D (lemma44InitialLeftShift s v)) := by
    unfold lemma57OmegaOne
    fun_prop
  have hne : ∀ v ∈ Set.Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20),
      lemma44InitialLeftShift s v ≠ 0 := by
    intro v _hv he
    have hre := congrArg Complex.re he
    simp only [lemma44_initial_left_shift_re, zero_re] at hre
    linarith [lemma59_ext44_omega3_re_pos hL hs]
  exact (((hz.mul htail.continuousOn).mul hB.continuousOn).mul hO.continuousOn).div₀
    hshift.continuousOn hne

open Complex MeasureTheory Set in
theorem lemma59_ext44_short_horizontal_error_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s
      (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))) w / w)
        (-s.re - 1 / 2) 10 (lemma23PaperL D ^ 20)‖ ≤
      26 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hre := lemma59_ext44_omega3_re_pos hL hs
  have ha := lemma44_alpha_pos_le_one hL
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  have hpoint (x : ℝ) (hx : x ∈ uIcc (-s.re - 1 / 2) 10)
      (v : ℝ) (hv : |v| = lemma23PaperL D ^ 20) := by
    rw [uIcc_of_le (by linarith : -s.re - 1 / 2 ≤ 10)] at hx
    exact lemma59_ext44_short_horizontal_point_bound χ ψ hD hψ hs hx.1
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

open Complex MeasureTheory in
theorem lemma59_ext44_reflected_tail_contour_intervalIntegrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    IntervalIntegrable (lemma44ReflectedTailContourIntegrand χ ψ s) volume
      (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) := by
  have horder : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20 := by
    have hp : 0 ≤ lemma23PaperL D ^ 20 := by positivity
    linarith
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le horder]
  exact lemma59_ext44_reflected_tail_contour_continuousOn χ ψ hD hs

open Complex MeasureTheory in
theorem lemma59_ext44_reflected_tail_contour_pointwise_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44ReflectedTailContourIntegrand χ ψ s v‖ ≤
      2 * lemma44DivisorSeriesMass *
        Real.exp (3 * lemma23PaperL D + 1 + (9 / 5 : ℝ) * Real.pi -
          (3 / 10 : ℝ) * lemma23PaperL D ^ 9) := by
  let L := lemma23PaperL D
  let w := lemma44InitialLeftShift s v
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hz := lemma59_ext44_initial_left_Z_scale_bound χ ψ hD hψ hs hv
  have ho := lemma59_ext44_initial_left_omega_bound hL hs v
  have hd := lemma59_ext44_initial_left_denominator_bound hL hs v
  have ht := (lemma44_reflected_tail_summable_and_bound χ ψ⁻¹
    (z := 1 - s - w) (by simp [w, lemma44InitialLeftShift]; ring)).2
  have hm := lemma44_divisor_series_mass_nonneg
  unfold lemma44ReflectedTailContourIntegrand
  change ‖lemma44ActualZtilde χ ψ (s + w) *
    (∑' n : ℕ, lemma44ReflectedTailTerm χ ψ⁻¹ (1 - s - w) n) *
      exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ)) * lemma57OmegaOne D w / w‖ ≤ _
  calc
    _ = (‖lemma44ActualZtilde χ ψ (s + w)‖ *
        ‖exp (w * (Real.log (lemma44PaperGaussianScale D) : ℂ))‖) *
        ‖∑' n : ℕ, lemma44ReflectedTailTerm χ ψ⁻¹ (1 - s - w) n‖ *
          ‖lemma57OmegaOne D w‖ * ‖w‖⁻¹ := by
      simp only [norm_mul, norm_inv, div_eq_mul_inv]
      ring
    _ ≤ Real.exp (3 * L + (9 / 5 : ℝ) * Real.pi + L ^ 9 / 5) *
        (lemma44DivisorSeriesMass * Real.exp (-(L ^ 9) / 2)) * Real.exp 1 * 2 := by
      gcongr
    _ = _ := by
      calc
        _ = 2 * lemma44DivisorSeriesMass *
          (Real.exp (3 * L + (9 / 5 : ℝ) * Real.pi + L ^ 9 / 5) *
            Real.exp (-(L ^ 9) / 2) * Real.exp 1) := by ring
        _ = _ := by
          rw [← Real.exp_add, ← Real.exp_add]
          congr 2
          ring

open Complex MeasureTheory in
theorem lemma59_ext44_right_mellin_approximation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ t : ℝ, lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 t * I) -
        lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s‖ ≤
      (1 + 5 * Real.exp (2 * Real.pi) + lemma44InverseSquareMass) *
        lemma23PaperL D ^ (-180 : ℤ) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have hm := (lemma44_product_gaussian_mellin_identity χ ψ s hD
    (B := lemma44PaperGaussianScale D)
    (Real.rpow_pos_of_pos (Real.exp_pos _) _) zero_lt_one
      (by linarith [lemma59_ext44_omega3_re_pos hL hs])).2.2
  rw [hm]
  exact lemma59_ext44_full_gaussian_series_approximation χ ψ hD hL hψ hs

open Complex MeasureTheory Set in
theorem lemma59_ext44_truncated_middle_contour_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (∫ v : ℝ in Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20),
        lemma44MiddleContourIntegrand χ ψ s v * Complex.I)‖ ≤
      5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-179 : ℤ) := by
  let C := 5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ)
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hdc : Continuous (fun v : ℝ =>
      ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖⁻¹) := by
    have hc : Continuous (fun v : ℝ =>
        ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖) := by fun_prop
    apply hc.inv₀
    intro v
    apply norm_ne_zero_iff.mpr
    intro h
    have hr := congrArg Complex.re h
    simp at hr
    exact ha.1.ne' hr
  have hm : IntegrableOn (fun v : ℝ => C *
      ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖⁻¹)
      (Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)) :=
    (hdc.const_mul C).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hb : ∀ᵐ v : ℝ ∂volume.restrict
      (Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)),
      ‖lemma44MiddleContourIntegrand χ ψ s v * Complex.I‖ ≤
        C * ‖-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I‖⁻¹ := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with v hv
    rw [norm_mul, Complex.norm_I, mul_one]
    exact lemma59_ext44_middle_integrand_norm_bound χ ψ hD hψ hs (abs_le.mpr ⟨hv.1.le, hv.2⟩)
  have hi := norm_integral_le_of_norm_le hm hb
  rw [integral_const_mul] at hi
  have hbudget := mul_le_mul_of_nonneg_left (lemma44_middle_denominator_budget hD) hC
  have hn : ‖(2 * (Real.pi : ℂ) * Complex.I)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, norm_mul, Complex.norm_I, mul_one]
    norm_num [Complex.norm_of_nonneg Real.pi_pos.le]
    have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.one_le_pi_div_two]
    have h := inv_le_one_of_one_le₀ hpi
    rw [abs_of_pos Real.pi_pos]
    convert h using 1
    ring
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∫ v : ℝ in Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20),
        lemma44MiddleContourIntegrand χ ψ s v * Complex.I‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ ≤ C * lemma23PaperL D := by simpa only [one_mul] using hi.trans hbudget
    _ = _ := by
      have hpow : lemma23PaperL D ^ (-180 : ℤ) * lemma23PaperL D =
          lemma23PaperL D ^ (-179 : ℤ) := by
        calc
          _ = lemma23PaperL D ^ (-180 : ℤ) * lemma23PaperL D ^ (1 : ℤ) := by rw [zpow_one]
          _ = _ := by
            rw [← zpow_add₀ (by linarith : lemma23PaperL D ≠ 0)]
            norm_num
      dsimp [C]
      rw [mul_assoc, hpow]

open Complex MeasureTheory Set in
theorem lemma59_ext44_left_product_contour_decomposition {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    lemma44TruncatedProductMellin χ ψ s (lemma44PaperGaussianScale D)
      (-s.re - 1 / 2) (lemma23PaperL D ^ 20) =
      lemma44TruncatedReflectedPolynomial χ ψ s
        (lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)))
          (-s.re - 1 / 2) (lemma23PaperL D ^ 20) +
        lemma44TruncatedReflectedPolynomial χ ψ s (lemma44LongDirichletSum χ ψ⁻¹)
          (-s.re - 1 / 2) (lemma23PaperL D ^ 20) +
        (2 * (Real.pi : ℂ) * I)⁻¹ *
          (∫ v : ℝ in -(lemma23PaperL D ^ 20)..lemma23PaperL D ^ 20,
            lemma44ReflectedTailContourIntegrand χ ψ s v * I) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hre := lemma59_ext44_omega3_re_pos hL hs
  have hσ := (lemma59_ext44_initial_left_shift_abs_re hL hs 0).trans (by norm_num : (3 : ℝ) ≤ 15)
  simp only [lemma44_initial_left_shift_re] at hσ
  have hσ0 : -s.re - 1 / 2 ≠ 0 := by linarith only [hre]
  let short := lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))
  let middle := lemma44LongDirichletSum χ ψ⁻¹
  have hshort := (lemma59_ext44_reflected_polynomial_intervalIntegrable χ ψ hL hs short
    (lemma44_short_polynomial_differentiable χ ψ⁻¹) hσ hσ0).mul_const I
  have hmiddle := (lemma59_ext44_reflected_polynomial_intervalIntegrable χ ψ hL hs middle
    (lemma44_long_polynomial_differentiable χ ψ⁻¹) hσ hσ0).mul_const I
  have htail := (lemma59_ext44_reflected_tail_contour_intervalIntegrable χ ψ hD hs).mul_const I
  have hpoint (v : ℝ) (hv : |v| ≤ lemma23PaperL D ^ 20) :
      lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) (-s.re - 1 / 2) v * I =
        lemma44ReflectedPolynomialNumerator χ ψ s short (lemma44InitialLeftShift s v) /
          lemma44InitialLeftShift s v * I +
        lemma44ReflectedPolynomialNumerator χ ψ s middle (lemma44InitialLeftShift s v) /
          lemma44InitialLeftShift s v * I + lemma44ReflectedTailContourIntegrand χ ψ s v * I := by
    have hfe := lemma59_ext44_left_product_mellin_eq_reflected_series χ ψ hL hψ hs
      (lemma44PaperGaussianScale D) hv
    have hmir : (1 - s - lemma44InitialLeftShift s v).re = 3 / 2 := by simp; ring
    have hsplit := lemma44_reflected_series_decomposition χ ψ⁻¹ hL hmir
    change lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D)
      (-s.re - 1 / 2) v = _ at hfe
    rw [hfe]
    change _ = _ at hsplit
    change (lemma44ActualZtilde χ ψ (s + lemma44InitialLeftShift s v) *
      LSeries (fun n => lemma23NuArithmeticFunction χ n * ψ⁻¹ (n : ZMod p))
        (1 - s - lemma44InitialLeftShift s v) *
        exp (lemma44InitialLeftShift s v * (Real.log (lemma44PaperGaussianScale D) : ℂ)) *
        lemma57OmegaOne D (lemma44InitialLeftShift s v) / lemma44InitialLeftShift s v) * I = _
    rw [hsplit]
    unfold lemma44ReflectedPolynomialNumerator lemma44ReflectedTailContourIntegrand
    dsimp only [short, middle]
    ring
  unfold lemma44TruncatedProductMellin lemma44TruncatedReflectedPolynomial
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  have he : (∫ v : ℝ in -(lemma23PaperL D ^ 20)..lemma23PaperL D ^ 20,
      lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) (-s.re - 1 / 2) v * I) =
      ∫ v : ℝ in -(lemma23PaperL D ^ 20)..lemma23PaperL D ^ 20,
        ((lemma44ReflectedPolynomialNumerator χ ψ s short (lemma44InitialLeftShift s v) /
          lemma44InitialLeftShift s v * I +
        lemma44ReflectedPolynomialNumerator χ ψ s middle (lemma44InitialLeftShift s v) /
          lemma44InitialLeftShift s v * I) + lemma44ReflectedTailContourIntegrand χ ψ s v * I) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [uIcc_of_le (by linarith : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20)] at hv
    exact hpoint v (abs_le.mpr hv)
  rw [he]
  dsimp only [lemma44InitialLeftShift]
  rw [intervalIntegral.integral_add (hshort.add hmiddle) htail,
    intervalIntegral.integral_add hshort hmiddle]
  dsimp only [short, middle]
  ring

open Complex MeasureTheory Set in
theorem lemma59_ext44_middle_reflected_polynomial_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖lemma44TruncatedReflectedPolynomial χ ψ s (lemma44LongDirichletSum χ ψ⁻¹)
      (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20)‖ ≤
      5 * Real.exp (3 + 4 * Real.pi) * lemma23PaperL D ^ (-179 : ℤ) := by
  have h := lemma59_ext44_truncated_middle_contour_bound χ ψ hD hψ hs
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  unfold lemma44TruncatedReflectedPolynomial lemma44ReflectedPolynomialNumerator
  rw [intervalIntegral.integral_of_le (by linarith : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20)]
  simpa only [ofReal_neg, lemma44MiddleContourIntegrand] using h

open Complex MeasureTheory in
theorem lemma59_ext44_reflected_tail_contour_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..lemma23PaperL D ^ 20,
        lemma44ReflectedTailContourIntegrand χ ψ s v * I)‖ ≤
      (4 * lemma44DivisorSeriesMass * Real.exp (1 + (9 / 5 : ℝ) * Real.pi)) *
        lemma23PaperL D ^ (-180 : ℤ) := by
  let L := lemma23PaperL D
  let C := 2 * lemma44DivisorSeriesMass *
    Real.exp (3 * L + 1 + (9 / 5 : ℝ) * Real.pi - (3 / 10 : ℝ) * L ^ 9)
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hm := lemma44_divisor_series_mass_nonneg
  have hT : 0 ≤ L ^ 20 := by positivity
  have hlen : |L ^ 20 - -(L ^ 20)| = 2 * L ^ 20 := by
    rw [abs_of_nonneg (by linarith only [hT])]
    ring
  have hi : ‖∫ v : ℝ in -(L ^ 20)..L ^ 20,
      lemma44ReflectedTailContourIntegrand χ ψ s v * I‖ ≤ C * (2 * L ^ 20) := by
    apply (intervalIntegral.norm_integral_le_of_norm_le_const ?_).trans_eq
      (congrArg (fun r : ℝ => C * r) hlen)
    intro v hv
    rw [Set.uIoc_of_le (by linarith only [hT] : -(L ^ 20) ≤ L ^ 20)] at hv
    rw [norm_mul, norm_I, mul_one]
    exact lemma59_ext44_reflected_tail_contour_pointwise_bound χ ψ hD hψ hs
      (abs_le.mpr ⟨hv.1.le, hv.2⟩)
  have hn : ‖(2 * (Real.pi : ℂ) * I)⁻¹‖ ≤ 1 := by
    rw [norm_inv, norm_mul, norm_mul, norm_I, mul_one]
    norm_num [Complex.norm_of_nonneg Real.pi_pos.le]
    have hpi : 1 ≤ 2 * Real.pi := by linarith only [Real.one_le_pi_div_two]
    have h := inv_le_one_of_one_le₀ hpi
    rw [abs_of_pos Real.pi_pos]
    convert h using 1
    ring
  rw [norm_mul]
  calc
    _ ≤ 1 * ‖∫ v : ℝ in -(L ^ 20)..L ^ 20,
        lemma44ReflectedTailContourIntegrand χ ψ s v * I‖ :=
      mul_le_mul_of_nonneg_right hn (norm_nonneg _)
    _ ≤ C * (2 * L ^ 20) := by simpa only [one_mul] using hi
    _ = (4 * lemma44DivisorSeriesMass * Real.exp (1 + (9 / 5 : ℝ) * Real.pi)) *
        (L ^ 20 * Real.exp (3 * L - (3 / 10 : ℝ) * L ^ 9)) := by
      dsimp [C]
      have he : Real.exp (3 * L + 1 + (9 / 5 : ℝ) * Real.pi - (3 / 10 : ℝ) * L ^ 9) =
          Real.exp (1 + (9 / 5 : ℝ) * Real.pi) * Real.exp (3 * L - (3 / 10 : ℝ) * L ^ 9) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (lemma44_initial_left_exponential_budget hL) (by positivity)

open Complex MeasureTheory in
theorem lemma59_ext44_actual_approximate_functional_equation {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    ‖DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
      (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s +
        lemma44ActualZtilde χ ψ s *
          lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s))‖ ≤
      lemma44ErrorConstant * lemma23PaperL D ^ (-179 : ℤ) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hT : 0 < lemma23PaperL D ^ 20 := pow_pos (by linarith) 20
  let F := lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s
  let f := lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p))
  let m := lemma44LongDirichletSum χ ψ⁻¹
  let R := (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ v : ℝ, lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 v * I)
  let Rt := lemma44TruncatedProductMellin χ ψ s (lemma44PaperGaussianScale D) 1 (lemma23PaperL D ^ 20)
  let Sr := lemma44TruncatedReflectedPolynomial χ ψ s f 10 (lemma23PaperL D ^ 20)
  let Mr := lemma44TruncatedReflectedPolynomial χ ψ s m (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20)
  let Hs := lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s f w / w)
    (-s.re - 1 / 2) 10 (lemma23PaperL D ^ 20)
  let Hm := lemma44HorizontalError (fun w => lemma44ReflectedPolynomialNumerator χ ψ s m w / w)
    (-s.re - 1 / 2) (-lemma44PaperAlpha D) (lemma23PaperL D ^ 20)
  let Tail := (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ v : ℝ in -(lemma23PaperL D ^ 20)..lemma23PaperL D ^ 20,
      lemma44ReflectedTailContourIntegrand χ ψ s v * I)
  let Hp := lemma44ProductHorizontalError χ ψ s (lemma44PaperGaussianScale D)
    (-s.re - 1 / 2) (lemma23PaperL D ^ 20)
  have hprod := lemma59_ext44_product_finite_shift χ ψ hL hψ.1 hs (lemma44PaperGaussianScale D) hT
  have hleft := lemma59_ext44_left_product_contour_decomposition χ ψ hD hψ.1 hs
  have hshort := lemma59_ext44_reflected_polynomial_residue_shift χ ψ hL hs f
    (lemma44_short_polynomial_differentiable χ ψ⁻¹)
  have hmiddle := lemma59_ext44_reflected_polynomial_middle_shift χ ψ hL hs m
    (lemma44_long_polynomial_differentiable χ ψ⁻¹)
  have he : DirichletCharacter.LFunction ψ s *
      DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
        (F + lemma44ActualZtilde χ ψ s * f (1 - s)) =
      (R - F) - (R - Rt) - Sr - Mr + Hs + Hm - Tail - Hp := by
    dsimp only [F, R, Rt, Sr, Mr, Hs, Hm, Tail, Hp, f, m] at *
    linear_combination -hprod - hleft + hshort + hmiddle
  have hR := lemma59_ext44_right_mellin_approximation χ ψ
    (lemma44_modulus_one_lt_at_threshold χ hD) hL hψ hs
  have hRt := lemma59_ext44_right_vertical_truncation_bound χ ψ hD hs
  have hSr := lemma59_ext44_short_right_contour_bound χ ψ hD hψ.1 hs
  have hMr := lemma59_ext44_middle_reflected_polynomial_bound χ ψ hD hψ hs
  have hHs := lemma59_ext44_short_horizontal_error_bound χ ψ hD hψ.1 hs
  have hHm := lemma59_ext44_long_horizontal_error_bound χ ψ hD hψ.1 hs
  have hTail := lemma59_ext44_reflected_tail_contour_bound χ ψ hD hψ.1 hs
  have hHp := lemma59_ext44_product_horizontal_error_bound χ ψ hD hψ.1 hs
  change ‖R - F‖ ≤ _ at hR
  change ‖R - Rt‖ ≤ _ at hRt
  change ‖Sr‖ ≤ _ at hSr
  change ‖Mr‖ ≤ _ at hMr
  change ‖Hs‖ ≤ _ at hHs
  change ‖Hm‖ ≤ _ at hHm
  change ‖Tail‖ ≤ _ at hTail
  change ‖Hp‖ ≤ _ at hHp
  have hn := lemma59_ext44_norm_eight_terms (R - F) (R - Rt) Sr Mr Hs Hm Tail Hp
  have hpow : lemma23PaperL D ^ (-180 : ℤ) ≤ lemma23PaperL D ^ (-179 : ℤ) :=
    zpow_le_zpow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (by norm_num)
  change ‖DirichletCharacter.LFunction ψ s *
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
      (F + lemma44ActualZtilde χ ψ s * f (1 - s))‖ ≤ _
  rw [he]
  calc
    _ ≤ lemma44ErrorConstant180 * lemma23PaperL D ^ (-180 : ℤ) +
        (5 * Real.exp (3 + 4 * Real.pi)) * lemma23PaperL D ^ (-179 : ℤ) := by
      unfold lemma44ErrorConstant180
      nlinarith only [hn, hR, hRt, hSr, hMr, hHs, hHm, hTail, hHp]
    _ ≤ lemma44ErrorConstant * lemma23PaperL D ^ (-179 : ℤ) := by
      have hm := mul_le_mul_of_nonneg_left hpow lemma44_error_constant180_nonneg
      unfold lemma44ErrorConstant
      nlinarith only [hm]

open Complex MeasureTheory in
theorem lemma59_ext44_uniform_error_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (D p : ℕ) [NeZero p]
      (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
      lemma23SectionFourModulusThreshold ≤ D → Lemma23InPsi1 χ ψ →
      ∀ s : ℂ, Lemma59ExtendedOmega3 D s →
      letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
      ‖DirichletCharacter.LFunction ψ s *
          DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s -
        (lemma23ActualSectionFourF χ (fun n => ψ (n : ZMod p)) s +
          lemma44ActualZtilde χ ψ s *
            lemma23ActualSectionFourF χ (fun n => ψ⁻¹ (n : ZMod p)) (1 - s))‖ ≤
        C * lemma23PaperL D ^ (-179 : ℤ) := by
  refine ⟨lemma44ErrorConstant, lemma44_error_constant_pos, ?_⟩
  intro D p _ χ ψ hD hψ s hs
  exact lemma59_ext44_actual_approximate_functional_equation χ ψ hD hψ hs

end ZhangLS.Spec
