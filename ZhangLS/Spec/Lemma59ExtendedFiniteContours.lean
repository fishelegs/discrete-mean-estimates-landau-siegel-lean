import ZhangLS.Spec.Lemma59ExtendedGammaAndSums

/-! # Full original actual L-function quotient for Lemma 5.9

Original Psi1, actual objects, original closed boundaries and all-zero
separation are retained. The final module proves the unchanged Lemma59Target.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open scoped ArithmeticFunction.zeta Interval Real Topology
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096

open Complex in
theorem lemma59_ext44_initial_left_denominator_bound {D : ℕ}
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) (v : ℝ) :
    ‖lemma44InitialLeftShift s v‖⁻¹ ≤ 2 := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have hre := lemma59_ext44_omega3_re_pos hL hs
  have hn := Complex.abs_re_le_norm (lemma44InitialLeftShift s v)
  rw [lemma44_initial_left_shift_re, abs_of_neg (by linarith : -s.re - 1 / 2 < 0)] at hn
  have hnorm : 0 < ‖lemma44InitialLeftShift s v‖ := by linarith only [hn, hre]
  apply (inv_le_comm₀ hnorm (by norm_num : (0 : ℝ) < 2)).mpr
  norm_num
  linarith only [hn, hre]

open Complex in
theorem lemma59_ext44_initial_left_shift_abs_re {D : ℕ} (hL : 3 ≤ lemma23PaperL D)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) (v : ℝ) :
    |(lemma44InitialLeftShift s v).re| ≤ 3 := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have ha := lemma44_alpha_pos_le_one hL
  have hre := lemma59_ext44_omega3_re_pos hL hs
  rw [lemma44_initial_left_shift_re]
  apply abs_le.mpr
  constructor <;> linarith only [hs.2.1, ha.2, hre]

open Complex MeasureTheory in
theorem lemma59_ext44_left_product_mellin_eq_reflected_series {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) (B : ℝ) {v : ℝ}
    (hv : |v| ≤ lemma23PaperL D ^ 20) :
    let w : ℂ := ((-s.re - 1 / 2 : ℝ) : ℂ) + (v : ℂ) * I
    lemma44ProductMellinIntegrand χ ψ s B (-s.re - 1 / 2) v =
      lemma44ActualZtilde χ ψ (s + w) *
        LSeries (fun n => lemma23NuArithmeticFunction χ n * ψ⁻¹ (n : ZMod p)) (1 - s - w) *
          exp (w * (Real.log B : ℂ)) * lemma57OmegaOne D w / w := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let w : ℂ := ((-s.re - 1 / 2 : ℝ) : ℂ) + (v : ℂ) * I
  have hwre : |w.re| ≤ 15 := by
    have ha := lemma44_alpha_pos_le_one hL
    have hre := lemma59_ext44_omega3_re_pos hL hs
    simp only [w, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    apply abs_le.mpr
    constructor <;> linarith only [hs.2.1, ha.2, hre]
  have hregion := lemma59_ext44_truncated_shift_in_extended_gamma_region hL hs hwre
    (by simpa [w] using hv)
  have him := (lemma44_extended_gamma_region_height hL hregion).2.2.1
  have hfe := lemma44_equation44 χ ψ hL hψ him
  have hmir : 1 < (1 - (s + w)).re := by simp [w]; linarith
  have hprod := lemma44_product_LFunction_eq_LSeries χ ψ⁻¹ hmir
  have hmirror : 1 - s - w = 1 - (s + w) := by ring
  change _ = lemma44ActualZtilde χ ψ (s + w) *
    LSeries (fun n => lemma23NuArithmeticFunction χ n * ψ⁻¹ (n : ZMod p)) (1 - s - w) *
      exp (w * (Real.log B : ℂ)) * lemma57OmegaOne D w / w
  rw [hmirror]
  unfold lemma44ProductMellinIntegrand
  change (DirichletCharacter.LFunction ψ (s + w) *
    DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) (s + w)) *
      exp (w * (Real.log B : ℂ)) * lemma57OmegaOne D w / w = _
  rw [hfe, lemma44CharacterTwist_inv, hprod]

open MeasureTheory Complex in
theorem lemma59_ext44_long_sum_on_omega3 {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖lemma44LongDirichletSum χ ψ s‖ ≤
      4 * Real.exp (2 * Real.pi) * lemma23PaperL D ^ (-180 : ℤ) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have hLpos : 0 < lemma23PaperL D := by linarith
  have ha := lemma44_alpha_pos_le_one hL
  have hmax : max 0 (1 / 2 - s.re) ≤ lemma44PaperAlpha D :=
    max_le ha.1.le (by linarith [hs.1])
  have halpha : lemma23PaperL D ^ 9 * lemma44PaperAlpha D = Real.pi := by
    simp only [lemma44PaperAlpha, lemma23PaperP, Real.log_exp]
    field_simp
  have hexp : Real.exp (2 * lemma23PaperL D ^ 9 * max 0 (1 / 2 - s.re)) ≤
      Real.exp (2 * Real.pi) := by
    apply Real.exp_le_exp.mpr
    have h := mul_le_mul_of_nonneg_left hmax (pow_pos hLpos 9).le
    rw [halpha] at h
    linarith
  have hb := lemma44_long_sum_L180_of_displacement χ ψ s hL hψ.2
    (lemma59_ext44_omega3_displacement hL hs)
  exact hb.trans (mul_le_mul_of_nonneg_right (by linarith) (by positivity))

open Complex ComplexConjugate in
theorem lemma59_ext44_middle_Z_norm_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44ActualZtilde χ ψ
      (s + (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I))‖ ≤
        Real.exp (2 + 2 * lemma23PaperL D ^ 9 *
          (1 / 2 - s.re + lemma44PaperAlpha D)) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  let z := s + (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I)
  have hz : Lemma44InExtendedGammaRegion D z :=
    lemma59_ext44_truncated_shift_in_extended_gamma_region hL hs
      (by simp only [Complex.add_re, Complex.neg_re, Complex.ofReal_re,
        Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul,
        sub_zero, add_zero, abs_neg]
          rw [abs_of_pos ha.1]; linarith [ha.2]) (by simpa using hv)
  have hre : z.re = s.re - lemma44PaperAlpha D := by simp [z]; ring
  have hlogP : Real.log (lemma23PaperP D) = lemma23PaperL D ^ 9 := by
    simp [lemma23PaperP]
  by_cases hr : 1 / 2 ≤ z.re
  · have hb := lemma44ActualZtilde_norm_le_right χ ψ hD hψ hz hr
    apply hb.trans
    rw [hre, hlogP]
    apply Real.exp_le_exp.mpr
    ring_nf
    linarith
  · have hb := lemma44ActualZtilde_norm_le_left χ ψ hD hψ hz (le_of_not_ge hr)
    have hsmall : 3 * lemma23PaperL D * (1 / 2 - z.re) ≤ 2 := by
      have hm := mul_le_mul_of_nonneg_left (show 1 / 2 - z.re ≤ 2 * lemma44PaperAlpha D by
        rw [hre]; linarith [hs.1]) (by linarith : 0 ≤ 3 * lemma23PaperL D)
      nlinarith only [hm, lemma44_alpha_horizontal_loss hL]
    apply hb.trans
    rw [hre, hlogP] at *
    apply Real.exp_le_exp.mpr
    nlinarith only [hsmall]

open Complex MeasureTheory Set in
theorem lemma59_ext44_middle_integrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    IntegrableOn (lemma44MiddleContourIntegrand χ ψ s)
      (Ioc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)) := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have ha := lemma44_alpha_pos_le_one hL
  let w : ℝ → ℂ := fun v => -(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I
  have hwc : Continuous w := by dsimp [w]; fun_prop
  have hwne (v : ℝ) : w v ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp [w] at hr
    exact ha.1.ne' hr
  have hrest : Continuous (fun v : ℝ => lemma44LongDirichletSum χ ψ⁻¹ (1 - s - w v) *
      Complex.exp (w v * (Real.log (lemma44PaperGaussianScale D) : ℂ)) *
        lemma57OmegaOne D (w v) / w v) := by
    have hnum : Continuous (fun v : ℝ => lemma44LongDirichletSum χ ψ⁻¹ (1 - s - w v) *
        Complex.exp (w v * (Real.log (lemma44PaperGaussianScale D) : ℂ)) *
          lemma57OmegaOne D (w v)) := by
      unfold lemma44LongDirichletSum lemma57OmegaOne
      fun_prop
    exact hnum.div₀ hwc hwne
  have hc : ContinuousOn (lemma44MiddleContourIntegrand χ ψ s)
      (Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)) := by
    intro v hv
    have hvabs : |v| ≤ lemma23PaperL D ^ 20 := abs_le.mpr hv
    have hz := lemma59_ext44_truncated_shift_in_extended_gamma_region hL hs
      (w := w v) (by
        simp only [w, Complex.add_re, Complex.neg_re, Complex.ofReal_re,
          Complex.mul_re, Complex.ofReal_im, Complex.I_re, mul_zero, zero_mul,
          sub_zero, add_zero, abs_neg]
        rw [abs_of_pos ha.1]; linarith [ha.2]) (by simpa [w] using hvabs)
    have him := (lemma44_extended_gamma_region_height hL hz).2.2.1
    have hzd : ContinuousAt (lemma44ActualZtilde χ ψ) (s + w v) :=
      (lemma44ActualZtilde_differentiableAt χ ψ him.ne').continuousAt
    have hargC : ContinuousAt (fun u : ℝ => s + w u) v :=
      continuousAt_const.add hwc.continuousAt
    have hzc : ContinuousAt (fun u : ℝ => lemma44ActualZtilde χ ψ (s + w u)) v :=
      hzd.comp (f := fun u : ℝ => s + w u) hargC
    have h := hzc.mul hrest.continuousAt
    have heq : lemma44MiddleContourIntegrand χ ψ s =
        (fun u : ℝ => lemma44ActualZtilde χ ψ (s + w u)) *
          (fun u : ℝ => lemma44LongDirichletSum χ ψ⁻¹ (1 - s - w u) *
            Complex.exp (w u * (Real.log (lemma44PaperGaussianScale D) : ℂ)) *
              lemma57OmegaOne D (w u) / w u) := by
      funext u
      dsimp [lemma44MiddleContourIntegrand, w]
      ring
    rw [heq]
    exact h.continuousWithinAt
  exact hc.integrableOn_Icc.mono_set Ioc_subset_Icc_self

open Complex MeasureTheory in
theorem lemma59_ext44_product_finite_shift {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) (B : ℝ) {T : ℝ} (hT : 0 < T) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    lemma44TruncatedProductMellin χ ψ s B 1 T =
      DirichletCharacter.LFunction ψ s *
          DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s +
        lemma44TruncatedProductMellin χ ψ s B (-s.re - 1 / 2) T +
          lemma44ProductHorizontalError χ ψ s B (-s.re - 1 / 2) T := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hres := lemma44_simple_pole_rectangle_left (lemma44ProductMellinNumerator χ ψ s B)
    (lemma44_product_mellin_numerator_differentiable χ ψ hL hψ s B)
    (a := -s.re - 1 / 2) (by linarith [lemma59_ext44_omega3_re_pos hL hs]) hT
  have hzero : lemma44ProductMellinNumerator χ ψ s B 0 =
      DirichletCharacter.LFunction ψ s *
        DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s := by
    simp [lemma44ProductMellinNumerator, lemma57OmegaOne]
  rw [hzero] at hres
  have hpoint (σ t : ℝ) : lemma44ProductMellinIntegrand χ ψ s B σ t =
      lemma44ProductMellinNumerator χ ψ s B ((σ : ℂ) + (t : ℂ) * I) /
        ((σ : ℂ) + (t : ℂ) * I) := rfl
  unfold lemma44TruncatedProductMellin lemma44ProductHorizontalError
  simp_rw [hpoint, intervalIntegral.integral_mul_const]
  field_simp [two_pi_I_ne_zero]
  unfold lemma44RectangleBoundaryIntegral at hres
  simp only [ofReal_one, sub_eq_add_neg] at hres ⊢
  ring_nf at hres ⊢
  simp only [sub_eq_add_neg, add_comm, add_left_comm,
    mul_comm, mul_left_comm, mul_assoc] at hres ⊢
  linear_combination hres

open Complex MeasureTheory Set in
theorem lemma59_ext44_product_horizontal_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {x v : ℝ}
    (hx : -s.re - 1 / 2 ≤ x) (hx10 : |x| ≤ 10) (hv : |v| = lemma23PaperL D ^ 20) :
    ‖lemma44ProductMellinNumerator χ ψ s (lemma44PaperGaussianScale D)
      ((x : ℂ) + (v : ℂ) * I) / ((x : ℂ) + (v : ℂ) * I)‖ ≤
      262144 * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL0 : 0 ≤ lemma23PaperL D := by linarith
  let w : ℂ := (x : ℂ) + (v : ℂ) * I
  have hr : Lemma44InExtendedGammaRegion D (s + w) :=
    lemma59_ext44_truncated_shift_in_extended_gamma_region hL hs
      (by simpa [w] using hx10.trans (by norm_num : (10 : ℝ) ≤ 15))
      (by simpa [w] using hv.le)
  have hre : -1 / 2 ≤ (s + w).re := by simp [w]; linarith only [hx]
  have hp := lemma44_actual_product_local_growth χ ψ hD hψ hr hre
  have hb := lemma44_horizontal_scale_bound hL (abs_le.mp hx10).2 v
  have hg := lemma44_horizontal_gaussian_bound hL hx10 hv
  have hi := lemma44_horizontal_denominator_bound hL x hv
  have hbudget : lemma23PaperL D ^ 1038 *
      Real.exp (22 * lemma23PaperL D ^ 9 + 4 * lemma23PaperL D - lemma23PaperL D ^ 10 / 4) ≤
      lemma23PaperL D ^ (-180 : ℤ) := by
    apply le_trans _ (lemma44_horizontal_decay_budget (lemma44_log_large_at_threshold hD))
    apply mul_le_mul
      (pow_le_pow_right₀ (by linarith : 1 ≤ lemma23PaperL D) (show 1038 ≤ 2000 by norm_num))
      (Real.exp_le_exp.mpr (by nlinarith only [hL0, pow_nonneg hL0 9]))
      (Real.exp_nonneg _) (pow_nonneg hL0 2000)
  change ‖lemma44ProductMellinNumerator χ ψ s (lemma44PaperGaussianScale D) w / w‖ ≤ _
  unfold lemma44ProductMellinNumerator
  simp only [norm_mul, norm_inv, div_eq_mul_inv]
  rw [norm_mul] at hp
  calc
    _ ≤ (262144 * Real.exp (4 * lemma23PaperL D + 4 * lemma23PaperL D ^ 9) * lemma23PaperL D ^ 1038) *
        Real.exp (18 * lemma23PaperL D ^ 9) *
        (Real.exp 1 * Real.exp (-(lemma23PaperL D ^ 10 / 4))) * 1 := by
      gcongr
    _ = (262144 * Real.exp 1) * (lemma23PaperL D ^ 1038 *
        Real.exp (22 * lemma23PaperL D ^ 9 + 4 * lemma23PaperL D - lemma23PaperL D ^ 10 / 4)) := by
      have he : Real.exp (22 * lemma23PaperL D ^ 9 + 4 * lemma23PaperL D - lemma23PaperL D ^ 10 / 4) =
          Real.exp (4 * lemma23PaperL D + 4 * lemma23PaperL D ^ 9) *
          Real.exp (18 * lemma23PaperL D ^ 9) * Real.exp (-(lemma23PaperL D ^ 10 / 4)) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbudget (by positivity)

open Complex MeasureTheory Set in
theorem lemma59_ext44_reflected_horizontal_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) (f : ℂ → ℂ) {x v E H : ℝ}
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
  have hr := lemma59_ext44_truncated_shift_in_extended_gamma_region hL hs
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

open Complex ComplexConjugate in
theorem lemma59_ext44_reflected_long_sum_bound {D p : ℕ}
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi1 χ ψ)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) {v : ℝ} (hv : |v| ≤ lemma23PaperL D ^ 20) :
    ‖lemma44LongDirichletSum χ ψ⁻¹
      (1 - s - (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I))‖ ≤
        5 * Real.exp (2 * lemma23PaperL D ^ 9 *
          max 0 (s.re - 1 / 2 - lemma44PaperAlpha D)) * lemma23PaperL D ^ (-180 : ℤ) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have harg : conj (1 - s - (-(lemma44PaperAlpha D : ℂ) + (v : ℂ) * Complex.I)) =
      lemma44MiddleReflectedArgument D s v := by
    apply Complex.ext <;> simp [lemma44MiddleReflectedArgument] <;> ring
  rw [lemma44_long_sum_inv_eq_conj, Complex.norm_conj, harg]
  have hdisp := lemma59_ext44_middle_reflected_displacement hL hs hv
  have hLpos : 0 < lemma23PaperL D := by linarith
  have hpow : 1 ≤ lemma23PaperL D ^ 405 := one_le_pow₀ (by linarith : 1 ≤ lemma23PaperL D)
  have hprod : lemma23PaperL D ^ 405 * lemma23PaperL D ^ (-585 : ℤ) =
      lemma23PaperL D ^ (-180 : ℤ) := by
    rw [← zpow_natCast, ← zpow_add₀ hLpos.ne']
    norm_num
  have hcoef : (1 + ‖lemma23PaperCenter D - lemma44MiddleReflectedArgument D s v‖) *
      lemma23PaperL D ^ (-585 : ℤ) ≤ 5 * lemma23PaperL D ^ (-180 : ℤ) := by
    calc
      _ ≤ (5 * lemma23PaperL D ^ 405) * lemma23PaperL D ^ (-585 : ℤ) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = _ := by rw [mul_assoc, hprod]
  have hb := lemma44_long_sum_bound χ ψ (lemma44MiddleReflectedArgument D s v) hL hψ.2
  have hre : 1 / 2 - (lemma44MiddleReflectedArgument D s v).re =
      s.re - 1 / 2 - lemma44PaperAlpha D := by
    simp [lemma44MiddleReflectedArgument]
    ring
  rw [hre] at hb
  have he := mul_le_mul_of_nonneg_left hcoef (Real.exp_nonneg
    (2 * lemma23PaperL D ^ 9 * max 0 (s.re - 1 / 2 - lemma44PaperAlpha D)))
  exact hb.trans (by nlinarith only [he])

open Complex MeasureTheory Set in
theorem lemma59_ext44_reflected_numerator_rectangle_differentiable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma59ExtendedOmega3 D s)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) {a b : ℝ} (ha : -3 ≤ a) (hb : b ≤ 10) :
    DifferentiableOn ℂ (lemma44ReflectedPolynomialNumerator χ ψ s f)
      (lemma44ClosedRectangle a b (lemma23PaperL D ^ 20)) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  intro w hw
  have hwr : |w.re| ≤ 15 := by
    have hr := hw.1
    apply abs_le.mpr
    constructor <;> linarith only [hr.1, hr.2, ha, hb]
  have hwi : |w.im| ≤ lemma23PaperL D ^ 20 := abs_le.mpr hw.2
  have hregion := lemma59_ext44_truncated_shift_in_extended_gamma_region hL hs hwr hwi
  exact (lemma44_reflected_numerator_differentiableAt χ ψ s f hf
    (ne_of_gt (lemma44_extended_gamma_region_height hL hregion).2.2.1)).differentiableWithinAt

open Complex MeasureTheory Set in
theorem lemma59_ext44_reflected_polynomial_intervalIntegrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) {s : ℂ} (hs : Lemma59ExtendedOmega3 D s)
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) {σ : ℝ} (hσ : |σ| ≤ 15) (hσ0 : σ ≠ 0) :
    IntervalIntegrable (fun v : ℝ =>
      lemma44ReflectedPolynomialNumerator χ ψ s f ((σ : ℂ) + (v : ℂ) * I) /
        ((σ : ℂ) + (v : ℂ) * I)) volume
      (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) := by
  have hheightmargin := lemma59_extended_height_margin hL
  have hL20nonneg := pow_nonneg (by linarith only [hL] : 0 ≤ lemma23PaperL D) 20
  have hT : 0 ≤ lemma23PaperL D ^ 20 := by positivity
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le (by linarith : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20)]
  intro v hv
  let w : ℂ := (σ : ℂ) + (v : ℂ) * I
  have hr := lemma59_ext44_truncated_shift_in_extended_gamma_region hL hs (w := w)
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

open Complex MeasureTheory in
theorem lemma59_ext44_right_vertical_truncation_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D)
    {s : ℂ} (hs : Lemma59ExtendedOmega3 D s) :
    ‖(2 * (Real.pi : ℂ) * I)⁻¹ *
      (∫ v : ℝ, lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 v * I) -
        lemma44TruncatedProductMellin χ ψ s (lemma44PaperGaussianScale D) 1
          (lemma23PaperL D ^ 20)‖ ≤
      8 * lemma44DivisorSeriesMass * Real.exp 1 * lemma23PaperL D ^ (-180 : ℤ) := by
  let L := lemma23PaperL D
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hmass := lemma44_divisor_series_mass_nonneg
  have hB : 0 < lemma44PaperGaussianScale D := by
    unfold lemma44PaperGaussianScale lemma23PaperP
    exact Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hi := (lemma44_product_gaussian_mellin_identity χ ψ s
    (lemma44_modulus_one_lt_at_threshold χ hD) hB (by norm_num : (0 : ℝ) < 1)
    (by linarith only [lemma59_ext44_omega3_re_pos hL hs])).1.mul_const I
  have hg := lemma44_gaussian_integral_truncation _ hi
    (mul_nonneg lemma44_divisor_series_mass_nonneg (Real.exp_nonneg _))
    (by positivity : 0 < 1 / (4 * L ^ 30)) (pow_pos hL0 20)
    (lemma59_ext44_right_mellin_gaussian_bound χ ψ hL hs)
  have he : 1 / (4 * L ^ 30) * (L ^ 20) ^ 2 = L ^ 10 / 4 := by
    field_simp
  have hk : 1 / (4 * L ^ 30) * L ^ 20 = (4 * L ^ 10)⁻¹ := by
    field_simp
  change ‖_ - _‖ ≤ _ at hg
  rw [neg_mul, he, hk, div_eq_mul_inv, inv_inv] at hg
  have hb : L ^ 10 * Real.exp ((9 / 5 : ℝ) * L ^ 9 - L ^ 10 / 4) ≤ L ^ (-180 : ℤ) := by
    calc
      _ ≤ L ^ 2000 * Real.exp (30 * L ^ 9 + 100 * L - L ^ 10 / 4) := by
        apply mul_le_mul
          (pow_le_pow_right₀ hL1 (show 10 ≤ 2000 by norm_num))
          (Real.exp_le_exp.mpr (by nlinarith only [hL0, pow_nonneg hL0.le 9]))
          (Real.exp_nonneg _) (pow_nonneg hL0.le 2000)
      _ ≤ _ := lemma44_horizontal_decay_budget (lemma44_log_large_at_threshold hD)
  have heprod : Real.exp (1 + (9 / 5 : ℝ) * L ^ 9) * Real.exp (-(L ^ 10 / 4)) =
      Real.exp 1 * Real.exp ((9 / 5 : ℝ) * L ^ 9 - L ^ 10 / 4) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  have hg' : ‖(∫ v : ℝ, lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 v * I) -
      (∫ v : ℝ in -(L ^ 20)..L ^ 20,
        lemma44ProductMellinIntegrand χ ψ s (lemma44PaperGaussianScale D) 1 v * I)‖ ≤
      8 * lemma44DivisorSeriesMass * Real.exp 1 * L ^ (-180 : ℤ) := by
    apply hg.trans
    calc
      _ = (8 * lemma44DivisorSeriesMass * Real.exp 1) *
          (L ^ 10 * Real.exp ((9 / 5 : ℝ) * L ^ 9 - L ^ 10 / 4)) := by
        dsimp only [L]
        rw [show 2 * (lemma44DivisorSeriesMass * Real.exp (1 + (9 / 5 : ℝ) * lemma23PaperL D ^ 9)) *
            Real.exp (-(lemma23PaperL D ^ 10 / 4)) * (4 * lemma23PaperL D ^ 10) =
          8 * lemma44DivisorSeriesMass * lemma23PaperL D ^ 10 *
            (Real.exp (1 + (9 / 5 : ℝ) * lemma23PaperL D ^ 9) * Real.exp (-(lemma23PaperL D ^ 10 / 4)))
          by ring]
        rw [heprod]
        ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
  unfold lemma44TruncatedProductMellin
  rw [← mul_sub, norm_mul]
  exact (mul_le_mul_of_nonneg_right lemma44_mellin_normalization_norm_le_one (norm_nonneg _)).trans
    (by simpa only [one_mul] using hg')

end ZhangLS.Spec
