import ZhangLS.Spec.Lemma112Parameters
/-! # The actual conductor-Dp Z error: regularity and original E₂ control -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
namespace ZhangLS.Spec
open Complex MeasureTheory Set
open scoped Real Topology

noncomputable def lemma112ConductorScale (D : ℕ) : ℝ :=
  (D : ℝ) * lemma23PaperP D * lemma51PaperT0 D

noncomputable def lemma112ErrorDifferenceNumerator {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s w : ℂ) : ℂ :=
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + w) -
    lemma23DirichletZ (lemma44CharacterTwist χ ψ) s *
      (lemma112ConductorScale D : ℂ) ^ (-w)

noncomputable def lemma112ActualZErrorIntegrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (z : ℝ) (w : ℂ) : ℂ :=
  (lemma112ErrorDifferenceNumerator χ ψ s w / w) *
    lemma112ShortPolynomial χ ψ⁻¹ (1 - s - w) *
      exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ)) * lemma57OmegaOne D w

noncomputable def lemma112ErrorRegularIntegrand {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (z : ℝ) (w : ℂ) : ℂ :=
  dslope (lemma112ErrorDifferenceNumerator χ ψ s) 0 w *
    lemma112ShortPolynomial χ ψ⁻¹ (1 - s - w) *
      exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ)) * lemma57OmegaOne D w

lemma lemma112_conductor_scale_pos {D : ℕ} (hD : 1 < D) :
    0 < lemma112ConductorScale D := by
  unfold lemma112ConductorScale lemma51PaperT0
  exact mul_pos (mul_pos (by exact_mod_cast lt_trans Nat.zero_lt_one hD) (Real.exp_pos _))
    (pow_pos (Real.log_pos (by exact_mod_cast hD)) _)

lemma lemma112_error_difference_at_zero {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) :
    lemma112ErrorDifferenceNumerator χ ψ s 0 = 0 := by
  simp [lemma112ErrorDifferenceNumerator]

lemma lemma112_error_regular_eq_actual {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (z : ℝ) {w : ℂ} (hw : w ≠ 0) :
    lemma112ErrorRegularIntegrand χ ψ s z w = lemma112ActualZErrorIntegrand χ ψ s z w := by
  unfold lemma112ErrorRegularIntegrand
  rw [dslope_of_ne _ hw, slope_def_field, lemma112_error_difference_at_zero]
  simp only [sub_zero]
  rfl

lemma lemma112_error_difference_rectangle_differentiable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s) :
    DifferentiableOn ℂ (lemma112ErrorDifferenceNumerator χ ψ s)
      (lemma44ClosedRectangle (-1) 1 (lemma23PaperL D ^ 20)) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hmodel : Differentiable ℂ (fun w : ℂ => (lemma112ConductorScale D : ℂ) ^ (-w)) := by
    simp_rw [lemma61_positive_real_cpow_model (lemma112_conductor_scale_pos hD)]
    fun_prop
  intro w hw
  change w.re ∈ Icc (-1) 1 ∧ w.im ∈ Icc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) at hw
  have hpow : lemma23PaperL D ^ 20 ≤ lemma23PaperL D ^ 405 :=
    pow_le_pow_right₀ (by linarith) (by norm_num)
  have hh : |(s + w).im - (lemma23PaperCenter D).im| ≤ 2 * lemma23PaperL D ^ 405 + 3 := by
    have he : (s + w).im - (lemma23PaperCenter D).im =
        (s.im - (lemma23PaperCenter D).im) + w.im := by simp; ring
    rw [he]
    exact (abs_add_le _ _).trans (by linarith only [hs.2, abs_le.mpr hw.2, hpow])
  have hzi : 0 < (s + w).im := by linarith only [(lemma61_wide_height_data hL hh).2.1]
  have hz : DifferentiableAt ℂ (fun u : ℂ => lemma23DirichletZ (lemma44CharacterTwist χ ψ) (s + u)) w :=
    (lemma23DirichletZ_differentiableAt_of_im_ne_zero _ hzi.ne').comp w (by fun_prop)
  exact (hz.sub ((hmodel w).const_mul (lemma23DirichletZ (lemma44CharacterTwist χ ψ) s))).differentiableWithinAt

lemma lemma112_error_regular_rectangle_differentiable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s) (z : ℝ) :
    DifferentiableOn ℂ (lemma112ErrorRegularIntegrand χ ψ s z)
      (lemma44ClosedRectangle (-1) 1 (lemma23PaperL D ^ 20)) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hn : lemma44ClosedRectangle (-1) 1 (lemma23PaperL D ^ 20) ∈ nhds (0 : ℂ) := by
    rw [← mem_interior_iff_mem_nhds]
    simp only [lemma44ClosedRectangle, interior_reProdIm, interior_Icc, mem_reProdIm,
      mem_Ioo, zero_re, zero_im]
    constructor <;> constructor <;> norm_num <;> positivity
  have hd := (Complex.differentiableOn_dslope hn).2
    (lemma112_error_difference_rectangle_differentiable χ ψ hD hL hs)
  have hN := lemma112_short_polynomial_differentiable χ ψ⁻¹
  have hp : Differentiable ℂ (fun w : ℂ => lemma112ShortPolynomial χ ψ⁻¹ (1 - s - w) *
      exp (w * (Real.log (lemma23PaperP D ^ z) : ℂ)) * lemma57OmegaOne D w) := by
    unfold lemma57OmegaOne
    fun_prop
  convert hd.mul hp.differentiableOn using 1
  funext w
  dsimp [lemma112ErrorRegularIntegrand]
  ring

lemma lemma112_actual_error_vertical_point_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma112InRegion D s) (z : ℝ) {v : ℝ}
    (hv : |v| < lemma23PaperL D ^ 20) :
    ‖lemma112ActualZErrorIntegrand χ ψ s z (I * (v : ℂ))‖ ≤
      lemma51ErrorConstant * lemma23PaperL D ^ (-68 : ℤ) *
        (‖lemma112ShortPolynomial χ ψ (s + I * (v : ℂ))‖ *
          Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30))) := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hz := (lemma51_actual_shift_estimates χ ψ hD hψ
    (lemma112_region_subset_lemma51 hL hs) (w := I * (v : ℂ)) (by simp) (by simpa using hv)).2.2.2
  change ‖lemma112ErrorDifferenceNumerator χ ψ s (I * (v : ℂ)) / (I * (v : ℂ))‖ ≤ _ at hz
  have hex : ‖exp ((I * (v : ℂ)) * (Real.log (lemma23PaperP D ^ z) : ℂ))‖ = 1 := by
    rw [norm_exp]
    simp
  unfold lemma112ActualZErrorIntegrand
  rw [norm_mul, norm_mul, norm_mul, hex, mul_one,
    lemma112_short_polynomial_critical_reflection χ ψ hs.1,
    lemma61_omega_one_imaginary_axis, Complex.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ (lemma51ErrorConstant * lemma23PaperL D ^ (-68 : ℤ)) *
        ‖lemma112ShortPolynomial χ ψ (s + I * (v : ℂ))‖ *
          Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hz (norm_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by ring

lemma lemma112_actual_error_vertical_integral_bound {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hD : lemma23SectionFourModulusThreshold ≤ D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma112InRegion D s) (z : ℝ) :
    ‖∫ v in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      lemma112ActualZErrorIntegrand χ ψ s z (I * (v : ℂ))‖ ≤
        lemma51ErrorConstant * lemma112ActualE2 χ ψ s := by
  have hL := (lemma44_parameters_at_explicit_threshold hD).1
  have hH : 0 < lemma23PaperL D ^ 20 := pow_pos (by linarith : 0 < lemma23PaperL D) 20
  have hi := (lemma112_error_integrand_interval_integrable χ ψ s
    (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20)).const_mul
      (lemma51ErrorConstant * lemma23PaperL D ^ (-68 : ℤ))
  have hb := intervalIntegral.norm_integral_le_of_norm_le (by linarith : -(lemma23PaperL D ^ 20) ≤ lemma23PaperL D ^ 20)
    (f := fun v => lemma112ActualZErrorIntegrand χ ψ s z (I * (v : ℂ))) (g := fun v =>
      (lemma51ErrorConstant * lemma23PaperL D ^ (-68 : ℤ)) *
        (‖lemma112ShortPolynomial χ ψ (s + I * (v : ℂ))‖ *
          Real.exp (-(v ^ 2) / (4 * lemma23PaperL D ^ 30)))) ?_ hi
  · apply hb.trans_eq
    rw [intervalIntegral.integral_const_mul]
    unfold lemma112ActualE2
    ring
  · filter_upwards [volume.ae_ne (lemma23PaperL D ^ 20)] with v hv
    intro hvI
    exact lemma112_actual_error_vertical_point_bound χ ψ hD hψ hs z
      (abs_lt.mpr ⟨hvI.1, lt_of_le_of_ne hvI.2 hv⟩)

lemma lemma112_error_vertical_ae_eq {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (z a : ℝ) :
    (fun v : ℝ => lemma112ErrorRegularIntegrand χ ψ s z ((a : ℂ) + (v : ℂ) * I)) =ᵐ[volume]
      (fun v : ℝ => lemma112ActualZErrorIntegrand χ ψ s z ((a : ℂ) + (v : ℂ) * I)) := by
  filter_upwards [volume.ae_ne (0 : ℝ)] with v hv
  apply lemma112_error_regular_eq_actual
  intro he
  have hi := congrArg Complex.im he
  simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
    add_zero, zero_add, zero_im] at hi
  exact hv hi

lemma lemma112_error_vertical_interval_integrable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s)
    (z : ℝ) {a : ℝ} (ha : a ∈ Icc (-1) 1) :
    IntervalIntegrable (fun v : ℝ => lemma112ActualZErrorIntegrand χ ψ s z ((a : ℂ) + (v : ℂ) * I))
      volume (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) := by
  have h0 : 0 < lemma23PaperL D := by linarith
  have hR := (lemma112_error_regular_rectangle_differentiable χ ψ hD hL hs z).continuousOn
  have hm : MapsTo (fun v : ℝ => (a : ℂ) + (v : ℂ) * I)
      (uIcc (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20))
      (lemma44ClosedRectangle (-1) 1 (lemma23PaperL D ^ 20)) := by
    intro v hv
    rw [uIcc_of_le (neg_le_self (pow_nonneg h0.le 20))] at hv
    simpa [lemma44ClosedRectangle, mem_reProdIm] using And.intro ha hv
  have hi : IntervalIntegrable (fun v : ℝ => lemma112ErrorRegularIntegrand χ ψ s z ((a : ℂ) + (v : ℂ) * I))
      volume (-(lemma23PaperL D ^ 20)) (lemma23PaperL D ^ 20) :=
    (hR.comp (by fun_prop) hm).intervalIntegrable
  exact hi.congr_ae (ae_restrict_of_ae (lemma112_error_vertical_ae_eq χ ψ s z a))

lemma lemma112_error_vertical_integral_eq {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (z a H : ℝ) :
    (∫ v : ℝ in -H..H, lemma112ErrorRegularIntegrand χ ψ s z ((a : ℂ) + (v : ℂ) * I) * I) =
      (∫ v : ℝ in -H..H, lemma112ActualZErrorIntegrand χ ψ s z ((a : ℂ) + (v : ℂ) * I) * I) := by
  apply intervalIntegral.integral_congr_ae
  filter_upwards [lemma112_error_vertical_ae_eq χ ψ s z a] with v hv
  intro _
  exact congrArg (fun w : ℂ => w * I) hv

lemma lemma112_error_regular_path_rectangle_cauchy {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s) (z : ℝ) :
    lemma44GeneralRectangleBoundaryIntegral (lemma112ErrorRegularIntegrand χ ψ s z)
      (-1) 0 (lemma23PaperL D ^ 20) = 0 := by
  apply lemma44_local_rectangle_cauchy _ (by norm_num) (by positivity)
  apply (lemma112_error_regular_rectangle_differentiable χ ψ hD hL hs z).mono
  intro w hw
  exact ⟨⟨hw.1.1, hw.1.2.trans (by norm_num)⟩, hw.2⟩

lemma lemma112_actual_error_line_shift {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) {s : ℂ}
    (hD : 1 < D) (hL : 3 ≤ lemma23PaperL D) (hs : Lemma112InRegion D s) (z : ℝ) :
    (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
      lemma112ActualZErrorIntegrand χ ψ s z ((-1 : ℂ) + (v : ℂ) * I) * I) =
      (∫ v : ℝ in -(lemma23PaperL D ^ 20)..(lemma23PaperL D ^ 20),
        lemma112ActualZErrorIntegrand χ ψ s z (I * (v : ℂ)) * I) +
      (∫ x : ℝ in (-1 : ℝ)..0,
        lemma112ActualZErrorIntegrand χ ψ s z ((x : ℂ) - ((lemma23PaperL D ^ 20 : ℝ) : ℂ) * I)) -
      (∫ x : ℝ in (-1 : ℝ)..0,
        lemma112ActualZErrorIntegrand χ ψ s z ((x : ℂ) + ((lemma23PaperL D ^ 20 : ℝ) : ℂ) * I)) := by
  let H := lemma23PaperL D ^ 20
  let R := lemma112ErrorRegularIntegrand χ ψ s z
  let F := lemma112ActualZErrorIntegrand χ ψ s z
  have h0 : 0 < H := by dsimp [H]; positivity
  have hb : (∫ x : ℝ in (-1 : ℝ)..0, R ((x : ℂ) - (H : ℂ) * I)) =
      (∫ x : ℝ in (-1 : ℝ)..0, F ((x : ℂ) - (H : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply lemma112_error_regular_eq_actual
    intro he
    have hi := congrArg Complex.im he
    simp only [sub_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
      add_zero, zero_im] at hi
    linarith only [hi, h0]
  have ht : (∫ x : ℝ in (-1 : ℝ)..0, R ((x : ℂ) + (H : ℂ) * I)) =
      (∫ x : ℝ in (-1 : ℝ)..0, F ((x : ℂ) + (H : ℂ) * I)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply lemma112_error_regular_eq_actual
    intro he
    have hi := congrArg Complex.im he
    simp only [add_im, ofReal_im, mul_im, ofReal_re, I_im, I_re, mul_one, mul_zero,
      add_zero, zero_add, zero_im] at hi
    linarith only [hi, h0]
  have hc := lemma112_error_regular_path_rectangle_cauchy χ ψ hD hL hs z
  unfold lemma44GeneralRectangleBoundaryIntegral at hc
  simp only [Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_zero, zero_add] at hc
  have hleft := lemma112_error_vertical_integral_eq χ ψ s z (-1) H
  have hright := lemma112_error_vertical_integral_eq χ ψ s z 0 H
  simp only [Complex.ofReal_neg, Complex.ofReal_one] at hleft
  simp only [Complex.ofReal_zero, zero_add] at hright
  conv at hright => lhs; arg 1; ext v; rw [mul_comm (v : ℂ) I]
  conv at hright => rhs; arg 1; ext v; rw [mul_comm (v : ℂ) I]
  rw [← hleft, ← hright]
  change (∫ v : ℝ in -H..H, R ((-1 : ℂ) + (v : ℂ) * I) * I) =
    (∫ v : ℝ in -H..H, R (I * (v : ℂ)) * I) + _ - _
  rw [← hb, ← ht]
  simp only [intervalIntegral.integral_mul_const]
  simp only [mul_comm (I : ℂ)] at hc ⊢
  linear_combination -hc

end ZhangLS.Spec
