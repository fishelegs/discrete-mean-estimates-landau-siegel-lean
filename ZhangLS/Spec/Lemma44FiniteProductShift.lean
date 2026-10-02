import ZhangLS.Spec.Lemma44ProductResidue
import ZhangLS.Spec.Lemma44RightMellinApproximation
import ZhangLS.Spec.Lemma44ModulusControl

/-!
# The finite product contour shift to the reflected convergence line

A pole-free rectangle extends the proved residue rectangle to any left side
`a≤-1/2`. Thus the genuine product Mellin integral can be moved to
`Re w=-Re s-1/2`, where the reflected Dirichlet series has real part `3/2`.
This is an exact finite identity; no horizontal decay is assumed or asserted.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory

set_option maxHeartbeats 1000000

noncomputable def lemma44RectangleBoundaryIntegral (f : ℂ → ℂ) (a T : ℝ) : ℂ :=
  (∫ x : ℝ in a..1, f ((x : ℂ) - (T : ℂ) * I)) -
    (∫ x : ℝ in a..1, f ((x : ℂ) + (T : ℂ) * I)) +
      I * (∫ y : ℝ in -T..T, f (1 + (y : ℂ) * I)) -
        I * (∫ y : ℝ in -T..T, f ((a : ℂ) + (y : ℂ) * I))

theorem lemma44_simple_pole_rectangle_left (N : ℂ → ℂ) (hN : Differentiable ℂ N)
    {a T : ℝ} (ha : a ≤ -1 / 2) (hT : 0 < T) :
    lemma44RectangleBoundaryIntegral (fun w => N w / w) a T =
      2 * (Real.pi : ℂ) * I * N 0 := by
  let f : ℂ → ℂ := fun w => N w / w
  let z : ℂ := (a : ℂ) - (T : ℂ) * I
  let w : ℂ := -(1 : ℂ) / 2 + (T : ℂ) * I
  have hzre : z.re = a := by simp [z]
  have hwre : w.re = -1 / 2 := by simp [w]
  have hdiff : DifferentiableOn ℂ f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    intro u hu
    have hr : u.re ∈ Set.uIcc a (-1 / 2) := by
      simpa only [hzre, hwre] using hu.1
    rw [Set.uIcc_of_le ha] at hr
    have hune : u ≠ 0 := by
      intro he
      rw [he] at hr
      norm_num at hr
    exact ((hN u).div (differentiableAt_id) hune).differentiableWithinAt
  have hc := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w hdiff
  have hc' :
      (∫ x : ℝ in a..(-1 / 2), f ((x : ℂ) - (T : ℂ) * I)) -
        (∫ x : ℝ in a..(-1 / 2), f ((x : ℂ) + (T : ℂ) * I)) +
          I * (∫ y : ℝ in -T..T, f (-(1 : ℂ) / 2 + (y : ℂ) * I)) -
            I * (∫ y : ℝ in -T..T, f ((a : ℂ) + (y : ℂ) * I)) = 0 := by
    simpa [z, w, smul_eq_mul, sub_eq_add_neg] using hc
  have hbottom : Continuous (fun x : ℝ => f ((x : ℂ) - (T : ℂ) * I)) := by
    have hg : Continuous (fun x : ℝ => (x : ℂ) - (T : ℂ) * I) := by fun_prop
    exact (hN.continuous.comp hg).div₀ hg
      (by intro x hx; have hi := congrArg Complex.im hx; simp at hi; linarith)
  have htop : Continuous (fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I)) := by
    have hg : Continuous (fun x : ℝ => (x : ℂ) + (T : ℂ) * I) := by fun_prop
    exact (hN.continuous.comp hg).div₀ hg
      (by intro x hx; have hi := congrArg Complex.im hx; simp at hi; linarith)
  have hb := intervalIntegral.integral_add_adjacent_intervals
    (hbottom.intervalIntegrable (μ := volume) a (-1 / 2))
    (hbottom.intervalIntegrable (μ := volume) (-1 / 2) 1)
  have ht := intervalIntegral.integral_add_adjacent_intervals
    (htop.intervalIntegrable (μ := volume) a (-1 / 2))
    (htop.intervalIntegrable (μ := volume) (-1 / 2) 1)
  have hres := lemma44_simple_pole_rectangle N hN hT
  change lemma57RectangleBoundaryIntegral f T = _ at hres
  unfold lemma44RectangleBoundaryIntegral
  change (∫ x : ℝ in a..1, f ((x : ℂ) - (T : ℂ) * I)) -
    (∫ x : ℝ in a..1, f ((x : ℂ) + (T : ℂ) * I)) +
      I * (∫ y : ℝ in -T..T, f (1 + (y : ℂ) * I)) -
        I * (∫ y : ℝ in -T..T, f ((a : ℂ) + (y : ℂ) * I)) = _
  rw [← hb, ← ht]
  unfold lemma57RectangleBoundaryIntegral at hres
  simp only [ofReal_one] at hres
  linear_combination hres + hc'

noncomputable def lemma44TruncatedProductMellin {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (B σ T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    (∫ t : ℝ in -T..T, lemma44ProductMellinIntegrand χ ψ s B σ t * I)

noncomputable def lemma44ProductHorizontalError {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (s : ℂ) (B a T : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ((∫ x : ℝ in a..1,
        lemma44ProductMellinNumerator χ ψ s B ((x : ℂ) + (T : ℂ) * I) /
          ((x : ℂ) + (T : ℂ) * I)) -
      (∫ x : ℝ in a..1,
        lemma44ProductMellinNumerator χ ψ s B ((x : ℂ) - (T : ℂ) * I) /
          ((x : ℂ) - (T : ℂ) * I)))

/-- Exact finite deformation to the line where the reflected series is
absolutely convergent. Horizontal errors remain explicit. -/
theorem lemma44_product_finite_shift {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) (B : ℝ) {T : ℝ} (hT : 0 < T) :
    letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
    lemma44TruncatedProductMellin χ ψ s B 1 T =
      DirichletCharacter.LFunction ψ s *
          DirichletCharacter.LFunction (lemma44CharacterTwist χ ψ) s +
        lemma44TruncatedProductMellin χ ψ s B (-s.re - 1 / 2) T +
          lemma44ProductHorizontalError χ ψ s B (-s.re - 1 / 2) T := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  have hres := lemma44_simple_pole_rectangle_left (lemma44ProductMellinNumerator χ ψ s B)
    (lemma44_product_mellin_numerator_differentiable χ ψ hL hψ s B)
    (a := -s.re - 1 / 2) (by linarith [lemma44_omega3_re_pos hL hs]) hT
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

/-- The new left line is inside the absolute convergence domain of the
genuine inverse-character product series. -/
theorem lemma44_left_reflected_series_summable {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p) (s : ℂ) (v : ℝ) :
    LSeriesSummable (fun n => lemma23NuArithmeticFunction χ n * ψ⁻¹ (n : ZMod p))
      (1 - s - (((-s.re - 1 / 2 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  apply lemma44_product_series_summable χ ψ⁻¹
  simp
  linarith

/-- On the actual truncated left contour, the functional equation and
coefficient identity turn the integrand into the reflected series. -/
theorem lemma44_left_product_mellin_eq_reflected_series {D p : ℕ} [NeZero p]
    (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p)
    (hL : 3 ≤ lemma23PaperL D) (hψ : Lemma23InPsi (D := D) ψ)
    {s : ℂ} (hs : Lemma44InOmega3 D s) (B : ℝ) {v : ℝ}
    (hv : |v| ≤ lemma23PaperL D ^ 20) :
    let w : ℂ := ((-s.re - 1 / 2 : ℝ) : ℂ) + (v : ℂ) * I
    lemma44ProductMellinIntegrand χ ψ s B (-s.re - 1 / 2) v =
      lemma44ActualZtilde χ ψ (s + w) *
        LSeries (fun n => lemma23NuArithmeticFunction χ n * ψ⁻¹ (n : ZMod p)) (1 - s - w) *
          exp (w * (Real.log B : ℂ)) * lemma57OmegaOne D w / w := by
  letI : NeZero (D * p) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne p)⟩
  let w : ℂ := ((-s.re - 1 / 2 : ℝ) : ℂ) + (v : ℂ) * I
  have hwre : |w.re| ≤ 15 := by
    have ha := lemma44_alpha_pos_le_one hL
    have hre := lemma44_omega3_re_pos hL hs
    simp only [w, add_re, ofReal_re, mul_re, ofReal_im, I_re, I_im,
      mul_zero, zero_mul, sub_zero, add_zero]
    apply abs_le.mpr
    constructor <;> linarith only [hs.2.1, ha.2, hre]
  have hregion := lemma44_truncated_shift_in_extended_gamma_region hL hs hwre
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

end ZhangLS.Spec
