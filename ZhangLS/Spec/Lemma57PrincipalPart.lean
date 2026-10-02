import ZhangLS.Spec.Lemma57RectangleWinding

/-!
# Principal-part decomposition on the finite rectangle

This module removes both Taylor coefficients of the entire residue numerator
at zero by two applications of `dslope`.  The resulting second divided
difference is entire and agrees away from zero with the regular part after
subtracting the `s⁻²` and `s⁻¹` terms.

It also proves the two boundary-integral facts needed by this decomposition:
the boundary integral of an entire function vanishes by the rectangular
Cauchy--Goursat theorem, and the boundary integral of `s⁻²` vanishes by the
fundamental theorem of calculus on the four individual edges.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Set
open scoped Real Topology

/-- The regular part left after removing the constant and linear Taylor terms
of the pole-removed numerator.  Iterated `dslope` gives the removable values at
zero canonically. -/
noncomputable def lemma57EntireRemainder {D : ℕ}
    (χ : RealPrimitiveCharacter D) : ℂ → ℂ :=
  dslope (dslope (lemma57ResidueNumerator χ) 0) 0

/-- The regular remainder is entire. -/
theorem lemma57EntireRemainder_differentiable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Differentiable ℂ (lemma57EntireRemainder χ) := by
  rw [← differentiableOn_univ]
  unfold lemma57EntireRemainder
  apply (Complex.differentiableOn_dslope (s := Set.univ) (c := (0 : ℂ))
    (by simp)).2
  apply (Complex.differentiableOn_dslope (s := Set.univ) (c := (0 : ℂ))
    (by simp)).2
  exact (lemma57ResidueNumerator_differentiable χ hD).differentiableOn

/-- Away from zero, the genuine Mellin integrand is its double-pole term,
residue term, and an entire remainder. -/
theorem lemma57MellinIntegrand_eq_principalPart_add_remainder
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : s ≠ 0) :
    lemma57MellinIntegrand χ s =
      lemma57ResidueNumerator χ 0 / s ^ 2 +
        lemma57ResidueValue χ / s + lemma57EntireRemainder χ s := by
  rw [lemma57MellinIntegrand_eq_residueNumerator_div_sq χ hs]
  unfold lemma57EntireRemainder
  rw [dslope_of_ne _ hs]
  simp only [slope, vsub_eq_sub, sub_zero]
  rw [dslope_of_ne _ hs, dslope_same]
  rw [(lemma57ResidueNumerator_hasDerivAt_zero χ hD).deriv]
  rw [slope_def_field]
  field_simp [hs]
  simp only [smul_eq_mul, one_div, sub_zero]
  field_simp [hs]
  ring

/-- In inverse-power notation, the same decomposition is ready for boundary
integral linearity. -/
theorem lemma57MellinIntegrand_eq_inv_principalPart_add_remainder
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : s ≠ 0) :
    lemma57MellinIntegrand χ s =
      lemma57ResidueNumerator χ 0 * s⁻¹ ^ 2 +
        lemma57ResidueValue χ * s⁻¹ + lemma57EntireRemainder χ s := by
  rw [lemma57MellinIntegrand_eq_principalPart_add_remainder χ hD hs]
  simp only [div_eq_mul_inv, inv_pow]

private def lemma57RectangleBoundaryIntegrable
    (f : ℂ → ℂ) (T : ℝ) : Prop :=
  IntervalIntegrable (fun x : ℝ => f ((x : ℂ) - (T : ℂ) * I)) volume
      (-(1 : ℝ) / 2) 1 ∧
    IntervalIntegrable (fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I)) volume
      (-(1 : ℝ) / 2) 1 ∧
    IntervalIntegrable (fun y : ℝ => f (1 + (y : ℂ) * I)) volume (-T) T ∧
    IntervalIntegrable
      (fun y : ℝ => f (-(1 : ℝ) / 2 + (y : ℂ) * I)) volume (-T) T

private theorem lemma57RectangleBoundaryIntegrable.add
    {f g : ℂ → ℂ} {T : ℝ}
    (hf : lemma57RectangleBoundaryIntegrable f T)
    (hg : lemma57RectangleBoundaryIntegrable g T) :
    lemma57RectangleBoundaryIntegrable (fun s => f s + g s) T := by
  exact ⟨hf.1.add hg.1, hf.2.1.add hg.2.1,
    hf.2.2.1.add hg.2.2.1, hf.2.2.2.add hg.2.2.2⟩

private theorem lemma57RectangleBoundaryIntegrable.const_mul
    {f : ℂ → ℂ} {T : ℝ} (c : ℂ)
    (hf : lemma57RectangleBoundaryIntegrable f T) :
    lemma57RectangleBoundaryIntegrable (fun s => c * f s) T := by
  exact ⟨hf.1.const_mul c, hf.2.1.const_mul c,
    hf.2.2.1.const_mul c, hf.2.2.2.const_mul c⟩

private theorem lemma57RectangleBoundaryIntegrable_inv_pow
    (n : ℕ) (T : ℝ) (hT : 0 < T) :
    lemma57RectangleBoundaryIntegrable (fun s : ℂ => s⁻¹ ^ n) T := by
  unfold lemma57RectangleBoundaryIntegrable
  constructor
  · apply Continuous.intervalIntegrable
    apply Continuous.pow
    apply Continuous.inv₀
    · fun_prop
    · intro x h
      have hi := congrArg Complex.im h
      norm_num at hi
      linarith
  constructor
  · apply Continuous.intervalIntegrable
    apply Continuous.pow
    apply Continuous.inv₀
    · fun_prop
    · intro x h
      have hi := congrArg Complex.im h
      norm_num at hi
      linarith
  constructor
  · apply Continuous.intervalIntegrable
    apply Continuous.pow
    apply Continuous.inv₀
    · fun_prop
    · intro y h
      have hr := congrArg Complex.re h
      norm_num at hr
  · apply Continuous.intervalIntegrable
    apply Continuous.pow
    apply Continuous.inv₀
    · fun_prop
    · intro y h
      have hr := congrArg Complex.re h
      norm_num at hr

private theorem lemma57RectangleBoundaryIntegrable_of_continuous
    (f : ℂ → ℂ) (hf : Continuous f) (T : ℝ) :
    lemma57RectangleBoundaryIntegrable f T := by
  unfold lemma57RectangleBoundaryIntegrable
  have hbottom : Continuous
      (fun x : ℝ => f ((x : ℂ) - (T : ℂ) * I)) := hf.comp (by fun_prop)
  have htop : Continuous
      (fun x : ℝ => f ((x : ℂ) + (T : ℂ) * I)) := hf.comp (by fun_prop)
  have hright : Continuous
      (fun y : ℝ => f (1 + (y : ℂ) * I)) := hf.comp (by fun_prop)
  have hleft : Continuous
      (fun y : ℝ => f (-(1 : ℝ) / 2 + (y : ℂ) * I)) := hf.comp (by fun_prop)
  exact ⟨hbottom.intervalIntegrable (μ := volume) (-(1 : ℝ) / 2) 1,
    htop.intervalIntegrable (μ := volume) (-(1 : ℝ) / 2) 1,
    hright.intervalIntegrable (μ := volume) (-T) T,
    hleft.intervalIntegrable (μ := volume) (-T) T⟩

private theorem lemma57RectangleBoundaryIntegral_add
    {f g : ℂ → ℂ} {T : ℝ}
    (hf : lemma57RectangleBoundaryIntegrable f T)
    (hg : lemma57RectangleBoundaryIntegrable g T) :
    lemma57RectangleBoundaryIntegral (fun s => f s + g s) T =
      lemma57RectangleBoundaryIntegral f T +
        lemma57RectangleBoundaryIntegral g T := by
  unfold lemma57RectangleBoundaryIntegral
  rw [intervalIntegral.integral_add hf.1 hg.1,
    intervalIntegral.integral_add hf.2.1 hg.2.1,
    intervalIntegral.integral_add hf.2.2.1 hg.2.2.1,
    intervalIntegral.integral_add hf.2.2.2 hg.2.2.2]
  ring

private theorem lemma57RectangleBoundaryIntegral_const_mul
    (c : ℂ) (f : ℂ → ℂ) (T : ℝ) :
    lemma57RectangleBoundaryIntegral (fun s => c * f s) T =
      c * lemma57RectangleBoundaryIntegral f T := by
  unfold lemma57RectangleBoundaryIntegral
  simp_rw [intervalIntegral.integral_const_mul]
  ring

private theorem lemma57RectangleBoundaryIntegral_congr_of_ne_zero
    (f g : ℂ → ℂ) (T : ℝ) (hT : 0 < T)
    (hfg : ∀ s : ℂ, s ≠ 0 → f s = g s) :
    lemma57RectangleBoundaryIntegral f T =
      lemma57RectangleBoundaryIntegral g T := by
  have hbottom :
      (∫ x : ℝ in (-(1 : ℝ) / 2)..1,
          f ((x : ℂ) - (T : ℂ) * I)) =
        ∫ x : ℝ in (-(1 : ℝ) / 2)..1,
          g ((x : ℂ) - (T : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply hfg
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    linarith
  have htop :
      (∫ x : ℝ in (-(1 : ℝ) / 2)..1,
          f ((x : ℂ) + (T : ℂ) * I)) =
        ∫ x : ℝ in (-(1 : ℝ) / 2)..1,
          g ((x : ℂ) + (T : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro x hx
    apply hfg
    intro h
    have hi := congrArg Complex.im h
    norm_num at hi
    linarith
  have hright :
      (∫ y : ℝ in -T..T, f (1 + (y : ℂ) * I)) =
        ∫ y : ℝ in -T..T, g (1 + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    apply hfg
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  have hleft :
      (∫ y : ℝ in -T..T,
          f (-(1 : ℝ) / 2 + (y : ℂ) * I)) =
        ∫ y : ℝ in -T..T,
          g (-(1 : ℝ) / 2 + (y : ℂ) * I) := by
    apply intervalIntegral.integral_congr
    intro y hy
    apply hfg
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
  unfold lemma57RectangleBoundaryIntegral
  rw [hbottom, htop, hright, hleft]

/-- Rectangular Cauchy--Goursat in the exact boundary convention fixed in
Step 38. -/
theorem lemma57RectangleBoundaryIntegral_eq_zero_of_differentiable
    (f : ℂ → ℂ) (hf : Differentiable ℂ f) (T : ℝ) :
    lemma57RectangleBoundaryIntegral f T = 0 := by
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    f (-(1 : ℝ) / 2 - (T : ℂ) * I) (1 + (T : ℂ) * I)
    hf.differentiableOn
  simpa [lemma57RectangleBoundaryIntegral, smul_eq_mul] using h

private theorem horizontal_inv_sq_integral
    (c a b : ℝ) (hc : c ≠ 0) :
    (∫ x : ℝ in a..b, ((x : ℂ) + (c : ℂ) * I)⁻¹ ^ 2) =
      -((b : ℂ) + (c : ℂ) * I)⁻¹ -
        (-((a : ℂ) + (c : ℂ) * I)⁻¹) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro x hx
    have hz : (x : ℂ) + (c : ℂ) * I ≠ 0 := by
      intro h
      have hi := congrArg Complex.im h
      norm_num at hi
      exact hc hi
    have hbase : HasDerivAt (fun z : ℂ => z + (c : ℂ) * I) 1 (x : ℂ) := by
      simpa using (hasDerivAt_id (x := (x : ℂ))).add_const ((c : ℂ) * I)
    have hz' : (fun z : ℂ => z + (c : ℂ) * I) (x : ℂ) ≠ 0 := hz
    have hinv := HasDerivAt.inv
      (c := fun z : ℂ => z + (c : ℂ) * I) (x := (x : ℂ)) hbase hz'
    have hcomplex : HasDerivAt
        (fun z : ℂ => -((z + (c : ℂ) * I)⁻¹))
        (((x : ℂ) + (c : ℂ) * I)⁻¹ ^ 2) (x : ℂ) := by
      convert hinv.neg using 1
      all_goals field_simp
    exact hcomplex.comp_ofReal
  · apply Continuous.intervalIntegrable
    apply Continuous.pow
    apply Continuous.inv₀
    · fun_prop
    · intro x h
      have hi := congrArg Complex.im h
      norm_num at hi
      exact hc hi

private theorem vertical_inv_sq_integral
    (c a b : ℝ) (hc : c ≠ 0) :
    I * (∫ y : ℝ in a..b, ((c : ℂ) + (y : ℂ) * I)⁻¹ ^ 2) =
      -((c : ℂ) + (b : ℂ) * I)⁻¹ -
        (-((c : ℂ) + (a : ℂ) * I)⁻¹) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro y hy
    have hz : (c : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro h
      have hr := congrArg Complex.re h
      norm_num at hr
      exact hc hr
    have hbase : HasDerivAt (fun z : ℂ => (c : ℂ) + z * I) I (y : ℂ) := by
      simpa using ((hasDerivAt_id (x := (y : ℂ))).mul_const I).const_add (c : ℂ)
    have hz' : (fun z : ℂ => (c : ℂ) + z * I) (y : ℂ) ≠ 0 := hz
    have hinv := HasDerivAt.inv
      (c := fun z : ℂ => (c : ℂ) + z * I) (x := (y : ℂ)) hbase hz'
    have hcomplex : HasDerivAt
        (fun z : ℂ => -(((c : ℂ) + z * I)⁻¹))
        (I * (((c : ℂ) + (y : ℂ) * I)⁻¹ ^ 2)) (y : ℂ) := by
      convert hinv.neg using 1
      all_goals field_simp
    exact hcomplex.comp_ofReal
  · apply Continuous.intervalIntegrable
    apply Continuous.const_mul
    apply Continuous.pow
    apply Continuous.inv₀
    · fun_prop
    · intro y h
      have hr := congrArg Complex.re h
      norm_num at hr
      exact hc hr

/-- The double-pole kernel has zero integral around the finite rectangle. -/
theorem lemma57RectangleBoundaryIntegral_inv_sq
    (T : ℝ) (hT : 0 < T) :
    lemma57RectangleBoundaryIntegral (fun s : ℂ => s⁻¹ ^ 2) T = 0 := by
  have hbottom :
      (∫ x : ℝ in (-(1 : ℝ) / 2)..1,
          ((x : ℂ) - (T : ℂ) * I)⁻¹ ^ 2) =
        -(1 - (T : ℂ) * I)⁻¹ -
          (-((-(1 : ℝ) / 2 : ℂ) - (T : ℂ) * I)⁻¹) := by
    simpa [sub_eq_add_neg, neg_mul] using
      horizontal_inv_sq_integral (-T) (-(1 : ℝ) / 2) 1
        (neg_ne_zero.mpr hT.ne')
  have htop :
      (∫ x : ℝ in (-(1 : ℝ) / 2)..1,
          ((x : ℂ) + (T : ℂ) * I)⁻¹ ^ 2) =
        -(1 + (T : ℂ) * I)⁻¹ -
          (-((-(1 : ℝ) / 2 : ℂ) + (T : ℂ) * I)⁻¹) :=
    by
      simpa using horizontal_inv_sq_integral T (-(1 : ℝ) / 2) 1 hT.ne'
  have hright :
      I * (∫ y : ℝ in -T..T,
          (1 + (y : ℂ) * I)⁻¹ ^ 2) =
        -(1 + (T : ℂ) * I)⁻¹ -
          (-(1 - (T : ℂ) * I)⁻¹) := by
    convert vertical_inv_sq_integral 1 (-T) T one_ne_zero using 1
    all_goals push_cast
    all_goals ring
  have hleft :
      I * (∫ y : ℝ in -T..T,
          ((-(1 : ℝ) / 2 : ℂ) + (y : ℂ) * I)⁻¹ ^ 2) =
        -((-(1 : ℝ) / 2 : ℂ) + (T : ℂ) * I)⁻¹ -
          (-((-(1 : ℝ) / 2 : ℂ) - (T : ℂ) * I)⁻¹) :=
    by
      simpa using vertical_inv_sq_integral (-(1 : ℝ) / 2) (-T) T (by norm_num)
  unfold lemma57RectangleBoundaryIntegral
  rw [hbottom, htop, hright, hleft]
  ring

/-- The exact residue theorem for Zhang's genuine Mellin integrand on every
positive-height finite rectangle. -/
theorem lemma57RectangleBoundaryIntegral_mellinIntegrand
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (T : ℝ) (hT : 0 < T) :
    lemma57RectangleBoundaryIntegral (lemma57MellinIntegrand χ) T =
      2 * (Real.pi : ℂ) * I * lemma57ResidueValue χ := by
  let p : ℂ → ℂ := fun s => lemma57ResidueNumerator χ 0 * s⁻¹ ^ 2
  let q : ℂ → ℂ := fun s => lemma57ResidueValue χ * s⁻¹
  let r : ℂ → ℂ := lemma57EntireRemainder χ
  have hinv2 := lemma57RectangleBoundaryIntegrable_inv_pow 2 T hT
  have hinv1 := lemma57RectangleBoundaryIntegrable_inv_pow 1 T hT
  have hp : lemma57RectangleBoundaryIntegrable p T := by
    exact hinv2.const_mul (lemma57ResidueNumerator χ 0)
  have hq : lemma57RectangleBoundaryIntegrable q T := by
    simpa [q] using hinv1.const_mul (lemma57ResidueValue χ)
  have hr : lemma57RectangleBoundaryIntegrable r T := by
    apply lemma57RectangleBoundaryIntegrable_of_continuous
    exact (lemma57EntireRemainder_differentiable χ hD).continuous
  have hdecomp :
      lemma57RectangleBoundaryIntegral (lemma57MellinIntegrand χ) T =
        lemma57RectangleBoundaryIntegral (fun s => p s + q s + r s) T := by
    apply lemma57RectangleBoundaryIntegral_congr_of_ne_zero _ _ T hT
    intro s hs
    simpa [p, q, r] using
      lemma57MellinIntegrand_eq_inv_principalPart_add_remainder χ hD hs
  have hpB : lemma57RectangleBoundaryIntegral p T =
      lemma57ResidueNumerator χ 0 *
        lemma57RectangleBoundaryIntegral (fun s : ℂ => s⁻¹ ^ 2) T := by
    change lemma57RectangleBoundaryIntegral
      (fun s : ℂ => lemma57ResidueNumerator χ 0 * s⁻¹ ^ 2) T = _
    exact lemma57RectangleBoundaryIntegral_const_mul
      (lemma57ResidueNumerator χ 0) (fun s : ℂ => s⁻¹ ^ 2) T
  have hqB : lemma57RectangleBoundaryIntegral q T =
      lemma57ResidueValue χ *
        lemma57RectangleBoundaryIntegral (fun s : ℂ => s⁻¹) T := by
    change lemma57RectangleBoundaryIntegral
      (fun s : ℂ => lemma57ResidueValue χ * s⁻¹) T = _
    exact lemma57RectangleBoundaryIntegral_const_mul
      (lemma57ResidueValue χ) (fun s : ℂ => s⁻¹) T
  have hrB : lemma57RectangleBoundaryIntegral r T = 0 := by
    exact lemma57RectangleBoundaryIntegral_eq_zero_of_differentiable r
      (lemma57EntireRemainder_differentiable χ hD) T
  calc
    lemma57RectangleBoundaryIntegral (lemma57MellinIntegrand χ) T =
        lemma57RectangleBoundaryIntegral (fun s => p s + q s + r s) T := hdecomp
    _ = lemma57RectangleBoundaryIntegral (fun s => p s + q s) T +
        lemma57RectangleBoundaryIntegral r T := by
      exact lemma57RectangleBoundaryIntegral_add (hp.add hq) hr
    _ = (lemma57RectangleBoundaryIntegral p T +
          lemma57RectangleBoundaryIntegral q T) +
        lemma57RectangleBoundaryIntegral r T := by
      rw [lemma57RectangleBoundaryIntegral_add hp hq]
    _ = _ := by
      rw [hpB, hqB, hrB, lemma57RectangleBoundaryIntegral_inv_sq T hT,
        lemma57RectangleBoundaryIntegral_inv T hT]
      ring

/-- The finite-rectangle contour-shift obligation from Step 36 is now proved,
with no remaining contour hypothesis. -/
theorem lemma57FiniteRectangleShift_proved
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Lemma57FiniteRectangleShift χ := by
  rw [lemma57FiniteRectangleShift_iff_boundaryIntegral]
  intro T hT
  exact lemma57RectangleBoundaryIntegral_mellinIntegrand χ hD T hT

/-- After the finite residue theorem, only left-line integrability and
horizontal decay remain in the contour-shift layer. -/
theorem lemma57ContourShiftIdentity_of_left_integrable_horizontal_decay
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    (hleft : Lemma57VerticalIntegrable χ (-(1 : ℝ) / 2))
    (hhorizontal : Lemma57HorizontalDecay χ) :
    Lemma57ContourShiftIdentity χ :=
  lemma57ContourShiftIdentity_of_finite_rectangles χ hD hleft
    (lemma57FiniteRectangleShift_proved χ hD) hhorizontal

end ZhangLS.Spec
