import ZhangLS.Spec.Lemma57MellinContour

/-!
# Analyticity and the local contour integral in Zhang's Lemma 5.7

This module proves that the pole-removed numerator is entire and that Zhang's
Mellin integrand is analytic away from its sole displayed singularity at zero.
It then applies the Cauchy formula for the first derivative to compute the
normalized integral around every centered circle: the answer is exactly the
residue value already calculated at zero.

This separates the local residue theorem from the remaining global contour
deformation between a small circle and the finite rectangle.
-/

namespace ZhangLS.Spec

open Complex MeasureTheory Filter Set
open scoped Real Topology

/-- The continuously filled factor `s * ζ(1+s)` is complex differentiable on
the whole plane. -/
theorem lemma57RegularizedZeta_differentiable :
    Differentiable ℂ lemma57RegularizedZeta := by
  intro s
  by_cases hs : s = 0
  · subst s
    exact lemma57RegularizedZeta_hasDerivAt_zero.differentiableAt
  · have heq : lemma57RegularizedZeta =ᶠ[𝓝 s]
        (fun z : ℂ => z * riemannZeta (1 + z)) := by
      filter_upwards [isOpen_ne.mem_nhds hs] with z hz
      simp [lemma57RegularizedZeta, hz]
    have hshift : DifferentiableAt ℂ (fun z : ℂ => 1 + z) s := by
      fun_prop
    have hzeta : DifferentiableAt ℂ riemannZeta (1 + s) :=
      differentiableAt_riemannZeta (by simpa using hs)
    apply (differentiableAt_id.mul (hzeta.comp s hshift)).congr_of_eventuallyEq
    exact heq

/-- The one-exponential Gaussian Mellin factor is entire. -/
theorem lemma57GaussianMellinFactor_differentiable (D : ℕ) :
    Differentiable ℂ (lemma57GaussianMellinFactor D) := by
  unfold lemma57GaussianMellinFactor
  fun_prop

/-- The numerator obtained after removing the double pole is entire. -/
theorem lemma57ResidueNumerator_differentiable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Differentiable ℂ (lemma57ResidueNumerator χ) := by
  unfold lemma57ResidueNumerator
  exact ((lemma57RegularizedZeta_differentiable.mul
    ((differentiable_dirichletLFunction_of_one_lt_modulus χ hD).comp
      ((differentiable_const (c := (1 : ℂ))).add differentiable_id))).mul
        (lemma57GaussianMellinFactor_differentiable D))

/-- Analytic form of the global pole-removed numerator statement. -/
theorem lemma57ResidueNumerator_analyticOnNhd
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    AnalyticOnNhd ℂ (lemma57ResidueNumerator χ) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  exact lemma57ResidueNumerator_differentiable χ hD

/-- The genuine Mellin integrand is complex differentiable at every nonzero
point. -/
theorem lemma57MellinIntegrand_differentiableAt
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : s ≠ 0) :
    DifferentiableAt ℂ (lemma57MellinIntegrand χ) s := by
  have heq : lemma57MellinIntegrand χ =ᶠ[𝓝 s]
      (fun z => lemma57ResidueNumerator χ z / z ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hs] with z hz
    exact lemma57MellinIntegrand_eq_residueNumerator_div_sq χ hz
  apply (((lemma57ResidueNumerator_differentiable χ hD).differentiableAt.div
    (differentiableAt_id.pow 2) (pow_ne_zero 2 hs))).congr_of_eventuallyEq
  exact heq

/-- Analytic form of the statement that zero is the only possible singularity
of the displayed Mellin integrand. -/
theorem lemma57MellinIntegrand_analyticAt
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {s : ℂ} (hs : s ≠ 0) :
    AnalyticAt ℂ (lemma57MellinIntegrand χ) s := by
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  filter_upwards [isOpen_ne.mem_nhds hs] with z hz
  exact lemma57MellinIntegrand_differentiableAt χ hD hz

/-- On every positive-radius centered circle, the actual singular integrand is
honestly circle-integrable. -/
theorem lemma57MellinIntegrand_circleIntegrable
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {R : ℝ} (hR : 0 < R) :
    CircleIntegrable (lemma57MellinIntegrand χ) 0 R := by
  apply ContinuousOn.circleIntegrable'
  intro s hsphere
  apply (lemma57MellinIntegrand_differentiableAt χ hD ?_).continuousAt.continuousWithinAt
  intro hs0
  subst s
  have hzero : (0 : ℝ) = R := by
    simpa [abs_of_pos hR] using hsphere
  exact hR.ne' hzero.symm

/-- The normalized contour integral of Zhang's genuine Mellin integrand around
the centered circle of radius `R`. -/
noncomputable def lemma57NormalizedCircleIntegral {D : ℕ}
    (χ : RealPrimitiveCharacter D) (R : ℝ) : ℂ :=
  (2 * (Real.pi : ℂ) * I)⁻¹ *
    ∮ s in C(0, R), lemma57MellinIntegrand χ s

/-- The normalized integral around every positive centered circle is exactly
the coefficient of `s⁻¹` at zero.  This is the local residue theorem needed
for the finite contour shift. -/
theorem lemma57NormalizedCircleIntegral_eq_residueValue
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D)
    {R : ℝ} (hR : 0 < R) :
    lemma57NormalizedCircleIntegral χ R = lemma57ResidueValue χ := by
  have hcircle := DifferentiableOn.deriv_eq_smul_circleIntegral
    (c := (0 : ℂ)) hR
    (lemma57ResidueNumerator_differentiable χ hD).differentiableOn
  have hintegral :
      (∮ s in C(0, R), lemma57MellinIntegrand χ s) =
        ∮ s in C(0, R),
          (1 / (s - 0) ^ 2) • lemma57ResidueNumerator χ s := by
    apply circleIntegral.integral_congr hR.le
    intro s hsphere
    have hs : s ≠ 0 := by
      intro hs0
      subst s
      have hzero : (0 : ℝ) = R := by simpa using hsphere
      exact hR.ne' hzero.symm
    rw [lemma57MellinIntegrand_eq_residueNumerator_div_sq χ hs]
    simp [div_eq_mul_inv, smul_eq_mul]
    ring
  have hderiv : deriv (lemma57ResidueNumerator χ) 0 =
      lemma57ResidueValue χ :=
    (lemma57ResidueNumerator_hasDerivAt_zero χ hD).deriv
  unfold lemma57NormalizedCircleIntegral
  rw [hintegral, hcircle, hderiv]
  simp only [smul_eq_mul]
  field_simp

end ZhangLS.Spec
