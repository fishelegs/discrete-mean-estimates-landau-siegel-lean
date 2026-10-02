import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.Order
import Mathlib.Tactic.Ring

/-!
# A finite-factor argument-principle component for Lemma 2.3

The full Rouché theorem is not available in Mathlib.  This file develops one of its analytic
ingredients: for an explicit finite product of linear factors times an analytic, zero-free factor,
the contour integral of the logarithmic derivative counts the enclosed linear factors.
-/

namespace ZhangLS.Spec

open Complex Metric

/-- A finite product of linear factors indexed by distinct roots. -/
noncomputable def lemma23LinearRootProduct (roots : Finset ℂ) : ℂ → ℂ :=
  fun z => ∏ a ∈ roots, (z - a)

/-- The logarithmic derivative of the finite root product is the sum of the simple-pole kernels,
away from its roots. -/
theorem lemma23_logDeriv_linear_root_product
    (roots : Finset ℂ) (z : ℂ) (hne : ∀ a ∈ roots, z ≠ a) :
    logDeriv (lemma23LinearRootProduct roots) z = ∑ a ∈ roots, (z - a)⁻¹ := by
  have h := logDeriv_prod (s := roots) (f := fun a z : ℂ => z - a) (x := z)
    (fun a ha => sub_ne_zero.mpr (hne a ha))
    (fun a ha => by fun_prop)
  simpa [lemma23LinearRootProduct, logDeriv, deriv_sub_const] using h

/-- A finite root product with a specified (possibly non-constant) multiplicity at each root. -/
noncomputable def lemma23WeightedRootProduct (roots : Finset ℂ) (m : ℂ → ℕ) : ℂ → ℂ :=
  fun z => ∏ a ∈ roots, (z - a) ^ m a

/-- The logarithmic derivative of a finite root product records the multiplicity of each root. -/
theorem lemma23_logDeriv_weighted_root_product
    (roots : Finset ℂ) (m : ℂ → ℕ) (z : ℂ)
    (hne : ∀ a ∈ roots, z ≠ a) :
    logDeriv (lemma23WeightedRootProduct roots m) z =
      ∑ a ∈ roots, (m a : ℂ) * (z - a)⁻¹ := by
  unfold lemma23WeightedRootProduct
  have h := logDeriv_prod (s := roots)
    (f := fun a z : ℂ => (z - a) ^ m a) (x := z)
    (fun a ha => pow_ne_zero _ (sub_ne_zero.mpr (hne a ha)))
    (fun a ha => by fun_prop)
  have hsum :
      logDeriv (fun z : ℂ => ∏ a ∈ roots, (z - a) ^ m a) z =
        ∑ a ∈ roots, (m a : ℂ) * (z - a)⁻¹ := by
    rw [h]
    apply Finset.sum_congr rfl
    intro a ha
    rw [logDeriv_fun_pow (by fun_prop)]
    simp [logDeriv, div_eq_mul_inv, mul_comm]
  exact hsum

/-- The logarithmic derivative of a zero-free analytic function has zero integral around a disk.
This is the Cauchy theorem applied to the analytic function `g'/g`. -/
theorem lemma23_circleIntegral_logDeriv_zero_of_analytic_nonzero
    {R : ℝ} (hR : 0 < R) (g : ℂ → ℂ)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hgne : ∀ z ∈ closedBall 0 R, g z ≠ 0) :
    (∮ z in C(0, R), logDeriv g z) = 0 := by
  have hlog : AnalyticOnNhd ℂ (logDeriv g) (closedBall 0 R) := by
    intro z hz
    have h := (hg z hz).deriv.div (hg z hz) (hgne z hz)
    simpa [logDeriv] using h
  exact Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable hR.le
    Set.countable_empty hlog.continuousOn (fun z hz =>
      (hlog z (Metric.ball_subset_closedBall hz.1)).differentiableAt)

/-- Argument-principle identity for an explicitly factored analytic function: each simple linear
factor with its root inside the disk contributes `2πi`, while the zero-free analytic factor
contributes zero. -/
theorem lemma23_circleIntegral_logDeriv_finite_product
    {R : ℝ} (hR : 0 < R) (roots : Finset ℂ) (g : ℂ → ℂ)
    (hroots : ∀ a ∈ roots, a ∈ ball (0 : ℂ) R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hgne : ∀ z ∈ closedBall 0 R, g z ≠ 0) :
    (∮ z in C(0, R),
      logDeriv (fun z => lemma23LinearRootProduct roots z * g z) z) =
        (2 * Real.pi * Complex.I) * (roots.card : ℂ) := by
  let f : ℂ → ℂ := fun z => lemma23LinearRootProduct roots z * g z
  have hrootsBoundary : ∀ z ∈ sphere (0 : ℂ) R, ∀ a ∈ roots, z ≠ a := by
    intro z hz a ha hza
    have hzR : ‖z‖ = R := by simpa using hz
    have haR : ‖a‖ < R := by simpa using hroots a ha
    rw [hza] at hzR
    linarith
  have hprodne : ∀ z ∈ sphere (0 : ℂ) R,
      lemma23LinearRootProduct roots z ≠ 0 := by
    intro z hz
    unfold lemma23LinearRootProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact sub_ne_zero.mpr (hrootsBoundary z hz a ha)
  have hglog : AnalyticOnNhd ℂ (logDeriv g) (closedBall 0 R) := by
    intro z hz
    have h := (hg z hz).deriv.div (hg z hz) (hgne z hz)
    simpa [logDeriv] using h
  have hpoint : ∀ z ∈ sphere (0 : ℂ) R,
      logDeriv f z =
        (∑ a ∈ roots, (z - a)⁻¹) + logDeriv g z := by
    intro z hz
    have hfactor := lemma23_logDeriv_linear_root_product roots z (hrootsBoundary z hz)
    have hprodDiff : DifferentiableAt ℂ (lemma23LinearRootProduct roots) z := by
      unfold lemma23LinearRootProduct
      fun_prop
    have hgDiff : DifferentiableAt ℂ g z := (hg z (sphere_subset_closedBall hz)).differentiableAt
    have hprod : lemma23LinearRootProduct roots z ≠ 0 := hprodne z hz
    have hgval : g z ≠ 0 := hgne z (sphere_subset_closedBall hz)
    change logDeriv (fun z => lemma23LinearRootProduct roots z * g z) z = _
    rw [logDeriv_mul z hprod hgval hprodDiff hgDiff, hfactor]
  have hsumInt : CircleIntegrable (fun z : ℂ => ∑ a ∈ roots, (z - a)⁻¹) 0 R := by
    apply CircleIntegrable.fun_sum
    intro a ha
    have hcont : ContinuousOn (fun z : ℂ => (z - a)⁻¹) (sphere 0 R) := by
      apply ContinuousOn.inv₀ (by fun_prop)
      intro z hz
      exact sub_ne_zero.mpr (hrootsBoundary z hz a ha)
    exact hcont.circleIntegrable hR.le
  have hlogInt : CircleIntegrable (logDeriv g) 0 R :=
    (hglog.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hsumFormula :
      (∮ z in C(0, R), ∑ a ∈ roots, (z - a)⁻¹) =
        ∑ a ∈ roots, ∮ z in C(0, R), (z - a)⁻¹ := by
    apply circleIntegral.integral_fun_sum
    intro a ha
    have hcont : ContinuousOn (fun z : ℂ => (z - a)⁻¹) (sphere 0 R) := by
      apply ContinuousOn.inv₀ (by fun_prop)
      intro z hz
      exact sub_ne_zero.mpr (hrootsBoundary z hz a ha)
    exact hcont.circleIntegrable hR.le
  have hterm (a : ℂ) (ha : a ∈ roots) :
      (∮ z in C(0, R), (z - a)⁻¹) = 2 * Real.pi * Complex.I := by
    exact circleIntegral.integral_sub_inv_of_mem_ball (hroots a ha)
  have hsumTerms :
      (∑ a ∈ roots, ∮ z in C(0, R), (z - a)⁻¹) =
        (roots.card : ℂ) * (2 * Real.pi * Complex.I) := by
    calc
      _ = ∑ a ∈ roots, (2 * Real.pi * Complex.I) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hterm a ha
      _ = (roots.card : ℂ) * (2 * Real.pi * Complex.I) := by simp
  calc
    (∮ z in C(0, R), logDeriv f z) =
        ∮ z in C(0, R), (∑ a ∈ roots, (z - a)⁻¹) + logDeriv g z := by
      apply circleIntegral.integral_congr hR.le
      exact hpoint
    _ = (∮ z in C(0, R), ∑ a ∈ roots, (z - a)⁻¹) +
        (∮ z in C(0, R), logDeriv g z) := by
      exact circleIntegral.integral_add hsumInt hlogInt
    _ = (2 * Real.pi * Complex.I) * (roots.card : ℂ) := by
      rw [hsumFormula, lemma23_circleIntegral_logDeriv_zero_of_analytic_nonzero hR g hg hgne]
      rw [hsumTerms]
      ring

/-- Argument principle for a finite factorization with arbitrary zero multiplicities. -/
theorem lemma23_circleIntegral_logDeriv_weighted_finite_product
    {R : ℝ} (hR : 0 < R) (roots : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ)
    (hroots : ∀ a ∈ roots, a ∈ ball (0 : ℂ) R)
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hgne : ∀ z ∈ closedBall 0 R, g z ≠ 0) :
    (∮ z in C(0, R),
      logDeriv (fun z => lemma23WeightedRootProduct roots m z * g z) z) =
        (2 * Real.pi * Complex.I) * ∑ a ∈ roots, (m a : ℂ) := by
  let f : ℂ → ℂ := fun z => lemma23WeightedRootProduct roots m z * g z
  have hrootsBoundary : ∀ z ∈ sphere (0 : ℂ) R, ∀ a ∈ roots, z ≠ a := by
    intro z hz a ha hza
    have hzR : ‖z‖ = R := by simpa using hz
    have haR : ‖a‖ < R := by simpa using hroots a ha
    rw [hza] at hzR
    linarith
  have hprodne : ∀ z ∈ sphere (0 : ℂ) R,
      lemma23WeightedRootProduct roots m z ≠ 0 := by
    intro z hz
    unfold lemma23WeightedRootProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    exact pow_ne_zero _ (sub_ne_zero.mpr (hrootsBoundary z hz a ha))
  have hglog : AnalyticOnNhd ℂ (logDeriv g) (closedBall 0 R) := by
    intro z hz
    have h := (hg z hz).deriv.div (hg z hz) (hgne z hz)
    simpa [logDeriv] using h
  have hpoint : ∀ z ∈ sphere (0 : ℂ) R,
      logDeriv f z =
        (∑ a ∈ roots, (m a : ℂ) * (z - a)⁻¹) + logDeriv g z := by
    intro z hz
    have hfactor := lemma23_logDeriv_weighted_root_product roots m z (hrootsBoundary z hz)
    have hprodDiff : DifferentiableAt ℂ (lemma23WeightedRootProduct roots m) z := by
      unfold lemma23WeightedRootProduct
      fun_prop
    have hgDiff : DifferentiableAt ℂ g z := (hg z (sphere_subset_closedBall hz)).differentiableAt
    have hprod : lemma23WeightedRootProduct roots m z ≠ 0 := hprodne z hz
    have hgval : g z ≠ 0 := hgne z (sphere_subset_closedBall hz)
    change logDeriv (fun z => lemma23WeightedRootProduct roots m z * g z) z = _
    rw [logDeriv_mul z hprod hgval hprodDiff hgDiff, hfactor]
  have hsumInt : CircleIntegrable
      (fun z : ℂ => ∑ a ∈ roots, (m a : ℂ) * (z - a)⁻¹) 0 R := by
    apply CircleIntegrable.fun_sum
    intro a ha
    have hcont : ContinuousOn (fun z : ℂ => (m a : ℂ) * (z - a)⁻¹) (sphere 0 R) := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ (by fun_prop)
      intro z hz
      exact sub_ne_zero.mpr (hrootsBoundary z hz a ha)
    exact hcont.circleIntegrable hR.le
  have hlogInt : CircleIntegrable (logDeriv g) 0 R :=
    (hglog.continuousOn.mono sphere_subset_closedBall).circleIntegrable hR.le
  have hsumFormula :
      (∮ z in C(0, R), ∑ a ∈ roots, (m a : ℂ) * (z - a)⁻¹) =
        ∑ a ∈ roots, ∮ z in C(0, R), (m a : ℂ) * (z - a)⁻¹ := by
    apply circleIntegral.integral_fun_sum
    intro a ha
    have hcont : ContinuousOn (fun z : ℂ => (m a : ℂ) * (z - a)⁻¹) (sphere 0 R) := by
      apply ContinuousOn.mul continuousOn_const
      apply ContinuousOn.inv₀ (by fun_prop)
      intro z hz
      exact sub_ne_zero.mpr (hrootsBoundary z hz a ha)
    exact hcont.circleIntegrable hR.le
  have hterm (a : ℂ) (ha : a ∈ roots) :
      (∮ z in C(0, R), (m a : ℂ) * (z - a)⁻¹) =
        (m a : ℂ) * (2 * Real.pi * Complex.I) := by
    have hcont : ContinuousOn (fun z : ℂ => (z - a)⁻¹) (sphere 0 R) := by
      apply ContinuousOn.inv₀ (by fun_prop)
      intro z hz
      exact sub_ne_zero.mpr (hrootsBoundary z hz a ha)
    have hInt := hcont.circleIntegrable hR.le
    calc
      _ = (∮ z in C(0, R), (z - a)⁻¹) • (m a : ℂ) := by
        rw [← circleIntegral.integral_smul_const]
        apply circleIntegral.integral_congr hR.le
        intro z hz
        simp [smul_eq_mul, mul_comm]
      _ = (m a : ℂ) • (∮ z in C(0, R), (z - a)⁻¹) := by
        simp [smul_eq_mul, mul_comm]
      _ = (m a : ℂ) * (2 * Real.pi * Complex.I) := by
        rw [circleIntegral.integral_sub_inv_of_mem_ball (hroots a ha)]
        simp [smul_eq_mul]
  have hsumTerms :
      (∑ a ∈ roots, ∮ z in C(0, R), (m a : ℂ) * (z - a)⁻¹) =
        (2 * Real.pi * Complex.I) * ∑ a ∈ roots, (m a : ℂ) := by
    calc
      _ = ∑ a ∈ roots, (m a : ℂ) * (2 * Real.pi * Complex.I) := by
        apply Finset.sum_congr rfl
        intro a ha
        exact hterm a ha
      _ = (∑ a ∈ roots, (m a : ℂ)) * (2 * Real.pi * Complex.I) := by
        rw [Finset.sum_mul]
      _ = _ := by ring
  calc
    (∮ z in C(0, R), logDeriv f z) =
        ∮ z in C(0, R), (∑ a ∈ roots, (m a : ℂ) * (z - a)⁻¹) + logDeriv g z := by
      apply circleIntegral.integral_congr hR.le
      exact hpoint
    _ = (∮ z in C(0, R), ∑ a ∈ roots, (m a : ℂ) * (z - a)⁻¹) +
        (∮ z in C(0, R), logDeriv g z) := by
      exact circleIntegral.integral_add hsumInt hlogInt
    _ = (2 * Real.pi * Complex.I) * ∑ a ∈ roots, (m a : ℂ) := by
      rw [hsumFormula, lemma23_circleIntegral_logDeriv_zero_of_analytic_nonzero hR g hg hgne]
      simpa using hsumTerms

end ZhangLS.Spec
