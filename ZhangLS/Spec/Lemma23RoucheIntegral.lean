import ZhangLS.Spec.Lemma23ArgumentPrinciple
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The boundary-homotopy component of Rouché's theorem for Lemma 2.3

If two analytic functions satisfy strict Rouché dominance on a circle, their quotient stays
inside the unit disk centered at `1` along the boundary. The principal logarithm of that quotient
then closes up after one circuit, forcing the difference of logarithmic-derivative integrals to
vanish. This file formalizes that contour-integral invariance; it is combined with the general
argument principle in `Lemma23GeneralArgumentPrinciple.lean` to obtain equality of interior zero
counts with multiplicity.
-/

namespace ZhangLS.Spec

open Complex Metric MeasureTheory

/-- Strict Rouché dominance on a circle makes the quotient's logarithmic derivative have zero
contour integral. -/
theorem lemma23_circleIntegral_logDeriv_eq_of_boundary_close
    {R : ℝ} (hR : 0 < R) (f g : ℂ → ℂ)
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (hg : AnalyticOnNhd ℂ g (closedBall 0 R))
    (hclose : ∀ z ∈ sphere (0 : ℂ) R, ‖f z - g z‖ < ‖g z‖) :
    (∮ z in C(0, R), logDeriv f z) = (∮ z in C(0, R), logDeriv g z) := by
  let q : ℂ → ℂ := fun z => f z / g z
  have hgne : ∀ z ∈ sphere (0 : ℂ) R, g z ≠ 0 := by
    intro z hz hgz
    have h := hclose z hz
    rw [hgz, norm_zero] at h
    exact (not_lt_of_ge (norm_nonneg _)) h
  have hqAnalytic : ∀ z ∈ sphere (0 : ℂ) R, AnalyticAt ℂ q z := by
    intro z hz
    dsimp [q]
    exact (hf z (sphere_subset_closedBall hz)).div
      (hg z (sphere_subset_closedBall hz)) (hgne z hz)
  have hqClose : ∀ z ∈ sphere (0 : ℂ) R, ‖q z - 1‖ < 1 := by
    intro z hz
    have hq : q z - 1 = (f z - g z) / g z := by
      dsimp [q]
      field_simp [hgne z hz]
    rw [hq, norm_div]
    apply (div_lt_iff₀ (norm_pos_iff.mpr (hgne z hz))).2
    simpa using hclose z hz
  have hqSlit : ∀ z ∈ sphere (0 : ℂ) R, q z ∈ Complex.slitPlane := by
    intro z hz
    have h := Complex.mem_slitPlane_of_norm_lt_one (hqClose z hz)
    have hrepr : q z = 1 + (q z - 1) := by ring
    rw [hrepr]
    exact h
  have hqne : ∀ z ∈ sphere (0 : ℂ) R, q z ≠ 0 := by
    intro z hz
    exact Complex.slitPlane_ne_zero (hqSlit z hz)
  have hratioPoint : ∀ z ∈ sphere (0 : ℂ) R,
      logDeriv q z = logDeriv f z - logDeriv g z := by
    intro z hz
    have hfne : f z ≠ 0 := by
      intro hfz
      have h := hclose z hz
      rw [hfz, zero_sub, norm_neg] at h
      exact (lt_irrefl _) h
    exact logDeriv_div z hfne (hgne z hz)
      (hf z (sphere_subset_closedBall hz)).differentiableAt
      (hg z (sphere_subset_closedBall hz)).differentiableAt
  have hlogfAnalytic : ∀ z ∈ sphere (0 : ℂ) R, AnalyticAt ℂ (logDeriv f) z := by
    intro z hz
    have hfne : f z ≠ 0 := by
      intro hfz
      have h := hclose z hz
      rw [hfz, zero_sub, norm_neg] at h
      exact (lt_irrefl _) h
    exact (hf z (sphere_subset_closedBall hz)).deriv.div
      (hf z (sphere_subset_closedBall hz)) hfne
  have hloggAnalytic : ∀ z ∈ sphere (0 : ℂ) R, AnalyticAt ℂ (logDeriv g) z := by
    intro z hz
    exact (hg z (sphere_subset_closedBall hz)).deriv.div
      (hg z (sphere_subset_closedBall hz)) (hgne z hz)
  have hlogqAnalytic : ∀ z ∈ sphere (0 : ℂ) R, AnalyticAt ℂ (logDeriv q) z := by
    intro z hz
    exact (hqAnalytic z hz).deriv.div (hqAnalytic z hz) (hqne z hz)
  have hlogfInt : CircleIntegrable (logDeriv f) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact (hlogfAnalytic z hz).continuousAt.continuousWithinAt
  have hloggInt : CircleIntegrable (logDeriv g) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact (hloggAnalytic z hz).continuousAt.continuousWithinAt
  have hlogqInt : CircleIntegrable (logDeriv q) 0 R := by
    apply ContinuousOn.circleIntegrable hR.le
    intro z hz
    exact (hlogqAnalytic z hz).continuousAt.continuousWithinAt
  let loopLog : ℝ → ℂ := fun θ => Complex.log (q (circleMap 0 R θ))
  have hloopDeriv : ∀ θ ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      HasDerivAt loopLog
        (deriv (circleMap 0 R) θ * logDeriv q (circleMap 0 R θ)) θ := by
    intro θ hθ
    have hz : circleMap 0 R θ ∈ sphere (0 : ℂ) R := circleMap_mem_sphere 0 hR.le θ
    have hcircle : HasDerivAt (circleMap 0 R) (deriv (circleMap 0 R) θ) θ :=
      (differentiable_circleMap 0 R θ).hasDerivAt
    have hq : HasDerivAt (fun t : ℝ => q (circleMap 0 R t))
        (deriv q (circleMap 0 R θ) * deriv (circleMap 0 R) θ) θ :=
      (hqAnalytic _ hz).differentiableAt.hasDerivAt.comp θ hcircle
    have hlog := hq.clog_real (hqSlit _ hz)
    convert hlog using 1
    simp [logDeriv]
    field_simp [hqne _ hz]
  have hqIntegralZero : (∮ z in C(0, R), logDeriv q z) = 0 := by
    have hint : IntervalIntegrable
        (fun θ : ℝ => deriv (circleMap 0 R) θ * logDeriv q (circleMap 0 R θ))
        volume 0 (2 * Real.pi) := by
      simpa [smul_eq_mul] using hlogqInt.out
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hloopDeriv hint
    change (∫ θ : ℝ in 0..2 * Real.pi,
      deriv (circleMap 0 R) θ • logDeriv q (circleMap 0 R θ)) = 0
    calc
      _ = loopLog (2 * Real.pi) - loopLog 0 := by
        simpa [smul_eq_mul] using hFTC
      _ = 0 := by
        have hperiod : circleMap 0 R (2 * Real.pi) = circleMap 0 R 0 := by
          simpa using (periodic_circleMap 0 R) 0
        simp [loopLog, hperiod]
  have hratioIntegral :
      (∮ z in C(0, R), logDeriv q z) =
        (∮ z in C(0, R), logDeriv f z) - (∮ z in C(0, R), logDeriv g z) := by
    calc
      _ = (∮ z in C(0, R), logDeriv f z - logDeriv g z) := by
        apply circleIntegral.integral_congr hR.le
        exact hratioPoint
      _ = _ := circleIntegral.integral_sub hlogfInt hloggInt
  rw [hqIntegralZero] at hratioIntegral
  exact sub_eq_zero.mp hratioIntegral.symm

end ZhangLS.Spec
