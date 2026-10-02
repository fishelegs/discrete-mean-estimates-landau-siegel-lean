import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Complex.BranchLogRoot

/-!
# Analyticity of a continuous logarithm lift

Mathlib constructs continuous logarithm branches on simply connected zero-free domains.  This
module supplies the missing local analytic upgrade: a continuous lift through `Complex.exp` agrees
near each point with the principal logarithm of a normalized quotient, and hence has logarithmic
derivative `g'/g`.
-/

namespace ZhangLS.Spec

open Filter Set
open scoped Topology

/-- A continuous lift through the complex exponential of a differentiable nonvanishing function
is differentiable, with derivative `g'/g`.  The proof uses the local injectivity of the exponential
on its principal strip, not an assumed analytic branch. -/
theorem lemma23_hasDerivAt_of_continuous_exp_lift
    {U : Set ℂ} (hUopen : IsOpen U) {a g' : ℂ} {g ℓ : ℂ → ℂ}
    (ha : a ∈ U) (hℓcont : ContinuousOn ℓ U)
    (hlift : ∀ z ∈ U, Complex.exp (ℓ z) = g z)
    (hg : HasDerivAt g g' a) (hgne : g a ≠ 0) :
    HasDerivAt ℓ (g' / g a) a := by
  let q : ℂ → ℂ := fun z => g z / g a
  have hℓat : ContinuousAt ℓ a :=
    hℓcont.continuousAt (hUopen.mem_nhds ha)
  have hqAt : ContinuousAt q a := by
    simpa [q] using hg.continuousAt.div_const (g a)
  have hqa : q a = 1 := by simp [q, hgne]
  have hstripZero : (0 : ℂ) ∈ Complex.expOpenPartialHomeomorph.source := by
    change (0 : ℝ) ∈ Set.Ioo (-Real.pi) Real.pi
    exact ⟨neg_lt_zero.mpr Real.pi_pos, Real.pi_pos⟩
  have hdiffCont : ContinuousAt (fun z : ℂ => ℓ z - ℓ a) a := by
    exact hℓat.sub continuousAt_const
  have hstrip : ∀ᶠ z in 𝓝 a,
      ℓ z - ℓ a ∈ Complex.expOpenPartialHomeomorph.source :=
    hdiffCont.eventually (Complex.expOpenPartialHomeomorph.open_source.mem_nhds (by simp [hstripZero]))
  have hball : ∀ᶠ z in 𝓝 a, q z ∈ Metric.ball (1 : ℂ) 1 :=
    hqAt.eventually (Metric.isOpen_ball.mem_nhds (by simpa [hqa]))
  have htarget : ∀ᶠ z in 𝓝 a, q z ∈ Complex.slitPlane := by
    filter_upwards [hball] with z hz
    exact Complex.ball_one_subset_slitPlane hz
  have hlocal : (fun z : ℂ => ℓ a + Complex.log (q z)) =ᶠ[𝓝 a] ℓ := by
    filter_upwards [hUopen.mem_nhds ha, hstrip, htarget] with z hz hstripz htargetz
    have hratio : Complex.exp (ℓ z - ℓ a) = q z := by
      dsimp [q]
      rw [Complex.exp_sub, hlift z hz, hlift a ha]
    have hlogexp : Complex.exp (Complex.log (q z)) = q z :=
      Complex.exp_log (Complex.slitPlane_ne_zero htargetz)
    have hlogstrip : Complex.log (q z) ∈ Complex.expOpenPartialHomeomorph.source :=
      Complex.expOpenPartialHomeomorph.map_target' htargetz
    have hdiff := Complex.expOpenPartialHomeomorph.injOn hstripz hlogstrip
      (hratio.trans hlogexp.symm)
    have hzEq : ℓ z = ℓ a + Complex.log (q z) := by
      calc
        ℓ z = (ℓ z - ℓ a) + ℓ a := by ring
        _ = Complex.log (q z) + ℓ a := by rw [hdiff]
        _ = ℓ a + Complex.log (q z) := by ring
    exact hzEq.symm
  have hqderiv : HasDerivAt q (g' / g a) a := by
    simpa [q] using hg.div_const (g a)
  have hlogderiv : HasDerivAt (fun z : ℂ => Complex.log (q z)) (g' / g a) a := by
    have hqtarget : q a ∈ Complex.slitPlane :=
      Complex.ball_one_subset_slitPlane (by simpa [hqa])
    simpa [hqa] using hqderiv.clog hqtarget
  have hmodel : HasDerivAt (fun z : ℂ => ℓ a + Complex.log (q z)) (g' / g a) a := by
    simpa only [zero_add] using (hasDerivAt_const a (ℓ a)).add hlogderiv
  exact hmodel.congr_of_eventuallyEq hlocal.symm

/-- The corresponding derivative formula expressed using `deriv`. -/
theorem lemma23_deriv_of_continuous_exp_lift
    {U : Set ℂ} (hUopen : IsOpen U) {a : ℂ} {g ℓ : ℂ → ℂ}
    (ha : a ∈ U) (hℓcont : ContinuousOn ℓ U)
    (hlift : ∀ z ∈ U, Complex.exp (ℓ z) = g z)
    (hg : DifferentiableAt ℂ g a) (hgne : g a ≠ 0) :
    deriv ℓ a = deriv g a / g a := by
  exact (lemma23_hasDerivAt_of_continuous_exp_lift hUopen ha hℓcont hlift
    hg.hasDerivAt hgne).deriv

/-- On a simply connected open zero-free domain, the continuous logarithm branch supplied by
Mathlib is in fact analytic, with derivative `g'/g` at every point. -/
theorem lemma23_exists_analytic_log_branch
    {U : Set ℂ} (hUc : IsSimplyConnected U) (hUopen : IsOpen U)
    {g : ℂ → ℂ} (hgcont : ContinuousOn g U) (hgne : ∀ z ∈ U, g z ≠ 0)
    (hgdif : ∀ z ∈ U, DifferentiableAt ℂ g z) :
    ∃ ℓ : ℂ → ℂ, ContinuousOn ℓ U ∧
      (∀ z ∈ U, Complex.exp (ℓ z) = g z) ∧
      (∀ z ∈ U, HasDerivAt ℓ (deriv g z / g z) z) := by
  obtain ⟨ℓ, hℓcont, hlift⟩ :=
    Complex.exists_continuousOn_eqOn_exp_comp hUc hUopen hgcont (by
      intro hz
      rcases hz with ⟨z, hzu, hz0⟩
      exact hgne z hzu hz0)
  refine ⟨ℓ, hℓcont, ?_, ?_⟩
  · intro z hz
    simpa only [Function.comp_apply] using (hlift hz)
  · intro z hz
    exact lemma23_hasDerivAt_of_continuous_exp_lift hUopen hz hℓcont
      (fun w hw => by simpa only [Function.comp_apply] using hlift hw)
      (hgdif z hz).hasDerivAt (hgne z hz)

end ZhangLS.Spec
