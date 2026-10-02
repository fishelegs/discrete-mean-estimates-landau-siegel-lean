import ZhangLS.Spec.RealDirichletCharacter
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.DirichletContinuation

/-!
# Trusted specification: Dirichlet L-series and analytic L-functions

This module deliberately reuses mathlib's L-series and analytic-continuation
infrastructure.  In particular, `L(1, χ)` is *not* defined by the naive series:
that series is not absolutely convergent at `s = 1`.
-/

namespace ZhangLS.Spec

open RealPrimitiveCharacter

/-- The coefficient sequence attached to a real primitive Dirichlet character. -/
noncomputable def dirichletCoeffs {D : ℕ} (χ : RealPrimitiveCharacter D) : ℕ → ℂ :=
  fun n => χ.chi (n : ZMod D)

/-- The naive Dirichlet L-series.  It is used only in its convergence region. -/
noncomputable def dirichletLSeries {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) : ℂ :=
  LSeries (dirichletCoeffs χ) s

/-- Absolute convergence of the naive Dirichlet L-series on `re(s) > 1`. -/
theorem dirichletLSeries_summable_of_one_lt_re {D : ℕ}
    (χ : RealPrimitiveCharacter D) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (dirichletCoeffs χ) s := by
  exact χ.chi.LSeriesSummable_of_one_lt_re hs

/-- The analytically continued Dirichlet L-function supplied by mathlib. -/
noncomputable def dirichletLFunction {D : ℕ} (χ : RealPrimitiveCharacter D) (s : ℂ) : ℂ := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  exact χ.chi.LFunction s

/-- In the half-plane of absolute convergence, the analytic L-function agrees
with the naive L-series. -/
theorem dirichletLFunction_eq_series {D : ℕ} (χ : RealPrimitiveCharacter D)
    {s : ℂ} (hs : 1 < s.re) :
    dirichletLFunction χ s = dirichletLSeries χ s := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  simpa [dirichletLFunction, dirichletLSeries, dirichletCoeffs] using
    (χ.chi.LFunction_eq_LSeries hs)

/-- The genuine value `L(1,χ)`, obtained from analytic continuation. -/
noncomputable def LAtOne {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  dirichletLFunction χ 1

/-- The genuine complex derivative `L'(1,χ)`.  No arithmetic lower bound is
encoded in this definition. -/
noncomputable def LDerivAtOne {D : ℕ} (χ : RealPrimitiveCharacter D) : ℂ :=
  deriv (dirichletLFunction χ) 1

/-- For modulus greater than one the analytic L-function is differentiable
at every point, hence in particular at `1`. -/
theorem differentiable_dirichletLFunction_of_one_lt_modulus {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    Differentiable ℂ (dirichletLFunction χ) := by
  letI : NeZero D := ⟨χ.modulus_ne_zero⟩
  have hχ : χ.chi ≠ 1 := χ.nontrivial_of_one_lt_modulus hD
  simpa [dirichletLFunction] using
    (DirichletCharacter.differentiable_LFunction hχ)

/- Zhang's small-value contradiction hypothesis, now stated using the
analytically continued value at `s = 1` rather than the divergent naive series.

The real part is used because the target theorem concerns a real character.
A later lemma must prove that `LAtOne χ` is real (equivalently, has zero
imaginary part) from `χ.quadratic`; we do not silently assume this here.
-/

end ZhangLS.Spec
