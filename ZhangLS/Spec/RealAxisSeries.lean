import ZhangLS.Spec.RealAxisLFunction

/-!
# Reality of the Dirichlet L-series on the real axis

This is the first genuinely analytic bridge in the repaired specification.
For a real-valued Dirichlet character, every term of its Dirichlet series is
real when the complex parameter is a real number.  Absolute convergence for
`x > 1` then implies that the entire L-series is real, and the mathlib
continuation agrees with that series in this half-plane.

No statement below uses the value at `s = 1`; crossing that boundary is a
separate analytic-continuation step.
-/

namespace ZhangLS.Spec

open RealPrimitiveCharacter
open ComplexConjugate

/-- Every individual Dirichlet-series term is real at a real parameter. -/
theorem dirichletTerm_im_eq_zero {D : ℕ} (χ : RealPrimitiveCharacter D)
    (x : ℝ) (n : ℕ) :
    (LSeries.term (dirichletCoeffs χ) (x : ℂ) n).im = 0 := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  · rw [LSeries.term_of_ne_zero hn]
    have hcoeff :
        dirichletCoeffs χ n = ((dirichletCoeffs χ n).re : ℂ) := by
      apply Complex.ext
      · simp
      · simp [dirichletCoeffs, χ.real_valued]
    have hpow :
        (n : ℂ) ^ (x : ℂ) = (((n : ℝ) ^ x : ℝ) : ℂ) := by
      simpa only [Complex.ofReal_natCast] using
        (Complex.ofReal_cpow (Nat.cast_nonneg n) x).symm
    rw [hcoeff, hpow]
    simp

/-- The absolutely convergent Dirichlet series is real for real `x > 1`. -/
theorem dirichletLSeries_im_eq_zero_of_one_lt {D : ℕ}
    (χ : RealPrimitiveCharacter D) {x : ℝ} (hx : 1 < x) :
    (dirichletLSeries χ (x : ℂ)).im = 0 := by
  have hsum : Summable (LSeries.term (dirichletCoeffs χ) (x : ℂ)) := by
    exact dirichletLSeries_summable_of_one_lt_re χ (by simpa using hx)
  rw [dirichletLSeries, LSeries, Complex.im_tsum hsum]
  simp only [dirichletTerm_im_eq_zero, tsum_zero]

/-- In the half-plane where the analytic continuation is represented by the
Dirichlet series, the L-function is real on the real axis. -/
theorem dirichletLFunction_im_eq_zero_of_one_lt {D : ℕ}
    (χ : RealPrimitiveCharacter D) {x : ℝ} (hx : 1 < x) :
    (dirichletLFunction χ (x : ℂ)).im = 0 := by
  rw [dirichletLFunction_eq_series χ (by simpa using hx)]
  exact dirichletLSeries_im_eq_zero_of_one_lt χ hx

/-- Conjugation fixes the L-function on the real half-line `x > 1`. -/
theorem conj_dirichletLFunction_of_one_lt {D : ℕ}
    (χ : RealPrimitiveCharacter D) {x : ℝ} (hx : 1 < x) :
    conj (dirichletLFunction χ (x : ℂ)) = dirichletLFunction χ (x : ℂ) := by
  apply Complex.ext
  · simp
  · simp [dirichletLFunction_im_eq_zero_of_one_lt χ hx]

end ZhangLS.Spec
