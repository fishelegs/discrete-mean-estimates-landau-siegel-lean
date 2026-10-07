import Mathlib.Tactic.NormDet
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# An explicitly displayed 8 by 8 matrix

The matrix entries below are the finite quality-free diagnostic, in row order
(j,s,beta) with j=0,1 and (s,beta)=(0,0),(1,0),(2,0),(0,1), and column order
(h,alpha)=(0,0),(1,0),(0,1),(1,1),(0,2),(1,2),(0,3),(1,3).

This checkpoint proves the determinant of the displayed matrix and its nonzero
value at the actual complex number 2*pi*i. It does NOT formalize the identification
of the entries with the paper's Taylor coefficients or translated test functions.
The finite parameters are not certified to satisfy asymptotic separation thresholds.
-/

set_option autoImplicit false

namespace PiRowRank

/-- Explicit finite matrix from the eight-row diagnostic. -/
noncomputable def qualityFreeMatrix (x : ℂ) : Matrix (Fin 8) (Fin 8) ℂ :=
  !![1, 1, 0, 0, 0, 0, 0, 0;
     0, 1, 1, 1, 0, 0, 0, 0;
     0, 0, -1/2, 1/2, 1, 1, 0, 0;
     0, 0, 1, 1, 0, 0, 0, 0;
     1, 1, x, x, x^2, x^2, x^3, x^3;
     0, 1, 1, x+1, 2*x, x^2+2*x, 3*x^2, x^3+3*x^2;
     0, 0, -1/2, 1/2, 1-x, x+1, -3*x^2/2+3*x, 3*x^2/2+3*x;
     0, 0, 1, 1, 2*x, 2*x, 3*x^2, 3*x^2]

/-- Kernel-checked symbolic determinant identity, valid at every complex x. -/
theorem qualityFreeMatrix_det (x : ℂ) : (qualityFreeMatrix x).det = x^8 := by
  unfold qualityFreeMatrix
  eval_det
  ring

/-- Nonzero centers give nonzero determinant in this displayed example. -/
theorem qualityFreeMatrix_det_ne_zero (x : ℂ) (hx : x ≠ 0) :
    (qualityFreeMatrix x).det ≠ 0 := by
  rw [qualityFreeMatrix_det]
  exact pow_ne_zero 8 hx

/-- The actual complex period, rather than a rational surrogate. -/
noncomputable def period : ℂ := 2 * (Real.pi : ℂ) * Complex.I

theorem period_ne_zero : period ≠ 0 := by
  unfold period
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
    Complex.I_ne_zero

/-- The explicit finite diagnostic is nonzero at the actual period. This
particular monomial determinant needs only pi != 0, not transcendence of pi. -/
theorem qualityFreeMatrix_period_det_ne_zero : (qualityFreeMatrix period).det ≠ 0 := by
  rw [qualityFreeMatrix_det]
  exact pow_ne_zero 8 period_ne_zero

end PiRowRank
