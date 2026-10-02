import ZhangLS.Spec.RealAxisAtOne
import Mathlib.Analysis.Complex.RealDeriv

/-!
# Derivative compatibility at `s = 1`

For a real primitive Dirichlet character of modulus `D > 1`, Step 05 proves that
`Im L(x, χ) = 0` for real `x > 1`, and Step 06 closes this at `x = 1`.
This file uses one-sided derivative uniqueness on `Set.Ici 1` to show that the
complex derivative at `1` is itself real.  It also identifies the derivative of
the real-axis real part with the real part of the complex derivative.
-/

namespace ZhangLS.Spec

open Set Complex

/-- Imaginary-part analogue of `HasDerivAt.real_of_complex`.  We keep this
local to the project until/unless mathlib exposes the corresponding helper. -/
private theorem HasDerivAt.im_of_complex
    {e : ℂ → ℂ} {e' : ℂ} {z : ℝ} (h : HasDerivAt e e' z) :
    HasDerivAt (fun x : ℝ => (e x).im) e'.im z := by
  have A : HasFDerivAt ((↑) : ℝ → ℂ) ofRealCLM z := ofRealCLM.hasFDerivAt
  have B :
      HasFDerivAt e
        ((ContinuousLinearMap.smulRight 1 e' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
        (ofRealCLM z) :=
    h.hasFDerivAt.restrictScalars ℝ
  have C : HasFDerivAt im imCLM (e (ofRealCLM z)) := imCLM.hasFDerivAt
  simpa using (C.comp z (B.comp z A)).hasDerivAt

/-- The complex derivative `L'(1, χ)` is real.  The proof only needs the
right-hand real axis, where the Dirichlet series has already shown the
imaginary part to vanish. -/
theorem LDerivAtOne_im_eq_zero {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (LDerivAtOne χ).im = 0 := by
  let f : ℂ → ℂ := dirichletLFunction χ
  let g : ℝ → ℝ := fun x => (f (x : ℂ)).im

  have hdiff : Differentiable ℂ f := by
    simpa [f] using differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hcomplex : HasDerivAt f (LDerivAtOne χ) (1 : ℂ) := by
    simpa [f, LDerivAtOne] using (hdiff.differentiableAt.hasDerivAt :
      HasDerivAt f (deriv f (1 : ℂ)) (1 : ℂ))
  have him : HasDerivAt g (LDerivAtOne χ).im (1 : ℝ) := by
    simpa [g, f] using HasDerivAt.im_of_complex hcomplex

  have hzero : ∀ x ∈ Set.Ici (1 : ℝ), g x = 0 := by
    intro x hx
    rcases eq_or_lt_of_le (show (1 : ℝ) ≤ x from hx) with hxeq | hxgt
    · subst x
      simpa [g, f] using LAtOne_im_eq_zero χ hD
    · simpa [g, f] using dirichletLFunction_im_eq_zero_of_one_lt χ hxgt

  have hzeroWithin : HasDerivWithinAt g 0 (Set.Ici (1 : ℝ)) 1 := by
    refine (hasDerivWithinAt_const (1 : ℝ) (Set.Ici (1 : ℝ)) (0 : ℝ)).congr_of_mem ?_ Set.self_mem_Ici
    intro x hx
    exact hzero x hx

  exact (uniqueDiffOn_Ici (1 : ℝ) (1 : ℝ) Set.self_mem_Ici).eq_deriv _
    him.hasDerivWithinAt hzeroWithin

/-- The derivative of the real-axis function used in the paper is exactly the
real part of the complex analytic derivative. -/
theorem realLDerivAtOne_eq_re {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    realLDerivAtOne χ = (LDerivAtOne χ).re := by
  have hdiff := differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hcomplex :
      HasDerivAt (dirichletLFunction χ) (LDerivAtOne χ) (1 : ℂ) := by
    simpa [LDerivAtOne] using
      (hdiff.differentiableAt.hasDerivAt :
        HasDerivAt (dirichletLFunction χ)
          (deriv (dirichletLFunction χ) (1 : ℂ)) (1 : ℂ))
  have hreal := hcomplex.real_of_complex
  simpa [realLDerivAtOne, realLValue] using hreal.deriv

/-- Step 07 discharges the derivative-compatibility target from Step 04. -/
theorem real_axis_derivative_theorem : RealAxisDerivativeTheoremTarget := by
  intro D χ hD
  exact ⟨LDerivAtOne_im_eq_zero χ hD, realLDerivAtOne_eq_re χ hD⟩

/-- Convenient complex-valued form: the analytic derivative is the coercion of
the paper's real derivative. -/
theorem LDerivAtOne_eq_realLDerivAtOne {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    LDerivAtOne χ = (realLDerivAtOne χ : ℂ) := by
  apply Complex.ext
  · simpa using (realLDerivAtOne_eq_re χ hD).symm
  · simpa using LDerivAtOne_im_eq_zero χ hD

end ZhangLS.Spec
