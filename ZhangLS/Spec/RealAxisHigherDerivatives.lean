import ZhangLS.Spec.RealAxisContinuation
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Reality of the actual higher Dirichlet L-function jets

The published real-axis continuation supplies the values of the actual analytic
L-function. Differentiating its imaginary part shows that every complex iterated
derivative remains real on the real axis. In particular, the quadratic Taylor
coefficient at one is exactly the coercion of half the second derivative's real
part; it is not a substitute scalar chosen to satisfy a residue identity.
-/

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex

private theorem hasDerivAt_im_of_complex_higher
    {f : ℂ → ℂ} {f' : ℂ} {x : ℝ} (h : HasDerivAt f f' (x : ℂ)) :
    HasDerivAt (fun y : ℝ => (f (y : ℂ)).im) f'.im x := by
  have A : HasFDerivAt ((↑) : ℝ → ℂ) ofRealCLM x := ofRealCLM.hasFDerivAt
  have B :
      HasFDerivAt f
        ((ContinuousLinearMap.smulRight 1 f' : ℂ →L[ℂ] ℂ).restrictScalars ℝ)
        (ofRealCLM x) := h.hasFDerivAt.restrictScalars ℝ
  have C : HasFDerivAt im imCLM (f (ofRealCLM x)) := imCLM.hasFDerivAt
  simpa using (C.comp x (B.comp x A)).hasDerivAt

/-- A complex function real on the real axis has a real totalized derivative
there. No differentiability assumption is needed: Lean's derivative is zero at
points where the function is not differentiable. -/
theorem deriv_im_eq_zero_of_real_axis (f : ℂ → ℂ)
    (hf : ∀ x : ℝ, (f (x : ℂ)).im = 0) (x : ℝ) :
    (deriv f (x : ℂ)).im = 0 := by
  by_cases hd : DifferentiableAt ℂ f (x : ℂ)
  · have him := hasDerivAt_im_of_complex_higher hd.hasDerivAt
    have hzero : (fun y : ℝ => (f (y : ℂ)).im) = fun _ => (0 : ℝ) := funext hf
    rw [hzero] at him
    exact him.unique (hasDerivAt_const x (0 : ℝ))
  · rw [deriv_zero_of_not_differentiableAt hd]
    rfl

/-- Reality is preserved by any number of complex derivatives. -/
theorem iteratedDeriv_im_eq_zero_of_real_axis (f : ℂ → ℂ)
    (hf : ∀ x : ℝ, (f (x : ℂ)).im = 0) (n : ℕ) (x : ℝ) :
    (iteratedDeriv n f (x : ℂ)).im = 0 := by
  induction n generalizing x with
  | zero => simpa only [iteratedDeriv_zero] using hf x
  | succ n ih =>
    rw [iteratedDeriv_succ]
    exact deriv_im_eq_zero_of_real_axis (iteratedDeriv n f) ih x

/-- Every actual Dirichlet L-function jet at a real point is real. -/
theorem dirichletLFunction_iteratedDeriv_im_eq_zero_real
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (n : ℕ) (x : ℝ) :
    (iteratedDeriv n (dirichletLFunction χ) (x : ℂ)).im = 0 :=
  iteratedDeriv_im_eq_zero_of_real_axis (dirichletLFunction χ)
    (dirichletLFunction_im_eq_zero_real χ hD) n x

/-- Complex-valued form of reality for every actual L-function jet. -/
theorem dirichletLFunction_iteratedDeriv_eq_ofReal_re
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) (n : ℕ) (x : ℝ) :
    iteratedDeriv n (dirichletLFunction χ) (x : ℂ) =
      ((iteratedDeriv n (dirichletLFunction χ) (x : ℂ)).re : ℂ) := by
  apply Complex.ext
  · rfl
  · simpa using dirichletLFunction_iteratedDeriv_im_eq_zero_real χ hD n x

/-- The actual second derivative at one has zero imaginary part. -/
theorem dirichletLFunction_second_deriv_at_one_im_eq_zero
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (iteratedDeriv 2 (dirichletLFunction χ) 1).im = 0 := by
  simpa using dirichletLFunction_iteratedDeriv_im_eq_zero_real χ hD 2 1

/-- The real scalar used for the quadratic Taylor jet is the actual complex
coefficient `L''(1, χ) / 2`. -/
theorem dirichletLFunction_second_jet_at_one_eq_ofReal
    {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    iteratedDeriv 2 (dirichletLFunction χ) 1 / 2 =
      (((iteratedDeriv 2 (dirichletLFunction χ) 1).re / 2 : ℝ) : ℂ) := by
  rw [Complex.ofReal_div, Complex.ofReal_ofNat]
  congr 1
  simpa using dirichletLFunction_iteratedDeriv_eq_ofReal_re χ hD 2 1

end ZhangLS.Spec
