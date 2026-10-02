import ZhangLS.Spec.RealAxisSeries

/-!
# Reality of `L(1, χ)` for real primitive characters

Step 05 established that the analytically continued Dirichlet L-function is
real on the real half-line `x > 1`, by comparison with the absolutely
convergent Dirichlet series.  This file closes the endpoint `x = 1` for
nontrivial primitive characters.

The proof is deliberately topological rather than using a global reflection
principle: for `D > 1`, the primitive character is nontrivial, hence its
L-function is differentiable (therefore continuous) everywhere.  The zero set
of the imaginary part is closed and contains `Set.Ioi 1`; hence it contains the
closure of `Set.Ioi 1`, in particular the endpoint `1`.
-/

namespace ZhangLS.Spec

open Set

/-- For a real primitive character of modulus `D > 1`, the analytically
continued value at `s = 1` is real. -/
theorem dirichletLFunction_im_eq_zero_at_one {D : ℕ}
    (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (dirichletLFunction χ (1 : ℂ)).im = 0 := by
  have hdiff : Differentiable ℂ (dirichletLFunction χ) :=
    differentiable_dirichletLFunction_of_one_lt_modulus χ hD
  have hcontL : Continuous (fun x : ℝ => dirichletLFunction χ (x : ℂ)) :=
    hdiff.continuous.comp Complex.continuous_ofReal
  have hcontIm : Continuous (fun x : ℝ => (dirichletLFunction χ (x : ℂ)).im) :=
    Complex.continuous_im.comp hcontL
  let S : Set ℝ := {x | (dirichletLFunction χ (x : ℂ)).im = 0}
  have hSclosed : IsClosed S := by
    dsimp [S]
    exact isClosed_eq hcontIm continuous_const
  have hIoi : Set.Ioi (1 : ℝ) ⊆ S := by
    intro x hx
    exact dirichletLFunction_im_eq_zero_of_one_lt χ hx
  have hclosure : closure (Set.Ioi (1 : ℝ)) ⊆ S :=
    closure_minimal hIoi hSclosed
  have h1 : (1 : ℝ) ∈ closure (Set.Ioi (1 : ℝ)) := by
    simp
  exact hclosure h1

/-- The genuine analytic value `LAtOne χ` has zero imaginary part. -/
theorem LAtOne_im_eq_zero {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    (LAtOne χ).im = 0 := by
  simpa [LAtOne] using dirichletLFunction_im_eq_zero_at_one χ hD

/-- The complex analytic value at one is exactly the coercion of the real-axis
value used by the paper-level inequalities. -/
theorem LAtOne_eq_realLAtOne {D : ℕ} (χ : RealPrimitiveCharacter D) (hD : 1 < D) :
    LAtOne χ = (realLAtOne χ : ℂ) := by
  apply Complex.ext
  · simpa using (realLAtOne_eq_re χ).symm
  · simpa using LAtOne_im_eq_zero χ hD

/-- Step 06 discharges the endpoint needed by Theorem 1 without yet proving a
global conjugation/reflection theorem for all real arguments. -/
theorem real_value_at_one_milestone :
    ∀ {D : ℕ} (χ : RealPrimitiveCharacter D), 1 < D → (LAtOne χ).im = 0 := by
  intro D χ hD
  exact LAtOne_im_eq_zero χ hD

end ZhangLS.Spec
