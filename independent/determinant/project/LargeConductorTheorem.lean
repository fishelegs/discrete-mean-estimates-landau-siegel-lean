import RawWitnessAdapter
import Splice.ElementaryPrimeMass

/-!
# Large-conductor lower bounds for the actual Dirichlet L-value

This file composes the elementary prime-mass theorem with the finite
same-determinant construction. All remaining hypotheses concern the actual
character and its conductor: reality, primitivity, nonprincipality, and
D >= 2^24. In particular, no prime-mass inequality, determinant witness,
small-L assumption, or real-zero hypothesis is an input.

`Splice.LOne` is the real part of Mathlib's analytic continuation
`χ.LFunction 1`. The complex-norm conclusions follow from the real-part
conclusions by `Complex.re_le_norm`.

The `NeZero D` instance is required by the analytic L-function API and is
consistent with, and implied by, the displayed positive conductor cutoff.
This is only the large-conductor branch; no finite-conductor or global
closure is claimed here. Compilation and transitive axiom checks are a
separate validation step.
-/

namespace LargeConductorTheorem

/-- Both interfaces use the identical good-prime sum, including its floor and
all three filter conditions. -/
theorem goodPrimeMass_eq (D : ℕ) (χ : DirichletCharacter ℂ D) :
    RawWitnessAdapter.goodPrimeMass D χ = Splice.goodPrimeMass D χ := by
  rfl

/-- Explicit strong and weak bounds for the real part of the actual analytic
L-value, with neither analytic nor determinant comparison premises. -/
theorem real_part_lower_bounds
    (D : ℕ) [NeZero D] (hD : 2 ^ 24 ≤ D) (χ : DirichletCharacter ℂ D)
    (hreal : ∀ x : ZMod D, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    1 / (1536 * Real.log (D : ℝ)) < (χ.LFunction 1).re ∧
      1 / (4096 * Real.log (D : ℝ)) < (χ.LFunction 1).re := by
  have h97 : 97 ≤ D := le_trans (by norm_num) hD
  apply RawWitnessAdapter.lower_bound_of_prime_mass D hD χ hreal hprim hne
  simpa only [Splice.LOne, goodPrimeMass_eq] using
    Splice.elementary_prime_mass h97 χ hne hreal

/-- The real-part lower bounds also bound the complex norm from below. -/
theorem norm_lower_bounds
    (D : ℕ) [NeZero D] (hD : 2 ^ 24 ≤ D) (χ : DirichletCharacter ℂ D)
    (hreal : ∀ x : ZMod D, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    1 / (1536 * Real.log (D : ℝ)) < ‖χ.LFunction 1‖ ∧
      1 / (4096 * Real.log (D : ℝ)) < ‖χ.LFunction 1‖ := by
  have h := real_part_lower_bounds D hD χ hreal hprim hne
  exact ⟨lt_of_lt_of_le h.1 (Complex.re_le_norm _),
    lt_of_lt_of_le h.2 (Complex.re_le_norm _)⟩

/-- The requested weaker norm constant, isolated as a single conclusion. -/
theorem norm_lower_bound
    (D : ℕ) [NeZero D] (hD : 2 ^ 24 ≤ D) (χ : DirichletCharacter ℂ D)
    (hreal : ∀ x : ZMod D, (χ x).im = 0)
    (hprim : χ.IsPrimitive) (hne : χ ≠ 1) :
    1 / (4096 * Real.log (D : ℝ)) < ‖χ.LFunction 1‖ := by
  exact (norm_lower_bounds D hD χ hreal hprim hne).2

#check goodPrimeMass_eq
#check real_part_lower_bounds
#check norm_lower_bounds
#check norm_lower_bound

#print axioms goodPrimeMass_eq
#print axioms real_part_lower_bounds
#print axioms norm_lower_bounds
#print axioms norm_lower_bound

end LargeConductorTheorem
