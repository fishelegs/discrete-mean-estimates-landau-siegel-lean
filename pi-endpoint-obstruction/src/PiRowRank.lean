import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# A finite weighted-row checkpoint

A self-map of a finite row packet that strictly lowers weight whenever it moves
an index cannot be injective unless it is the identity. Consequently a moved
row assignment has a collision, and the associated (even separately weighted)
row-reindexed determinant vanishes.

The hypotheses explicitly require a self-map of the COMPLETE finite packet and
strict decrease at every changed index. This file does not derive those
hypotheses from logarithmic Taylor coefficients or from the paper's row formula.
It does not formalize the all-m source attachment, a transcendence argument,
interpolation thresholds, or bad approximability of pi.
-/

set_option autoImplicit false

namespace PiRowRank

/-- Finite injectivity and strict weight decrease on every moved index force
pointwise identity. No injectivity of the weight function itself is assumed. -/
theorem finite_injective_downward_eq_self {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (f : ι → ι)
    (hdown : ∀ i, f i ≠ i → weight (f i) < weight i)
    (hinj : Function.Injective f) : ∀ i, f i = i := by
  classical
  have hweak : ∀ i, weight (f i) ≤ weight i := by
    intro i
    by_cases hfix : f i = i
    · rw [hfix]
    · exact (hdown i hfix).le
  have hsum : (∑ i, weight (f i)) = ∑ i, weight i :=
    Fintype.sum_bijective f ⟨hinj, Finite.surjective_of_injective hinj⟩
      (fun i => weight (f i)) weight (fun _ => rfl)
  intro i
  by_contra hmove
  have hlt : (∑ j, weight (f j)) < ∑ j, weight j :=
    Finset.sum_lt_sum (fun j _ => hweak j) ⟨i, Finset.mem_univ i, hdown i hmove⟩
  exact (ne_of_lt hlt) hsum

/-- A nonidentity downward self-map has two distinct source indices with the
same target. Closure in the finite packet is encoded in the type of `f`. -/
theorem downward_nonidentity_has_collision {ι : Type*} [Fintype ι]
    (weight : ι → ℝ) (f : ι → ι)
    (hdown : ∀ i, f i ≠ i → weight (f i) < weight i)
    (hmove : ∃ i, f i ≠ i) : ∃ i j, i ≠ j ∧ f i = f j := by
  classical
  by_contra h
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    exact h ⟨i, j, hne, hij⟩
  obtain ⟨i, hi⟩ := hmove
  exact hi (finite_injective_downward_eq_self weight f hdown hinj i)

/-- A changed, strictly weight-lowering assignment of rows has determinant zero. -/
theorem det_reindexed_eq_zero_of_downward_nonidentity
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (weight : ι → ℝ) (f : ι → ι) (A : Matrix ι ι R)
    (hdown : ∀ i, f i ≠ i → weight (f i) < weight i)
    (hmove : ∃ i, f i ≠ i) :
    Matrix.det (fun i j => A (f i) j) = 0 := by
  obtain ⟨i, j, hne, heq⟩ := downward_nonidentity_has_collision weight f hdown hmove
  exact Matrix.det_zero_of_row_eq hne (congrArg A heq)

/-- Independent scalar factors on the reindexed rows do not remove vanishing. -/
theorem det_weighted_reindexed_eq_zero_of_downward_nonidentity
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]
    (weight : ι → ℝ) (f : ι → ι) (A : Matrix ι ι R) (c : ι → R)
    (hdown : ∀ i, f i ≠ i → weight (f i) < weight i)
    (hmove : ∃ i, f i ≠ i) :
    Matrix.det (fun i j => c i * A (f i) j) = 0 := by
  calc
    _ = (∏ i, c i) * Matrix.det (fun i j => A (f i) j) :=
      Matrix.det_mul_column c (fun i j => A (f i) j)
    _ = 0 := by
      rw [det_reindexed_eq_zero_of_downward_nonidentity weight f A hdown hmove, mul_zero]

end PiRowRank
