import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

open scoped BigOperators
namespace FixedQuadratic

variable {ι σ R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

/-- A nonzero minor has a genuinely nonzero permutation product. -/
theorem exists_matching_of_det_ne_zero (A : Matrix ι ι R) (hA : A.det ≠ 0) :
    ∃ p : Equiv.Perm ι, ∀ j, A (p j) j ≠ 0 := by
  classical
  by_contra! h
  apply hA
  rw [Matrix.det_apply]
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨j, hj⟩ := h p
  have hz : (∏ i, A (p i) i) = 0 := Finset.prod_eq_zero (Finset.mem_univ j) hj
  rw [hz, smul_zero]

omit [DecidableEq ι] in
/-- Each surviving permutation has the same difference of total column and
row exponents. Incompatible products must be discarded before subtraction. -/
theorem matched_sum_sub (α b : ι → ℕ) (p : Equiv.Perm ι)
    (h : ∀ j, b (p j) ≤ α j) :
    ∑ j, (α j - b (p j)) = (∑ j, α j) - ∑ j, b j := by
  rw [Finset.sum_tsub_distrib Finset.univ (fun j _ => h j), Equiv.sum_comp p]

/-- Coordinate degree bound with the row rebate, allowing cancellation to
lower the actual degree. This is a statement about a determinant polynomial. -/
theorem det_degreeOf_le (A : Matrix ι ι (MvPolynomial σ R))
    (α b : ι → σ → ℕ)
    (hzero : ∀ r c, ¬ (∀ i, b r i ≤ α c i) → A r c = 0)
    (hdegree : ∀ r c i, (A r c).degreeOf i ≤ α c i - b r i) (i : σ) :
    A.det.degreeOf i ≤ (∑ c, α c i) - ∑ r, b r i := by
  classical
  rw [Matrix.det_apply']
  apply (MvPolynomial.degreeOf_sum_le i Finset.univ _).trans
  apply Finset.sup_le
  intro p hp
  by_cases h : ∀ c, ∀ k, b (p c) k ≤ α c k
  · change MvPolynomial.degreeOf i (MvPolynomial.C (↑↑(Equiv.Perm.sign p) : R) * _) ≤ _
    apply (MvPolynomial.degreeOf_mul_le i _ _).trans
    simp only [MvPolynomial.degreeOf_C, zero_add]
    apply (MvPolynomial.degreeOf_prod_le i Finset.univ _).trans
    calc
      _ ≤ ∑ c, (α c i - b (p c) i) := Finset.sum_le_sum (fun c _ => hdegree _ _ _)
      _ = _ := matched_sum_sub (fun c => α c i) (fun r => b r i) p (fun c => h c i)
  · push Not at h
    obtain ⟨c, k, hk⟩ := h
    have hz : A (p c) c = 0 := hzero _ _ (by intro hh; exact (not_le_of_gt hk) (hh k))
    have hpz : (∏ j, A (p j) j) = 0 := Finset.prod_eq_zero (Finset.mem_univ c) hz
    rw [hpz, mul_zero]
    simp

/-- Nonzero minors have nonnegative (integer) coordinate rebates. -/
theorem row_total_le_column_total (A : Matrix ι ι R)
    (α b : ι → σ → ℕ) (hA : A.det ≠ 0)
    (hzero : ∀ r c, ¬ (∀ i, b r i ≤ α c i) → A r c = 0) (i : σ) :
    (∑ r, b r i) ≤ ∑ c, α c i := by
  obtain ⟨p, hp⟩ := exists_matching_of_det_ne_zero A hA
  have h : ∀ c, b (p c) i ≤ α c i := by
    intro c
    by_contra hc
    exact hp c (hzero _ _ (by intro hh; exact hc (hh i)))
  calc
    _ = ∑ c, b (p c) i := (Equiv.sum_comp p _).symm
    _ ≤ _ := Finset.sum_le_sum (fun c _ => h c)

omit [DecidableEq ι] in
/-- The weighted total retains one row rebate rather than m separate budgets. -/
theorem weighted_rebate {m : ℕ} (α b : ι → Fin m → ℕ) (w : Fin m → ℝ)
    (h : ∀ i, (∑ r, b r i) ≤ ∑ c, α c i) :
    ∑ i, w i * (((∑ c, α c i) - ∑ r, b r i : ℕ) : ℝ) =
      (∑ c, ∑ i, w i * (α c i : ℝ)) - ∑ r, ∑ i, w i * (b r i : ℝ) := by
  simp_rw [Nat.cast_sub (h _), Nat.cast_sum, mul_sub, Finset.mul_sum]
  rw [Finset.sum_sub_distrib, Finset.sum_comm, Finset.sum_comm (f := fun i r => w i * (b r i : ℝ))]

end FixedQuadratic
