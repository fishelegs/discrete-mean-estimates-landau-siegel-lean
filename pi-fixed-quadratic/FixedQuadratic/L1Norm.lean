import FixedQuadratic.MultiEnvelope
import Mathlib.Data.Fintype.Perm
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

open scoped BigOperators
namespace FixedQuadratic

theorem multiCoefficientL1_nonneg {m : ℕ} (P : MvPolynomial (Fin m) ℂ) :
    0 ≤ multiCoefficientL1 P := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem multiCoefficientL1_on_superset {m : ℕ} (P : MvPolynomial (Fin m) ℂ)
    (s : Finset (Fin m →₀ ℕ)) (hs : P.support ⊆ s) :
    multiCoefficientL1 P = ∑ a ∈ s, ‖P.coeff a‖ := by
  classical
  apply Finset.sum_subset hs
  intro a _ ha
  rw [MvPolynomial.notMem_support_iff.mp ha, norm_zero]

theorem multiCoefficientL1_add_le {m : ℕ} (P Q : MvPolynomial (Fin m) ℂ) :
    multiCoefficientL1 (P+Q) ≤ multiCoefficientL1 P + multiCoefficientL1 Q := by
  classical
  rw [multiCoefficientL1_on_superset (P+Q) (P.support ∪ Q.support)
    MvPolynomial.support_add,
    multiCoefficientL1_on_superset P _ Finset.subset_union_left,
    multiCoefficientL1_on_superset Q _ Finset.subset_union_right, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum (fun a _ => by simpa using norm_add_le (P.coeff a) (Q.coeff a))

theorem multiCoefficientL1_zero {m : ℕ} :
    multiCoefficientL1 (0 : MvPolynomial (Fin m) ℂ) = 0 := by
  simp [multiCoefficientL1]

theorem multiCoefficientL1_monomial {m : ℕ} (a : Fin m →₀ ℕ) (z : ℂ) :
    multiCoefficientL1 (MvPolynomial.monomial a z) = ‖z‖ := by
  classical
  by_cases hz : z = 0
  · simp [hz, multiCoefficientL1]
  · simp [multiCoefficientL1, MvPolynomial.support_monomial, hz]

theorem multiCoefficientL1_sum_le {ι : Type*} {m : ℕ} (s : Finset ι)
    (P : ι → MvPolynomial (Fin m) ℂ) :
    multiCoefficientL1 (∑ i ∈ s, P i) ≤ ∑ i ∈ s, multiCoefficientL1 (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [multiCoefficientL1_zero]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (multiCoefficientL1_add_le _ _).trans (add_le_add (le_refl _) ih)

theorem multiCoefficientL1_mul_le {m : ℕ} (P Q : MvPolynomial (Fin m) ℂ) :
    multiCoefficientL1 (P*Q) ≤ multiCoefficientL1 P * multiCoefficientL1 Q := by
  classical
  rw [MvPolynomial.mul_def, MvPolynomial.sum_def]
  apply (multiCoefficientL1_sum_le _ _).trans
  calc
    _ ≤ ∑ a ∈ P.support, ∑ b ∈ Q.support, ‖P.coeff a * Q.coeff b‖ := by
      apply Finset.sum_le_sum
      intro a ha
      rw [MvPolynomial.sum_def]
      exact (multiCoefficientL1_sum_le _ _).trans_eq (by simp [multiCoefficientL1_monomial])
    _ = multiCoefficientL1 P * multiCoefficientL1 Q := by
      simp only [norm_mul, multiCoefficientL1, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm

theorem multiCoefficientL1_C {m : ℕ} (z : ℂ) :
    multiCoefficientL1 (MvPolynomial.C z : MvPolynomial (Fin m) ℂ) = ‖z‖ :=
  multiCoefficientL1_monomial 0 z

theorem multiCoefficientL1_one {m : ℕ} :
    multiCoefficientL1 (1 : MvPolynomial (Fin m) ℂ) = 1 := by
  simpa using (multiCoefficientL1_C (m := m) 1)

theorem multiCoefficientL1_prod_le {ι : Type*} {m : ℕ} (s : Finset ι)
    (P : ι → MvPolynomial (Fin m) ℂ) :
    multiCoefficientL1 (∏ i ∈ s, P i) ≤ ∏ i ∈ s, multiCoefficientL1 (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [multiCoefficientL1_one]
  | @insert i s hi ih =>
    simp only [Finset.prod_insert hi]
    exact (multiCoefficientL1_mul_le _ _).trans
      (mul_le_mul_of_nonneg_left ih (multiCoefficientL1_nonneg _))

theorem multiCoefficientL1_pow_le {m : ℕ} (P : MvPolynomial (Fin m) ℂ) (n : ℕ) :
    multiCoefficientL1 (P^n) ≤ (multiCoefficientL1 P)^n := by
  induction n with
  | zero => simp [multiCoefficientL1_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (multiCoefficientL1_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (multiCoefficientL1_nonneg _))

theorem multiCoefficientL1_neg {m : ℕ} (P : MvPolynomial (Fin m) ℂ) :
    multiCoefficientL1 (-P) = multiCoefficientL1 P := by
  simp [multiCoefficientL1]

/-- Full polynomial coefficient envelope, retaining each genuine determinant
permutation product. This is not an envelope only at the target tuple. -/
theorem determinant_l1_le {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix ι ι (MvPolynomial (Fin m) ℂ)) :
    multiCoefficientL1 (Matrix.det A) ≤
      ∑ σ : Equiv.Perm ι, ∏ i, multiCoefficientL1 (A (σ i) i) := by
  classical
  rw [Matrix.det_apply']
  apply (multiCoefficientL1_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro σ hσ
  have hsign : Equiv.Perm.sign σ = 1 ∨ Equiv.Perm.sign σ = -1 := Int.units_eq_one_or σ.sign
  rcases hsign with h | h
  · simpa [h] using multiCoefficientL1_prod_le Finset.univ (fun i => A (σ i) i)
  · simpa [h, multiCoefficientL1_neg] using multiCoefficientL1_prod_le Finset.univ (fun i => A (σ i) i)

theorem determinant_l1_factorial_le {ι : Type*} [Fintype ι] [DecidableEq ι] {m : ℕ}
    (A : Matrix ι ι (MvPolynomial (Fin m) ℂ)) (B : ℝ)
    (hB : ∀ σ : Equiv.Perm ι, (∏ i, multiCoefficientL1 (A (σ i) i)) ≤ B) :
    multiCoefficientL1 (Matrix.det A) ≤ (Fintype.card ι).factorial * B := by
  apply (determinant_l1_le A).trans
  calc
    _ ≤ ∑ _σ : Equiv.Perm ι, B := Finset.sum_le_sum (fun σ _ => hB σ)
    _ = _ := by simp [Fintype.card_perm]

end FixedQuadratic
