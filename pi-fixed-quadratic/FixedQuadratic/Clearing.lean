import FixedQuadratic.MinorBudget

open scoped BigOperators
namespace FixedQuadratic

/-- Exact determinant clearing with permutation-independent degree differences.
The subring can be Gaussian-coefficient multivariate polynomials, so this clears
the entire polynomial, not only its value at a target tuple. -/
theorem determinant_clearing {ι σ R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype σ] [CommRing R] (S : Subring R) (A : Matrix ι ι R)
    (L : σ → R) (α b : ι → σ → ℕ)
    (hzero : ∀ r c, ¬ (∀ i, b r i ≤ α c i) → A r c = 0)
    (hclear : ∀ r c, (∏ i, L i^(α c i-b r i)) * A r c ∈ S) :
    (∏ i, L i^((∑ c, α c i)-(∑ r, b r i))) * A.det ∈ S := by
  classical
  rw [Matrix.det_apply', Finset.mul_sum]
  apply S.sum_mem
  intro p hp
  by_cases h : ∀ c i, b (p c) i ≤ α c i
  · have he : (∏ i, L i^((∑ c, α c i)-(∑ r, b r i))) =
        ∏ c, ∏ i, L i^(α c i-b (p c) i) := by
      rw [Finset.prod_comm]
      apply Finset.prod_congr rfl
      intro i hi
      rw [Finset.prod_pow_eq_pow_sum,
        matched_sum_sub (fun c => α c i) (fun r => b r i) p (fun c => h c i)]
    rw [he]
    have hh : (∏ c, (∏ i, L i^(α c i-b (p c) i))*A (p c) c) ∈ S :=
      S.prod_mem (fun c _ => hclear (p c) c)
    have ht := S.mul_mem (intCast_mem S (↑(Equiv.Perm.sign p))) hh
    simpa only [Finset.prod_mul_distrib, mul_left_comm, mul_assoc] using ht
  · push Not at h
    obtain ⟨c, i, hi⟩ := h
    have hz : A (p c) c = 0 := hzero _ _ (by intro hh; exact (not_le_of_gt hi) (hh i))
    have hpz : (∏ j, A (p j) j) = 0 := Finset.prod_eq_zero (Finset.mem_univ c) hz
    simp [hpz]

end FixedQuadratic
