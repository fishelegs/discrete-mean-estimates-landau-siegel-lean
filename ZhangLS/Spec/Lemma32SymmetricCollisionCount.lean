import ZhangLS.Spec.Lemma32BurgessCongruenceCount
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma32_burgess_determinant_swap (M : ℤ) (a b : ℕ) {N : ℕ} (n m : Fin N) :
    lemma32BurgessDeterminant M b a m n = -lemma32BurgessDeterminant M a b n m := by
  unfold lemma32BurgessDeterminant
  ring

lemma lemma32_burgess_collision_card_symmetric (D : ℕ) (M : ℤ) (a b N : ℕ) :
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => (D : ℤ) ∣ lemma32BurgessDeterminant M a b p.1 p.2)).card =
    ((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => (D : ℤ) ∣ lemma32BurgessDeterminant M b a p.1 p.2)).card := by
  apply Finset.card_bij (fun p hp => (p.2,p.1))
  · intro p hp
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [lemma32_burgess_determinant_swap]
    exact dvd_neg.mpr (Finset.mem_filter.mp hp).2
  · intro p hp q hq he
    exact Prod.ext (congrArg Prod.snd he) (congrArg Prod.fst he)
  · intro q hq
    refine ⟨(q.2,q.1), ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [lemma32_burgess_determinant_swap]
      exact dvd_neg.mpr (Finset.mem_filter.mp hq).2
    · exact Prod.ext rfl rfl

lemma lemma32_burgess_fixed_multiplier_max_count {D A N a b : ℕ}
    (hsize : 2*A*N < D) (haA : a ≤ A) (hbA : b ≤ A)
    (ha : 0 < a) (hb : 0 < b) (M : ℤ) :
    (((Finset.univ : Finset (Fin N × Fin N)).filter
      (fun p => (D : ℤ) ∣ lemma32BurgessDeterminant M a b p.1 p.2)).card : ℝ) ≤
      (N : ℝ)*(a.gcd b : ℝ)/((max a b : ℕ) : ℝ)+1 := by
  by_cases hab : a ≤ b
  · rw [max_eq_right hab]
    exact lemma32_burgess_fixed_multiplier_real_count hsize haA hbA hb M
  · rw [max_eq_left (Nat.le_of_lt (Nat.lt_of_not_ge hab)),
      lemma32_burgess_collision_card_symmetric D M a b N, Nat.gcd_comm]
    exact lemma32_burgess_fixed_multiplier_real_count hsize hbA haA ha M

end ZhangLS.Spec
