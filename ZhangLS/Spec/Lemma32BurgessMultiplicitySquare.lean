import ZhangLS.Spec.Lemma32BurgessResidueCollision
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma lemma32_actual_burgess_multiplicity_square_collision {D : ℕ} [NeZero D]
    (M : ℤ) (A N : ℕ) :
    (∑ x : ZMod D, (lemma32BurgessMultiplicity D M A N x : ℝ)^2) =
      ∑ p ∈ lemma32BurgessMultiplierPairs D A N,
        ∑ q ∈ lemma32BurgessMultiplierPairs D A N,
          if lemma32BurgessNormalizedResidue D M p=lemma32BurgessNormalizedResidue D M q
          then (1 : ℝ) else 0 := by
  rw [show (∑ x : ZMod D, (lemma32BurgessMultiplicity D M A N x : ℝ)^2) =
      ∑ x : ZMod D, (lemma32BurgessMultiplicity D M A N x : ℝ)*
        (lemma32BurgessMultiplicity D M A N x : ℝ) by simp only [pow_two]]
  rw [lemma32_actual_burgess_multiplicity_weighted_sum]
  apply Finset.sum_congr rfl
  intro p hp
  unfold lemma32BurgessMultiplicity
  calc
    _ = ∑ _q ∈ (lemma32BurgessMultiplierPairs D A N).filter
        (fun q => lemma32BurgessNormalizedResidue D M q=lemma32BurgessNormalizedResidue D M p),
        (1 : ℝ) := by simp
    _ = _ := by rw [Finset.sum_filter];simp only [eq_comm]

lemma lemma32_actual_burgess_multiplicity_square_determinant {D : ℕ} [NeZero D]
    (M : ℤ) (A N : ℕ) :
    (∑ x : ZMod D, (lemma32BurgessMultiplicity D M A N x : ℝ)^2) =
      ∑ p ∈ lemma32BurgessMultiplierPairs D A N,
        ∑ q ∈ lemma32BurgessMultiplierPairs D A N,
          if (D : ℤ) ∣ (((p.1.val+1 : ℕ) : ℤ)*(M+(q.2.val : ℤ))-
            ((q.1.val+1 : ℕ) : ℤ)*(M+(p.2.val : ℤ))) then (1 : ℝ) else 0 := by
  rw [lemma32_actual_burgess_multiplicity_square_collision]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  simp only [lemma32_actual_burgess_residue_collision M p q hp hq]

end ZhangLS.Spec
