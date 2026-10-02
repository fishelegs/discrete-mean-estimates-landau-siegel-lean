import ZhangLS.Spec.Lemma32BurgessShiftCharacter
import Mathlib.Data.Fintype.BigOperators
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

noncomputable def lemma32BurgessUnitMultipliers (D A : ℕ) : Finset (Fin A) :=
  Finset.univ.filter (fun a => (a.val+1).Coprime D)

noncomputable def lemma32BurgessMultiplierPairs (D A N : ℕ) : Finset (Fin A × Fin N) :=
  (lemma32BurgessUnitMultipliers D A).product Finset.univ

def lemma32BurgessNormalizedResidue (D : ℕ) (M : ℤ) {A N : ℕ}
    (p : Fin A × Fin N) : ZMod D :=
  ((p.1.val+1 : ℕ) : ZMod D)⁻¹ * (((M+(p.2.val : ℤ)) : ℤ) : ZMod D)

noncomputable def lemma32BurgessMultiplicity (D : ℕ) (M : ℤ) (A N : ℕ) (x : ZMod D) : ℕ :=
  ((lemma32BurgessMultiplierPairs D A N).filter
    (fun p => lemma32BurgessNormalizedResidue D M p=x)).card

lemma lemma32_actual_burgess_multiplicity_mass {D : ℕ} [NeZero D]
    (M : ℤ) (A N : ℕ) :
    (∑ x : ZMod D, lemma32BurgessMultiplicity D M A N x) =
      (lemma32BurgessUnitMultipliers D A).card*N := by
  have he := Finset.card_eq_sum_card_fiberwise
    (s := lemma32BurgessMultiplierPairs D A N) (t := Finset.univ)
    (f := lemma32BurgessNormalizedResidue D M) (fun p hp => Finset.mem_univ _)
  unfold lemma32BurgessMultiplicity
  rw [← he]
  unfold lemma32BurgessMultiplierPairs
  calc
    _ = (lemma32BurgessUnitMultipliers D A).card*(Finset.univ : Finset (Fin N)).card :=
      Finset.card_product _ _
    _ = _ := by rw [Finset.card_univ, Fintype.card_fin]

lemma lemma32_actual_burgess_multiplicity_mass_bound {D : ℕ} [NeZero D]
    (M : ℤ) (A N : ℕ) :
    (∑ x : ZMod D, lemma32BurgessMultiplicity D M A N x) ≤ A*N := by
  rw [lemma32_actual_burgess_multiplicity_mass]
  apply Nat.mul_le_mul_right
  exact (Finset.card_le_card (Finset.filter_subset (fun a : Fin A => (a.val+1).Coprime D)
    Finset.univ)).trans_eq (by simp)

lemma lemma32_actual_burgess_multiplicity_weighted_sum {D : ℕ} [NeZero D]
    (M : ℤ) (A N : ℕ) (F : ZMod D → ℝ) :
    (∑ x : ZMod D, (lemma32BurgessMultiplicity D M A N x : ℝ)*F x) =
      ∑ p ∈ lemma32BurgessMultiplierPairs D A N, F (lemma32BurgessNormalizedResidue D M p) := by
  calc
    _ = ∑ x : ZMod D, ∑ p ∈ (lemma32BurgessMultiplierPairs D A N).filter
        (fun p => lemma32BurgessNormalizedResidue D M p=x),
        F (lemma32BurgessNormalizedResidue D M p) := by
      apply Finset.sum_congr rfl
      intro x hx
      have he : (∑ p ∈ (lemma32BurgessMultiplierPairs D A N).filter
          (fun p => lemma32BurgessNormalizedResidue D M p=x),
          F (lemma32BurgessNormalizedResidue D M p)) =
          ∑ _p ∈ (lemma32BurgessMultiplierPairs D A N).filter
          (fun p => lemma32BurgessNormalizedResidue D M p=x), F x := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
      rw [he]
      simp only [Finset.sum_const, nsmul_eq_mul, lemma32BurgessMultiplicity]
    _ = _ := Finset.sum_fiberwise_of_maps_to (fun p hp => Finset.mem_univ _)
      (fun p => F (lemma32BurgessNormalizedResidue D M p))

end ZhangLS.Spec
