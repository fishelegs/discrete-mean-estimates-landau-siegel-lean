import ZhangLS.Spec.Lemma32ActualCollisionBound
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_quartic_noninjective_iff_collision {α : Type*} (v : Fin 4 → α) :
    ¬ Function.Injective v ↔
      v 0=v 1 ∨ v 0=v 2 ∨ v 0=v 3 ∨ v 1=v 2 ∨ v 1=v 3 ∨ v 2=v 3 := by
  constructor
  · intro hr
    by_contra h
    apply hr
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro h hi
    rcases h with h | h | h | h | h | h
    all_goals have he := hi h
    all_goals have hv := congrArg Fin.val he
    all_goals norm_num at hv

noncomputable def lemma32CollisionQuarticTuples (H : ℕ) : Finset (Fin 4 → Fin H) :=
  Finset.univ.filter (fun v => ¬ Function.Injective v)

def lemma32QuarticCollisionFamily {H : ℕ} (j : Fin 6) (u : Fin 3 → Fin H) :
    Fin 4 → Fin H :=
  ![![u 0,u 0,u 1,u 2], ![u 0,u 1,u 0,u 2], ![u 0,u 1,u 2,u 0],
    ![u 0,u 1,u 1,u 2], ![u 0,u 1,u 2,u 1], ![u 0,u 1,u 2,u 2]] j

lemma lemma32_collision_tuples_covered (H : ℕ) :
    lemma32CollisionQuarticTuples H ⊆ Finset.univ.biUnion
      (fun j : Fin 6 => Finset.univ.image (lemma32QuarticCollisionFamily j)) := by
  intro v hv
  have hr := (lemma32_quartic_noninjective_iff_collision v).mp
    ((Finset.mem_filter.mp hv).2)
  rcases hr with h | h | h | h | h | h
  · apply Finset.mem_biUnion.mpr
    refine ⟨0,Finset.mem_univ _,Finset.mem_image.mpr ⟨![v 0,v 2,v 3],Finset.mem_univ _,?_⟩⟩
    ext i
    fin_cases i <;> simp_all [lemma32QuarticCollisionFamily]
  · apply Finset.mem_biUnion.mpr
    refine ⟨1,Finset.mem_univ _,Finset.mem_image.mpr ⟨![v 0,v 1,v 3],Finset.mem_univ _,?_⟩⟩
    ext i
    fin_cases i <;> simp_all [lemma32QuarticCollisionFamily]
  · apply Finset.mem_biUnion.mpr
    refine ⟨2,Finset.mem_univ _,Finset.mem_image.mpr ⟨![v 0,v 1,v 2],Finset.mem_univ _,?_⟩⟩
    ext i
    fin_cases i <;> simp_all [lemma32QuarticCollisionFamily]
  · apply Finset.mem_biUnion.mpr
    refine ⟨3,Finset.mem_univ _,Finset.mem_image.mpr ⟨![v 0,v 1,v 3],Finset.mem_univ _,?_⟩⟩
    ext i
    fin_cases i <;> simp_all [lemma32QuarticCollisionFamily]
  · apply Finset.mem_biUnion.mpr
    refine ⟨4,Finset.mem_univ _,Finset.mem_image.mpr ⟨![v 0,v 1,v 2],Finset.mem_univ _,?_⟩⟩
    ext i
    fin_cases i <;> simp_all [lemma32QuarticCollisionFamily]
  · apply Finset.mem_biUnion.mpr
    refine ⟨5,Finset.mem_univ _,Finset.mem_image.mpr ⟨![v 0,v 1,v 2],Finset.mem_univ _,?_⟩⟩
    ext i
    fin_cases i <;> simp_all [lemma32QuarticCollisionFamily]

lemma lemma32_collision_quartic_tuple_card (H : ℕ) :
    (lemma32CollisionQuarticTuples H).card ≤ 6*H^3 := by
  calc
    _ ≤ (Finset.univ.biUnion (fun j : Fin 6 =>
        Finset.univ.image (lemma32QuarticCollisionFamily j))).card :=
      Finset.card_le_card (lemma32_collision_tuples_covered H)
    _ ≤ ∑ j : Fin 6, (Finset.univ.image (lemma32QuarticCollisionFamily j)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _j : Fin 6, H^3 := by
      apply Finset.sum_le_sum
      intro j hj
      calc
        _ ≤ (Finset.univ : Finset (Fin 3 → Fin H)).card := Finset.card_image_le
        _ = H^3 := by simp
    _ = 6*H^3 := by simp

end ZhangLS.Spec
