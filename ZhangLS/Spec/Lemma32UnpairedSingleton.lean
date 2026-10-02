import ZhangLS.Spec.Lemma32QuarticPermutations
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_unpaired_quartic_tuple_has_singleton {A : Type*} (v : Fin 4 → A)
    (hp : ¬ ((v 0=v 1 ∧ v 2=v 3) ∨ (v 0=v 2 ∧ v 1=v 3) ∨
      (v 0=v 3 ∧ v 1=v 2))) :
    ∃ j : Fin 4, ∀ i : Fin 4, i ≠ j → v j ≠ v i := by
  classical
  by_cases h01 : v 0=v 1 <;> by_cases h02 : v 0=v 2 <;>
    by_cases h03 : v 0=v 3 <;> by_cases h12 : v 1=v 2 <;>
    by_cases h13 : v 1=v 3 <;> by_cases h23 : v 2=v 3
  all_goals solve
    | (refine ⟨0, ?_⟩; intro i hi; fin_cases i <;> simp_all [eq_comm])
    | (refine ⟨1, ?_⟩; intro i hi; fin_cases i <;> simp_all [eq_comm])
    | (refine ⟨2, ?_⟩; intro i hi; fin_cases i <;> simp_all [eq_comm])
    | (refine ⟨3, ?_⟩; intro i hi; fin_cases i <;> simp_all [eq_comm])
    | simp_all [eq_comm]

end ZhangLS.Spec
