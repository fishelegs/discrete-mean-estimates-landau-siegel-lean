import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical

lemma lemma32_short_congruence_class_card {N d : ℕ} (s : Finset (Fin N))
    (hs : ∀ n ∈ s, ∀ m ∈ s, Nat.ModEq d n.val m.val) :
    s.card ≤ N/d+1 := by
  have hc : s.card ≤ (Finset.range (N/d+1)).card := by
    apply Finset.card_le_card_of_injOn (fun n : Fin N => n.val/d)
    · intro n hn
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right n.isLt.le))
    · intro n hn m hm he
      have hmod := hs n hn m hm
      change n.val%d=m.val%d at hmod
      change n.val/d=m.val/d at he
      have h1 := Nat.mod_add_div n.val d
      have h2 := Nat.mod_add_div m.val d
      rw [hmod, he] at h1
      exact Fin.ext (h1.symm.trans h2)
  simpa only [Finset.card_range] using hc

end ZhangLS.Spec
