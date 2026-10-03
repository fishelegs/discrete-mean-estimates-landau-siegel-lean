import Mathlib.Data.PNat.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-! # Removing a zero natural-index term before genuine positive-pair reindexing -/
set_option autoImplicit false
namespace ZhangLS.Spec

lemma proposition71_positive_nat_tsum {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ → E) (h0 : f 0=0) : (∑'n : ℕ+, f (n : ℕ))=∑'n : ℕ, f n := by
  apply PNat.coe_injective.tsum_eq
  intro n hn
  have hp : 0<n := Nat.pos_of_ne_zero (by intro hh; subst n; exact hn h0)
  exact ⟨⟨n,hp⟩,rfl⟩

lemma proposition71_positive_nat_summable {E : Type*} [NormedAddCommGroup E]
    [CompleteSpace E] (f : ℕ → E) (hf : Summable f) : Summable (fun n : ℕ+ => f (n : ℕ)) :=
  hf.comp_injective PNat.coe_injective

end ZhangLS.Spec
