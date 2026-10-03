import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Basic

/-! # Exact natural-multiple reindexing, including the zero index

No project target, character, or analytic-kernel module is imported.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Set
open scoped Classical
set_option maxHeartbeats 1000000

lemma proposition71_nat_multiples_tsum {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    {p : ℕ} (hp : 0<p) (f : ℕ → E) :
    (∑'m : ℕ, if p∣m then f m else 0)=∑'l : ℕ, f (p*l) := by
  let F := fun m : ℕ => if p∣m then f m else 0
  have hi : Function.Injective (fun l : ℕ => p*l) := mul_right_injective₀ hp.ne'
  have hs : Function.support F⊆Set.range (fun l : ℕ => p*l) := by
    intro m hm
    have hd : p∣m := by
      by_contra hh
      exact hm (by simp [F,hh])
    obtain ⟨l,hl⟩ := hd
    exact ⟨l,hl.symm⟩
  have he := hi.tsum_eq hs
  simpa only [F,if_pos (dvd_mul_right p _)] using he.symm

lemma proposition71_nat_multiples_summable_iff {E : Type*} [NormedAddCommGroup E]
    {p : ℕ} (hp : 0<p) (f : ℕ → E) :
    Summable (fun m : ℕ => if p∣m then f m else 0) ↔ Summable (fun l : ℕ => f (p*l)) := by
  let F := fun m : ℕ => if p∣m then f m else 0
  have hi : Function.Injective (fun l : ℕ => p*l) := mul_right_injective₀ hp.ne'
  have hz (m : ℕ) (hm : m∉Set.range (fun l : ℕ => p*l)) : F m=0 := by
    have hd : ¬p∣m := by
      rintro ⟨l,hl⟩
      exact hm ⟨l,hl.symm⟩
    simp [F,hd]
  have hh := hi.summable_iff hz
  have he : (F ∘ fun l : ℕ => p*l)=(fun l : ℕ => f (p*l)) := by
    funext l
    simp [F]
  rw [he] at hh
  exact hh.symm

end ZhangLS.Spec
