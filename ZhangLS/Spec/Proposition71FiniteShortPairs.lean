import Mathlib.Data.PNat.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Constructions

/-! # Finite-short / infinite-long positive-pair summability

The actual joint series is assembled from its finitely many supported short
fibers using injective embeddings. No rearrangement of an unproved summable
pair series is used.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Set
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def proposition71FiniteShortPair {E : Type*} [Zero E]
    (S : Finset ℕ) (f : ℕ+ → ℕ → E) (mn : ℕ+×ℕ+) : E :=
  if (mn.2 : ℕ)∈S then f mn.1 (mn.2 : ℕ) else 0

/-- The joint positive-pair series has the genuine sum of its finitely many
actual short fibers. This statement establishes summability in a
complete normed group, rather than assuming it for the later gcd bijection. -/
theorem proposition71_finite_short_pair_hasSum {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (f : ℕ+ → ℕ → E)
    (hf : ∀n∈S, Summable (fun m : ℕ+ => f m n)) :
    HasSum (proposition71FiniteShortPair S f) (∑n∈S, ∑'m : ℕ+, f m n) := by
  let slice := fun (n : ℕ) (mn : ℕ+×ℕ+) => if (mn.2 : ℕ)=n then f mn.1 n else 0
  have hs (n : ℕ) (hn : n∈S) : Summable (slice n) ∧
      (∑'mn : ℕ+×ℕ+, slice n mn)=∑'m : ℕ+, f m n := by
    let g := fun m : ℕ+ => (m,(⟨n,hS n hn⟩ : ℕ+))
    have hi : Function.Injective g := by
      intro m m' hh
      exact congrArg Prod.fst hh
    have hc : (slice n ∘ g)=(fun m : ℕ+ => f m n) := by
      funext m
      simp [slice,g]
    have hz (mn : ℕ+×ℕ+) (hmn : mn∉Set.range g) : slice n mn=0 := by
      by_cases he : (mn.2 : ℕ)=n
      · exact (hmn ⟨mn.1,Prod.ext rfl (Subtype.ext he.symm)⟩).elim
      · simp [slice,he]
    have hsum : Summable (slice n) := (hi.summable_iff hz).mp (by
      have hh := hf n hn
      exact hh.congr (fun m => by simp [Function.comp_apply,slice,g]))
    have hsupport : Function.support (slice n)⊆Set.range g := by
      intro mn hmn
      by_contra hh
      exact hmn (hz mn hh)
    refine ⟨hsum,?_⟩
    have ht := hi.tsum_eq hsupport
    calc
      _=∑'m : ℕ+, slice n (g m) := ht.symm
      _=_ := by apply tsum_congr; intro m; simp [slice,g]
  have hpoint (mn : ℕ+×ℕ+) : (∑n∈S, slice n mn)=proposition71FiniteShortPair S f mn := by
    by_cases hn : (mn.2 : ℕ)∈S
    · rw [proposition71FiniteShortPair,if_pos hn]
      calc
        _=slice (mn.2 : ℕ) mn := Finset.sum_eq_single (s := S) (f := fun n => slice n mn) (mn.2 : ℕ)
          (fun n hn hne => by simp [slice,Ne.symm hne]) (fun hnot => (hnot hn).elim)
        _=_ := by simp [slice]
    · rw [proposition71FiniteShortPair,if_neg hn]
      apply sum_eq_zero
      intro n hns
      have he : (mn.2 : ℕ)≠n := by intro hh; exact hn (hh ▸ hns)
      simp [slice,he]
  have hh := hasSum_sum (s := S) (fun n hn => (hs n hn).1.hasSum)
  have hsum : HasSum (proposition71FiniteShortPair S f) (∑n∈S, ∑'mn : ℕ+×ℕ+, slice n mn) := by
    apply hh.congr
    intro T
    apply sum_congr rfl
    intro mn hmn
    exact hpoint mn
  have hv : (∑n∈S, ∑'mn : ℕ+×ℕ+, slice n mn)=(∑n∈S, ∑'m : ℕ+, f m n) :=
    sum_congr rfl (fun n hn => (hs n hn).2)
  rwa [hv] at hsum

lemma proposition71_finite_short_pair_summable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (S : Finset ℕ) (hS : ∀n∈S, 0<n) (f : ℕ+ → ℕ → E)
    (hf : ∀n∈S, Summable (fun m : ℕ+ => f m n)) :
    Summable (proposition71FiniteShortPair S f) := (proposition71_finite_short_pair_hasSum S hS f hf).summable

end ZhangLS.Spec
