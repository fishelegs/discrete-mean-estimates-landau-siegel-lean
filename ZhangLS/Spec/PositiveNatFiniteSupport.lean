import ZhangLS.Spec.Proposition71PositiveNatSeries

/-! Finite outer support extraction from a positive-index sum. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

/-- A positive-index sum with known finite natural support is a literal
finite sum, with the zero index handled explicitly. -/
theorem positiveNat_tsum_eq_finset {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (f : ℕ+ → E) (S : Finset ℕ) (hS : ∀n : ℕ+, (n : ℕ)∉S → f n=0) :
    (∑'n : ℕ+, f n)=∑n∈S, if hn : 0<n then f ⟨n,hn⟩ else 0 := by
  let g := fun n : ℕ => if hn : 0<n then f ⟨n,hn⟩ else 0
  have hg0 : g 0=0 := by simp [g]
  calc
    _=∑'n : ℕ+, g (n : ℕ) := by
      apply tsum_congr
      intro n
      cases n with
      | mk n hn => simp [g,hn]
    _=∑'n : ℕ, g n := proposition71_positive_nat_tsum g hg0
    _=∑n∈S, g n := tsum_eq_sum (fun n hn => by
      dsimp [g]
      split_ifs with hp
      · exact hS ⟨n,hp⟩ hn
      · rfl)
    _=_ := rfl

end ZhangLS.Spec
