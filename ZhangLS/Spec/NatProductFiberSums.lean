import Mathlib.NumberTheory.LSeries.Convolution

/-! Exact natural-product fiber reindexing, with all zero-product terms
vanishing and the joint series proved summable before fiber exchange. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Set
open scoped Classical
set_option maxHeartbeats 2000000

theorem natProduct_fiber_eq_divisorsAntidiagonal {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] (F : ℕ×ℕ → E)
    (hzero : ∀a b : ℕ, a*b=0 → F (a,b)=0) (n : ℕ) :
    (∑'ab : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}, F ab.val)=
      ∑ab∈n.divisorsAntidiagonal,F ab := by
  by_cases hn : n=0
  · subst n
    have hz (ab : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {0}) : F ab.val=0 :=
      hzero ab.val.1 ab.val.2 ab.property
    simp only [hz,tsum_zero,Nat.divisorsAntidiagonal_zero,sum_empty]
  · have hs : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n}=n.divisorsAntidiagonal := by
      ext p
      simp [hn]
    rw [hs,Finset.tsum_subtype']

/-- Product-fiber summation for a genuine absolutely convergent pair series.
This is the infinite counterpart of the finite divisor-antidiagonal identity. -/
theorem natProduct_summable_divisorsAntidiagonal {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] (F : ℕ×ℕ → E)
    (hF : Summable F) (hzero : ∀a b : ℕ, a*b=0 → F (a,b)=0) :
    Summable (fun n : ℕ => ∑ab∈n.divisorsAntidiagonal,F ab) ∧
      (∑'n : ℕ,∑ab∈n.divisorsAntidiagonal,F ab)=∑'ab : ℕ×ℕ,F ab := by
  have hs := hF.hasSum.tsum_fiberwise (fun p : ℕ×ℕ => p.1*p.2)
  have he : (fun n : ℕ => ∑'ab : (fun p : ℕ×ℕ => p.1*p.2) ⁻¹' {n},F ab.val)=
      (fun n : ℕ => ∑ab∈n.divisorsAntidiagonal,F ab) := by
    funext n
    exact natProduct_fiber_eq_divisorsAntidiagonal F hzero n
  rw [he] at hs
  exact ⟨hs.summable,hs.tsum_eq⟩

end ZhangLS.Spec
