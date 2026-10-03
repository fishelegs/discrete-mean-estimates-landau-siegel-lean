import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma finiteFourSum_le_of_subset (S T : Finset ℕ) (hST : S⊆T)
    (F : ℕ → ℕ → ℕ → ℕ → ℝ) (hF : ∀a b c d,0≤F a b c d) :
    (∑a∈S,∑b∈S,∑c∈S,∑d∈S,F a b c d)≤
      ∑a∈T,∑b∈T,∑c∈T,∑d∈T,F a b c d := by
  calc
    _≤∑a∈S,∑b∈S,∑c∈S,∑d∈T,F a b c d := by
      apply sum_le_sum; intro a ha
      apply sum_le_sum; intro b hb
      apply sum_le_sum; intro c hc
      exact sum_le_sum_of_subset_of_nonneg hST (fun d hd hn => hF a b c d)
    _≤∑a∈S,∑b∈S,∑c∈T,∑d∈T,F a b c d := by
      apply sum_le_sum; intro a ha
      apply sum_le_sum; intro b hb
      exact sum_le_sum_of_subset_of_nonneg hST (fun c hc hn => sum_nonneg (fun d hd => hF a b c d))
    _≤∑a∈S,∑b∈T,∑c∈T,∑d∈T,F a b c d := by
      apply sum_le_sum; intro a ha
      exact sum_le_sum_of_subset_of_nonneg hST (fun b hb hn =>
        sum_nonneg (fun c hc => sum_nonneg (fun d hd => hF a b c d)))
    _≤_ := sum_le_sum_of_subset_of_nonneg hST (fun a ha hn =>
      sum_nonneg (fun b hb => sum_nonneg (fun c hc => sum_nonneg (fun d hd => hF a b c d))))

end ZhangLS.Spec
