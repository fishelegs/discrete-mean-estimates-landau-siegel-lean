import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum

set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical

lemma finiteFourSum_norm_sub_le (S : Finset ℕ)
    (f g : ℕ → ℕ → ℕ → ℕ → ℂ) (W : ℕ → ℕ → ℕ → ℕ → ℝ) (F : ℝ)
    (hfg : ∀a∈S,∀b∈S,∀c∈S,∀d∈S,‖f a b c d-g a b c d‖≤F*W a b c d) :
    ‖(∑a∈S,∑b∈S,∑c∈S,∑d∈S,f a b c d)-
      (∑a∈S,∑b∈S,∑c∈S,∑d∈S,g a b c d)‖≤
      F*(∑a∈S,∑b∈S,∑c∈S,∑d∈S,W a b c d) := by
  simp only [←sum_sub_distrib,mul_sum]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro a ha
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro b hb
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro c hc
  apply (norm_sum_le _ _).trans
  apply sum_le_sum; intro d hd
  exact hfg a ha b hb c hc d hd

end ZhangLS.Spec
