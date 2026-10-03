import ZhangLS.Spec.Proposition71DeltaPairs
namespace ZhangLS.Spec
open Complex
open scoped Classical
example (D : ℕ) (Q : ℝ) (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ) (mn : ℕ+×ℕ+) :
    proposition71DeltaPair D Q ∅ κ a w mn=0 := by
  simp [proposition71DeltaPair,proposition71FiniteShortPair]
example (D : ℕ) (Q : ℝ) (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ) (m : ℕ+) :
    proposition71DeltaPair D Q {1} κ a w (m,1)=
      a 1*(κ (m : ℕ)*w (m : ℕ) 1*lemma53PaperDelta D ((m : ℝ)/Q)) := by
  simp [proposition71DeltaPair,proposition71FiniteShortPair]
example {E : Type*} [NormedAddCommGroup E] [CompleteSpace E] (f : ℕ → E) (h0 : f 0=0) :
    (∑'n : ℕ+, f n)=(∑'n : ℕ, f n) := proposition71_positive_nat_tsum f h0
example (D : ℕ) (Q : ℝ) (S : Finset ℕ) (κ a : ℕ → ℂ) (w : ℕ → ℕ → ℂ)
    (mn : ℕ+×ℕ+) (hn : (mn.2 : ℕ)∉S) : proposition71DeltaPair D Q S κ a w mn=0 := by
  simp [proposition71DeltaPair,proposition71FiniteShortPair,hn]
end ZhangLS.Spec
#print axioms ZhangLS.Spec.proposition71FiniteShortPair
#print axioms ZhangLS.Spec.proposition71_finite_short_pair_hasSum
#print axioms ZhangLS.Spec.proposition71_finite_short_pair_summable
#print axioms ZhangLS.Spec.proposition71_positive_nat_tsum
#print axioms ZhangLS.Spec.proposition71_positive_nat_summable
#print axioms ZhangLS.Spec.proposition71DeltaPair
#print axioms ZhangLS.Spec.proposition71_delta_pair_fiber
#print axioms ZhangLS.Spec.proposition71_delta_pairs_summable_and_bound
#print ZhangLS.Spec.proposition71_delta_pairs_summable_and_bound
