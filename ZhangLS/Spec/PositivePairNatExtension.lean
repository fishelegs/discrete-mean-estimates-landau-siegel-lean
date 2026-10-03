import ZhangLS.Spec.Proposition71FiniteShortPairs

/-! Zero extension from genuine positive pairs to natural pairs. -/
set_option autoImplicit false
namespace ZhangLS.Spec
open scoped Classical
set_option maxHeartbeats 2000000

def positivePairNatCoe (mn : ℕ+×ℕ+) : ℕ×ℕ := ((mn.1 : ℕ),(mn.2 : ℕ))

lemma positivePairNatCoe_injective : Function.Injective positivePairNatCoe := by
  intro x y h
  apply Prod.ext
  · exact PNat.eq (congrArg Prod.fst h)
  · exact PNat.eq (congrArg Prod.snd h)

lemma positivePairNatCoe_zero_off_range {E : Type*} [Zero E] (F : ℕ×ℕ → E)
    (hzero : ∀a b : ℕ, a*b=0 → F (a,b)=0)
    (mn : ℕ×ℕ) (hmn : mn∉Set.range positivePairNatCoe) : F mn=0 := by
  by_cases hm : 0<mn.1
  · by_cases hn : 0<mn.2
    · exact (hmn ⟨(⟨mn.1,hm⟩,⟨mn.2,hn⟩),rfl⟩).elim
    · have hz : mn.2=0 := by omega
      exact hzero _ _ (by rw [hz,mul_zero])
  · have hz : mn.1=0 := by omega
    exact hzero _ _ (by rw [hz,zero_mul])

lemma positivePairNatCoe_summable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℕ×ℕ → E) (hzero : ∀a b : ℕ, a*b=0 → F (a,b)=0)
    (hF : Summable (F ∘ positivePairNatCoe)) : Summable F :=
  (positivePairNatCoe_injective.summable_iff (positivePairNatCoe_zero_off_range F hzero)).mp hF

lemma positivePairNatCoe_tsum {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]
    (F : ℕ×ℕ → E) (hzero : ∀a b : ℕ, a*b=0 → F (a,b)=0) :
    (∑'mn : ℕ+×ℕ+, F (positivePairNatCoe mn))=∑'mn : ℕ×ℕ,F mn := by
  apply positivePairNatCoe_injective.tsum_eq
  intro mn hmn
  by_contra hh
  exact hmn (positivePairNatCoe_zero_off_range F hzero mn hh)

end ZhangLS.Spec
