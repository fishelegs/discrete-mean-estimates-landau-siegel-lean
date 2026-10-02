import ZhangLS.Spec.Lemma32ActualOddCurveCount
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_four_distinct_roots_injective {F : Type*} (a b c d : F)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    Function.Injective (![a,b,c,d] : Fin 4 → F) := by
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all

lemma lemma32_four_distinct_roots_field_card {F : Type*} [Fintype F] (a b c d : F)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : 4 ≤ Fintype.card F := by
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective
    (![a,b,c,d] : Fin 4 → F)
    (lemma32_four_distinct_roots_injective a b c d hab hac had hbc hbd hcd)

lemma lemma32_four_distinct_prime_roots_modulus_ge_five {p : ℕ} [Fact p.Prime]
    (a b c d : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) : 5 ≤ p := by
  have h4 : 4 ≤ p := by
    simpa only [ZMod.card] using
      lemma32_four_distinct_roots_field_card a b c d hab hac had hbc hbd hcd
  have hn : p ≠ 4 := by
    intro h
    have hp := (Fact.out : p.Prime)
    rw [h] at hp
    exact (by decide : ¬ Nat.Prime 4) hp
  omega

end ZhangLS.Spec
