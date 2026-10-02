import ZhangLS.Spec.Lemma32CharacterEquivPullback
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32CRTCharacterLeft {m n : ℕ} (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) : DirichletCharacter ℂ m :=
  lemma32ProductCharacterLeft
    (lemma32CharacterEquivPullback (ZMod.chineseRemainder h).symm.toMulEquiv χ)

noncomputable def lemma32CRTCharacterRight {m n : ℕ} (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) : DirichletCharacter ℂ n :=
  lemma32ProductCharacterRight
    (lemma32CharacterEquivPullback (ZMod.chineseRemainder h).symm.toMulEquiv χ)

lemma lemma32_actual_CRT_character_quadratic {m n : ℕ} (h : m.Coprime n)
    (χ : DirichletCharacter ℂ (m*n)) (hq : χ^2=1) :
    (lemma32CRTCharacterLeft h χ)^2=1 ∧ (lemma32CRTCharacterRight h χ)^2=1 := by
  have ht := lemma32_character_equiv_pullback_quadratic
    (ZMod.chineseRemainder h).symm.toMulEquiv χ hq
  exact ⟨lemma32_product_character_left_quadratic _ ht,
    lemma32_product_character_right_quadratic _ ht⟩

lemma lemma32_actual_CRT_quartic_character_sum {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (χ : DirichletCharacter ℂ (m*n)) (a b c d : ZMod (m*n)) :
    let e := ZMod.chineseRemainder h
    (∑ x : ZMod (m*n), χ (lemma32QuarticRootProduct a b c d x)) =
      (∑ x : ZMod m, lemma32CRTCharacterLeft h χ
        (lemma32QuarticRootProduct (e a).1 (e b).1 (e c).1 (e d).1 x))*
      (∑ x : ZMod n, lemma32CRTCharacterRight h χ
        (lemma32QuarticRootProduct (e a).2 (e b).2 (e c).2 (e d).2 x)) := by
  letI : NeZero (m*n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [lemma32_quartic_character_sum_ring_equiv (ZMod.chineseRemainder h)]
  exact lemma32_product_quartic_character_sum _ _ _ _ _

end ZhangLS.Spec
