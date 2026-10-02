import ZhangLS.Spec.Lemma32RealPrimitiveCRTCharacter
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_real_primitive_integer_CRT_quartic_sum {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (χ : RealPrimitiveCharacter (m*n)) (a b c d : ℤ) :
    (∑ x : ZMod (m*n), χ.chi (lemma32QuarticRootProduct (a : ZMod (m*n)) b c d x)) =
      (∑ x : ZMod m, (lemma32RealCRTLeft h χ).chi
        (lemma32QuarticRootProduct (a : ZMod m) b c d x)) *
      (∑ x : ZMod n, (lemma32RealCRTRight h χ).chi
        (lemma32QuarticRootProduct (a : ZMod n) b c d x)) := by
  have hi (z : ℤ) : ZMod.chineseRemainder h (z : ZMod (m*n)) =
      ((z : ZMod m), (z : ZMod n)) := by
    rw [map_intCast]
    apply Prod.ext
    · exact map_intCast (RingHom.fst (ZMod m) (ZMod n)) z
    · exact map_intCast (RingHom.snd (ZMod m) (ZMod n)) z
  have he := lemma32_real_primitive_CRT_quartic_sum h χ
    (a : ZMod (m*n)) b c d
  dsimp only at he
  rw [hi a, hi b, hi c, hi d] at he
  exact he

lemma lemma32_real_primitive_integer_CRT_quartic_norm {m n : ℕ} [NeZero m] [NeZero n]
    (h : m.Coprime n) (χ : RealPrimitiveCharacter (m*n)) (a b c d : ℤ) :
    ‖∑ x : ZMod (m*n), χ.chi (lemma32QuarticRootProduct (a : ZMod (m*n)) b c d x)‖ =
      ‖∑ x : ZMod m, (lemma32RealCRTLeft h χ).chi
        (lemma32QuarticRootProduct (a : ZMod m) b c d x)‖ *
      ‖∑ x : ZMod n, (lemma32RealCRTRight h χ).chi
        (lemma32QuarticRootProduct (a : ZMod n) b c d x)‖ := by
  rw [lemma32_real_primitive_integer_CRT_quartic_sum, norm_mul]

end ZhangLS.Spec
