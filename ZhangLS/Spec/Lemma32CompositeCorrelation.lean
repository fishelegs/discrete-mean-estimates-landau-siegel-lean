import ZhangLS.Spec.Lemma32SquarefreeCorrelation
import ZhangLS.Spec.Lemma32CorrelationFactorDivisor
import ZhangLS.Spec.Lemma32PrimitiveModulusShape
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_actual_primitive_quartic_composite_bound {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (a b c d : ℤ) :
    ‖∑ x : ZMod D, χ.chi (lemma32QuarticRootProduct (a : ZMod D) b c d x)‖ ≤
      8 * lemma32SquarefreeCorrelationFactor D (lemma32IntegerRootDifferenceProduct a b c d) := by
  obtain ⟨e, m, he, hmOdd, hmSf, hD⟩ := lemma32_real_primitive_modulus_shape χ
  subst D
  have hmPos : 0 < m := Nat.pos_of_mul_pos_left χ.modulus_pos
  letI : NeZero m := ⟨hmPos.ne'⟩
  letI : NeZero (2^e) := ⟨pow_ne_zero _ (by decide)⟩
  have hc : (2^e).Coprime m := hmOdd.coprime_two_left.pow_left e
  have hpow : (2^e : ℕ) ≤ 8 := by
    calc
      _ ≤ 2^3 := Nat.pow_le_pow_right (by decide) he
      _ = 8 := by decide
  have hl := lemma32_actual_quartic_sum_trivial_norm (lemma32RealCRTLeft hc χ)
    (a : ZMod (2^e)) b c d
  have hr := lemma32_actual_squarefree_quartic_correlation_bound
    (lemma32RealCRTRight hc χ) hmSf a b c d
  have hl8 : ‖∑ x : ZMod (2^e), (lemma32RealCRTLeft hc χ).chi
      (lemma32QuarticRootProduct (a : ZMod (2^e)) b c d x)‖ ≤ 8 :=
    hl.trans (by exact_mod_cast hpow)
  calc
    _ = ‖∑ x : ZMod (2^e), (lemma32RealCRTLeft hc χ).chi
        (lemma32QuarticRootProduct (a : ZMod (2^e)) b c d x)‖ *
        ‖∑ x : ZMod m, (lemma32RealCRTRight hc χ).chi
        (lemma32QuarticRootProduct (a : ZMod m) b c d x)‖ :=
      lemma32_real_primitive_integer_CRT_quartic_norm hc χ a b c d
    _ ≤ 8 * lemma32SquarefreeCorrelationFactor m
        (lemma32IntegerRootDifferenceProduct a b c d) :=
      mul_le_mul hl8 hr (norm_nonneg _) (by norm_num)
    _ ≤ 8 * lemma32SquarefreeCorrelationFactor (2^e*m)
        (lemma32IntegerRootDifferenceProduct a b c d) :=
      mul_le_mul_of_nonneg_left (lemma32_correlation_factor_mono_of_dvd
        χ.modulus_pos (Nat.dvd_mul_left m (2^e))) (by norm_num)

end ZhangLS.Spec
