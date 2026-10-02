import ZhangLS.Spec.Lemma32ActualPrimeCurveCount
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_nontrivial_quadratic_odd_characteristic {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1) : ringChar F ≠ 2 := by
  intro hF
  apply hn
  apply MulChar.ext
  intro a
  obtain ⟨b,hb⟩ := FiniteField.isSquare_of_char_two hF (a : F)
  have hb0 : b ≠ 0 := by
    intro h
    rw [h,mul_zero] at hb
    exact a.ne_zero hb
  rw [MulChar.one_apply_coe,hb,map_mul,← pow_two,
    lemma32_quadratic_character_value_square χ hq b hb0]

lemma lemma32_field_two_nonzero_of_odd_characteristic {F : Type*} [Field F]
    (hF : ringChar F ≠ 2) : (2 : F) ≠ 0 := by
  intro h
  apply Ring.neg_one_ne_one_of_char_ne_two hF
  linear_combination -h

lemma lemma32_actual_prime_odd_characteristic {p : ℕ} [Fact p.Prime]
    (χ : RealPrimitiveCharacter p) : ringChar (ZMod p) ≠ 2 :=
  lemma32_nontrivial_quadratic_odd_characteristic χ.chi
    (χ.nontrivial_of_one_lt_modulus (Fact.out : p.Prime).one_lt) χ.quadratic

lemma lemma32_actual_prime_distinct_quartic_point_count {p : ℕ} [Fact p.Prime]
    (χ : RealPrimitiveCharacter p) (a b c d : ZMod p)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d)
    (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d) :
    (∑ x : ZMod p, χ.chi ((x+a)*(x+b)*(x+c)*(x+d)))+1 =
      (Nat.card (lemma32QuarticWeierstrass a b c d).toAffine.Point : ℂ)-(p : ℂ)-1 := by
  have hF := lemma32_actual_prime_odd_characteristic χ
  letI := lemma32_quartic_Weierstrass_isElliptic a b c d
    (lemma32_field_two_nonzero_of_odd_characteristic hF) hab hac had hbc hbd hcd
  exact lemma32_actual_prime_quartic_point_count χ hF a b c d
    (lemma32_cubic_leading_coefficient_nonzero a b c d hab hac had)

end ZhangLS.Spec
