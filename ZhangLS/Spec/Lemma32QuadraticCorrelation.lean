import ZhangLS.Spec.Lemma32QuarticTrivialBounds
import Mathlib.NumberTheory.JacobiSum.Basic
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma lemma32_quadratic_character_value_square {F : Type*} [Field F] (χ : MulChar F ℂ)
    (hχ : χ^2=1) (a : F) (ha : a ≠ 0) : (χ a)^2=1 := by
  have h := congrArg (fun ψ : MulChar F ℂ => ψ a) hχ
  change (χ^2) a = (1 : MulChar F ℂ) a at h
  rw [χ.pow_apply' two_ne_zero,MulChar.one_apply (isUnit_iff_ne_zero.mpr ha)] at h
  exact h

lemma lemma32_quadratic_character_inverse {F : Type*} [Field F] (χ : MulChar F ℂ)
    (hχ : χ^2=1) : χ⁻¹=χ := by
  rw [pow_two] at hχ
  calc
    _ = χ⁻¹*(χ*χ) := by rw [hχ,mul_one]
    _ = _ := by simp [← mul_assoc]

lemma lemma32_quadratic_two_linear_correlation {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1) (a b : F) (hab : a ≠ b) :
    (∑ x : F, χ ((x+a)*(x+b))) = -1 := by
  have hd : a-b ≠ 0 := sub_ne_zero.mpr hab
  have hc : χ ((a-b)^2*(-1)) = χ (-1) := by
    rw [map_mul,map_pow,lemma32_quadratic_character_value_square χ hq (a-b) hd,one_mul]
  have hb : Function.Bijective (fun y : F => (a-b)*y-a) := by
    constructor
    · intro y z h
      apply mul_left_cancel₀ hd
      linear_combination h
    · intro x
      refine ⟨(x+a)/(a-b),?_⟩
      field_simp <;> ring
  calc
    _ = ∑ y : F, χ ((((a-b)*y-a)+a)*(((a-b)*y-a)+b)) :=
      (Fintype.sum_bijective _ hb _ _ (fun y => rfl)).symm
    _ = χ (-1)*jacobiSum χ χ := by
      unfold jacobiSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y hy
      rw [show (((a-b)*y-a)+a)*(((a-b)*y-a)+b) =
        ((a-b)^2*(-1))*(y*(1-y)) by ring,map_mul,hc,map_mul]
    _ = χ (-1)*(-χ (-1)) := by
      have hj := jacobiSum_nontrivial_inv hn
      rw [lemma32_quadratic_character_inverse χ hq] at hj
      rw [hj]
    _ = -1 := by
      have h := lemma32_quadratic_character_value_square χ hq (-1) (neg_ne_zero.mpr one_ne_zero)
      linear_combination -h

end ZhangLS.Spec
