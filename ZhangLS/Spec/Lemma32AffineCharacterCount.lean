import ZhangLS.Spec.Lemma32QuadraticCharacterUniqueness
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32CubicAffineSolutions {F : Type*} [Field F] [Fintype F]
    (P : F → F) : Finset (F × F) :=
  Finset.univ.filter (fun v => v.2^2=P v.1)

lemma lemma32_affine_solution_card_fibers {F : Type*} [Field F] [Fintype F]
    (P : F → F) : (lemma32CubicAffineSolutions P).card =
      ∑ x : F, ({y : F | y^2=P x}.toFinset).card := by
  unfold lemma32CubicAffineSolutions
  rw [Finset.card_filter,Fintype.sum_prod_type]
  simp only [Set.toFinset_setOf,Finset.card_filter]

lemma lemma32_quadratic_square_root_count {F : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1) (hF : ringChar F ≠ 2) (a : F) :
    (({y : F | y^2=a}.toFinset).card : ℂ) = χ a+1 := by
  rw [lemma32_nontrivial_quadratic_character_canonical_value χ hn hq hF]
  exact_mod_cast quadraticChar_card_sqrts hF a

lemma lemma32_actual_affine_card_character_sum {F : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1) (hF : ringChar F ≠ 2) (P : F → F) :
    ((lemma32CubicAffineSolutions P).card : ℂ) =
      (Fintype.card F : ℂ)+(∑ x : F, χ (P x)) := by
  rw [lemma32_affine_solution_card_fibers,Nat.cast_sum]
  calc
    _ = ∑ x : F, (χ (P x)+1) := by
        apply Finset.sum_congr rfl
        intro x _
        simpa only [Set.toFinset_card,Fintype.card_eq_nat_card] using
          lemma32_quadratic_square_root_count χ hn hq hF (P x)
    _ = (Fintype.card F : ℂ)+(∑ x : F, χ (P x)) := by
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
      ring

lemma lemma32_quartic_character_sum_affine_card {F : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    (χ : MulChar F ℂ) (hn : χ ≠ 1) (hq : χ^2=1) (hF : ringChar F ≠ 2)
    (a b c d : F) (hA : lemma32CubicLeadingCoefficient a b c d ≠ 0) :
    (∑ x : F, χ (lemma32QuarticRootProduct a b c d x)) =
      ((lemma32CubicAffineSolutions (lemma32NormalizedMonicCubic a b c d)).card : ℂ)-
      (Fintype.card F : ℂ)-1 := by
  rw [lemma32_quadratic_quartic_normalized_cubic_sum_identity χ hq a b c d hA,
    lemma32_actual_affine_card_character_sum χ hn hq hF]
  ring

end ZhangLS.Spec
