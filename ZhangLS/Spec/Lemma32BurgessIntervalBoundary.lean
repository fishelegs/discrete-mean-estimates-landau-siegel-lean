import ZhangLS.Spec.Lemma32BurgessShiftCharacter
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma32_burgess_interval_sum_eq_range {D : ℕ} (χ : RealPrimitiveCharacter D)
    (M : ℤ) (N : ℕ) :
    lemma32BurgessIntervalSum χ M N =
      ∑ i ∈ Finset.range N, χ.chi (((M+(i : ℤ)) : ℤ) : ZMod D) := by
  exact Fin.sum_univ_eq_sum_range (fun i => χ.chi (((M+(i : ℤ)) : ℤ) : ZMod D)) N

lemma lemma32_burgess_interval_sum_add {D : ℕ} (χ : RealPrimitiveCharacter D)
    (M : ℤ) (N H : ℕ) :
    lemma32BurgessIntervalSum χ M (N+H) = lemma32BurgessIntervalSum χ M N +
      lemma32BurgessIntervalSum χ (M+(N : ℤ)) H := by
  simp only [lemma32_burgess_interval_sum_eq_range, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  push_cast
  ring

lemma lemma32_burgess_interval_shift_boundary {D : ℕ} (χ : RealPrimitiveCharacter D)
    (M : ℤ) (N H : ℕ) :
    lemma32BurgessIntervalSum χ (M+(H : ℤ)) N-lemma32BurgessIntervalSum χ M N =
      lemma32BurgessIntervalSum χ (M+(N : ℤ)) H-lemma32BurgessIntervalSum χ M H := by
  have h1 := lemma32_burgess_interval_sum_add χ M N H
  have h2 := lemma32_burgess_interval_sum_add χ M H N
  rw [Nat.add_comm H N] at h2
  linear_combination h1-h2

lemma lemma32_burgess_interval_shift_error {D : ℕ} (χ : RealPrimitiveCharacter D)
    (M : ℤ) (N H : ℕ) :
    ‖lemma32BurgessIntervalSum χ (M+(H : ℤ)) N-lemma32BurgessIntervalSum χ M N‖ ≤
      ‖lemma32BurgessIntervalSum χ (M+(N : ℤ)) H‖+
        ‖lemma32BurgessIntervalSum χ M H‖ := by
  rw [lemma32_burgess_interval_shift_boundary]
  exact norm_sub_le _ _

end ZhangLS.Spec
