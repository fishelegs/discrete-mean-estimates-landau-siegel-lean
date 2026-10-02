import ZhangLS.Spec.Lemma32BurgessIntervalBoundary
import ZhangLS.Spec.Lemma32BurgessShiftAmplification
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset Complex
open scoped Classical

lemma lemma32_finite_shift_average_bound {I : Type*} (s : Finset I) (f : I → ℂ)
    (z : ℂ) (E : ℝ) (hE : ∀ i ∈ s, ‖z-f i‖ ≤ E) :
    (s.card : ℝ)*‖z‖ ≤ ‖∑ i ∈ s, f i‖+(s.card : ℝ)*E := by
  have he : (s.card : ℂ)*z-(∑ i ∈ s, f i) = ∑ i ∈ s, (z-f i) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hh : ‖(s.card : ℂ)*z-(∑ i ∈ s, f i)‖ ≤ (s.card : ℝ)*E := by
    rw [he]
    calc
      _ ≤ ∑ i ∈ s, ‖z-f i‖ := norm_sum_le _ _
      _ ≤ ∑ _i ∈ s, E := Finset.sum_le_sum hE
      _ = _ := by simp only [Finset.sum_const, nsmul_eq_mul]
  have ht := norm_le_norm_sub_add ((s.card : ℂ)*z) (∑ i ∈ s, f i)
  rw [norm_mul, Complex.norm_natCast] at ht
  linarith

noncomputable def lemma32BurgessShiftIntervalSum {D : ℕ}
    (χ : RealPrimitiveCharacter D) (M : ℤ) (A N B : ℕ) : ℂ :=
  ∑ p ∈ lemma32BurgessMultiplierPairs D A B,
    lemma32BurgessIntervalSum χ (M+(((p.1.val+1)*p.2.val : ℕ) : ℤ)) N

lemma lemma32_actual_shift_interval_double_sum {D : ℕ} (χ : RealPrimitiveCharacter D)
    (M : ℤ) (A N B : ℕ) :
    lemma32BurgessShiftIntervalSum χ M A N B =
      ∑ p ∈ lemma32BurgessMultiplierPairs D A N, ∑ b : Fin B,
        χ.chi ((((M+(p.2.val : ℤ)) : ℤ) : ZMod D)+
          ((p.1.val+1 : ℕ) : ZMod D)*(b.val : ZMod D)) := by
  unfold lemma32BurgessShiftIntervalSum lemma32BurgessMultiplierPairs lemma32BurgessIntervalSum
  change (∑ p ∈ (lemma32BurgessUnitMultipliers D A) ×ˢ (Finset.univ : Finset (Fin B)),
      ∑ i : Fin N, χ.chi ((((M+(((p.1.val+1)*p.2.val : ℕ) : ℤ))+
        (i.val : ℤ)) : ℤ) : ZMod D)) =
    ∑ p ∈ (lemma32BurgessUnitMultipliers D A) ×ˢ (Finset.univ : Finset (Fin N)),
      ∑ b : Fin B, χ.chi ((((M+(p.2.val : ℤ)) : ℤ) : ZMod D)+
        ((p.1.val+1 : ℕ) : ZMod D)*(b.val : ZMod D))
  simp_rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  apply Finset.sum_congr rfl
  intro b hb
  congr 1
  push_cast
  ring

lemma lemma32_actual_shift_interval_norm_bound {D : ℕ} (χ : RealPrimitiveCharacter D)
    (M : ℤ) (A N B : ℕ) :
    ‖lemma32BurgessShiftIntervalSum χ M A N B‖ ≤
      lemma32BurgessShiftAbsoluteSum χ M A N B := by
  rw [lemma32_actual_shift_interval_double_sum]
  exact norm_sum_le _ _

lemma lemma32_actual_burgess_interval_average_bound {D : ℕ}
    (χ : RealPrimitiveCharacter D) (M : ℤ) (A N B : ℕ) (E : ℝ)
    (hE : ∀ a ∈ lemma32BurgessUnitMultipliers D A, ∀ b : Fin B,
      ‖lemma32BurgessIntervalSum χ M N-
        lemma32BurgessIntervalSum χ (M+(((a.val+1)*b.val : ℕ) : ℤ)) N‖ ≤ E) :
    ((lemma32BurgessUnitMultipliers D A).card : ℝ)*(B : ℝ)*
        ‖lemma32BurgessIntervalSum χ M N‖ ≤
      lemma32BurgessShiftAbsoluteSum χ M A N B+
        ((lemma32BurgessUnitMultipliers D A).card : ℝ)*(B : ℝ)*E := by
  have h := lemma32_finite_shift_average_bound (lemma32BurgessMultiplierPairs D A B)
    (fun p => lemma32BurgessIntervalSum χ (M+(((p.1.val+1)*p.2.val : ℕ) : ℤ)) N)
    (lemma32BurgessIntervalSum χ M N) E
    (fun p hp => hE p.1 (Finset.mem_product.mp hp).1 p.2)
  have hc : ((lemma32BurgessMultiplierPairs D A B).card : ℝ) =
      ((lemma32BurgessUnitMultipliers D A).card : ℝ)*(B : ℝ) := by
    unfold lemma32BurgessMultiplierPairs
    have he := Finset.card_product (lemma32BurgessUnitMultipliers D A)
      (Finset.univ : Finset (Fin B))
    exact_mod_cast (by simpa using he :
      ((lemma32BurgessUnitMultipliers D A).product (Finset.univ : Finset (Fin B))).card =
        (lemma32BurgessUnitMultipliers D A).card*B)
  rw [hc] at h
  exact h.trans (add_le_add (lemma32_actual_shift_interval_norm_bound χ M A N B) le_rfl)

end ZhangLS.Spec
