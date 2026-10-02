import ZhangLS.Spec.Lemma32CollisionTupleCount
import ZhangLS.Spec.Lemma32FourthMomentRemainder
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def lemma32DistinctFourthMoment {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (H : ℕ) : ℝ :=
  ∑ v ∈ (Finset.univ \ lemma32DegenerateQuarticTuples H).filter Function.Injective,
    |lemma32QuarticCorrelation χ v|

lemma lemma32_prime_collision_fourth_moment_bound {p : ℕ} [Fact p.Prime]
    (χ : RealPrimitiveCharacter p) {H : ℕ} (hH : H ≤ p) :
    (∑ v ∈ (Finset.univ \ lemma32DegenerateQuarticTuples H).filter
      (fun v => ¬ Function.Injective v), |lemma32QuarticCorrelation χ v|) ≤
      12*(H : ℝ)^3 := by
  let S : Finset (Fin 4 → Fin H) := (Finset.univ \ lemma32DegenerateQuarticTuples H).filter
    (fun v => ¬ Function.Injective v)
  have hsub : S ⊆ lemma32CollisionQuarticTuples H := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hv).2⟩
  have hc : S.card ≤ 6*H^3 :=
    (Finset.card_le_card hsub).trans (lemma32_collision_quartic_tuple_card H)
  calc
    _ ≤ ∑ _v ∈ S, (2 : ℝ) := by
      apply Finset.sum_le_sum
      intro v hv
      have hm := Finset.mem_filter.mp hv
      exact lemma32_actual_prime_unpaired_collision_correlation χ hH v
        (Finset.mem_sdiff.mp hm.1).2 hm.2
    _ = (S.card : ℝ)*2 := by simp
    _ ≤ ((6*H^3 : ℕ) : ℝ)*2 :=
      mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hc) (by norm_num)
    _ = 12*(H : ℝ)^3 := by push_cast;ring

lemma lemma32_nondegenerate_split_by_injectivity {D : ℕ} [NeZero D]
    (χ : RealPrimitiveCharacter D) (H : ℕ) :
    lemma32NondegenerateFourthMoment χ H =
      (∑ v ∈ (Finset.univ \ lemma32DegenerateQuarticTuples H).filter
        (fun v => ¬ Function.Injective v), |lemma32QuarticCorrelation χ v|)+
      lemma32DistinctFourthMoment χ H := by
  unfold lemma32NondegenerateFourthMoment lemma32DistinctFourthMoment
  exact (Finset.sum_filter_add_sum_filter_not
    (Finset.univ \ lemma32DegenerateQuarticTuples H)
    (fun v => ¬ Function.Injective v) (fun v => |lemma32QuarticCorrelation χ v|)).symm.trans
      (by simp only [not_not])

lemma lemma32_actual_prime_fourth_moment_distinct_reduction {p : ℕ} [Fact p.Prime]
    (χ : RealPrimitiveCharacter p) {H : ℕ} (hH : H ≤ p) :
    lemma32BurgessFourthMoment χ H ≤
      3*(p : ℝ)*(H : ℝ)^2+12*(H : ℝ)^3+lemma32DistinctFourthMoment χ H := by
  have hb := lemma32_actual_fourth_moment_remainder_bound χ H
  rw [lemma32_nondegenerate_split_by_injectivity] at hb
  have hc := lemma32_prime_collision_fourth_moment_bound χ hH
  linarith

end ZhangLS.Spec
