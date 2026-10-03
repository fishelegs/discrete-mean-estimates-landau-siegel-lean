import ZhangLS.Spec.Lemma84BoundaryHarmonic

/-! Closed moving layers for the genuine arithmetic weight. This extends only
an endpoint in an already quantified weight estimate, not a smoothing theorem
or a profile class. In particular it is not a proof of a tent Gram attachment. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

/-- Every fixed-product layer has at most one d for each r; its reciprocal
r-square factor supplies the uniform bound, without any count of divisors. -/
theorem actualGram_weight_product_endpoint {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (S : Finset (ℕ×ℕ)) (N : ℕ)
    (hS : S ⊆ (Icc 1 N)×ˢ(Icc 1 N)) {Q y : ℝ} (hy : 1<y)
    (hlog : Real.log Q ≤ y)
    (hend : ∀ a ∈ S, ((a.1*a.2 : ℕ) : ℝ) = Q) :
    (∑ a ∈ S, ‖lemma84Section8Weight χ c j a.1 a.2‖) ≤ 2*lemma84WeightScale y := by
  have hinj : Set.InjOn Prod.snd (S : Set (ℕ×ℕ)) := by
    intro a ha b hb hab
    apply Prod.ext _ hab
    have hm : a.1*a.2 = b.1*b.2 := by exact_mod_cast (hend a ha).trans (hend b hb).symm
    have hr : 0 < b.2 := (mem_Icc.mp (mem_product.mp (hS hb)).2).1
    rw [hab] at hm
    nlinarith
  have he : (∑ r ∈ S.image Prod.snd, (r : ℝ)⁻¹^2) =
      ∑ a ∈ S, (a.2 : ℝ)⁻¹^2 := sum_image hinj
  calc
    _ ≤ ∑ a ∈ S, lemma84WeightScale y*(a.2 : ℝ)⁻¹^2 := by
      apply sum_le_sum
      intro a ha
      obtain ⟨hd, hr⟩ := mem_product.mp (hS ha)
      have hd0 := (mem_Icc.mp hd).1
      have hr0 := (mem_Icc.mp hr).1
      have hweight := lemma84_actual_weight_bound χ c j hd0 hr0 hy (by rw [hend a ha]; exact hlog)
      have hdinv : (a.1 : ℝ)⁻¹ ≤ 1 := by
        have hd1 : (1 : ℝ) ≤ a.1 := by exact_mod_cast hd0
        simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ)<1) hd1
      calc
        _ ≤ lemma84WeightScale y*(a.1 : ℝ)⁻¹*(a.2 : ℝ)⁻¹^2 := hweight
        _ ≤ lemma84WeightScale y*1*(a.2 : ℝ)⁻¹^2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hdinv
            (lemma84_weight_scale_nonneg y)) (sq_nonneg _)
        _ = _ := by ring
    _ = lemma84WeightScale y * ∑ r ∈ S.image Prod.snd, (r : ℝ)⁻¹^2 := by
      rw [he, mul_sum]
    _ ≤ lemma84WeightScale y * 2 := mul_le_mul_of_nonneg_left
      (lemma84_finite_reciprocal_square _) (lemma84_weight_scale_nonneg y)
    _ = _ := by ring

/-- All endpoints of a moving band, with the same actual lambda/mu/chi/phi.
The extra unit pays the upper endpoint uniformly in Q,T,D and the finite set. -/
theorem actualGram_actual_weight_closed_layer {D : ℕ} (χ : RealPrimitiveCharacter D)
    (c : ℝ) (j : Fin 3) (S : Finset (ℕ×ℕ)) (N : ℕ)
    (hS : S ⊆ (Icc 1 N)×ˢ(Icc 1 N)) {Q T y : ℝ}
    (hQ : 0<Q) (hT : 1≤T) (hy : 1<y) (hlog : Real.log Q≤y)
    (hband : ∀ a ∈ S, Q/T≤(a.1*a.2 : ℕ) ∧ ((a.1*a.2 : ℕ) : ℝ)≤Q) :
    (∑ a ∈ S, ‖lemma84Section8Weight χ c j a.1 a.2‖) ≤
      2*lemma84WeightScale y*(3+Real.log T) := by
  let A := S.filter (fun a => ((a.1*a.2 : ℕ) : ℝ)<Q)
  let E := S.filter (fun a => ¬ ((a.1*a.2 : ℕ) : ℝ)<Q)
  have hA : A ⊆ (Icc 1 N)×ˢ(Icc 1 N) := (filter_subset _ _).trans hS
  have hE : E ⊆ (Icc 1 N)×ˢ(Icc 1 N) := (filter_subset _ _).trans hS
  have ha := lemma84_actual_weight_layer χ c j A N hA hQ hT hy hlog (by
    intro a ha
    have ham := mem_filter.mp ha
    exact ⟨(hband a ham.1).1, ham.2⟩)
  have he := actualGram_weight_product_endpoint χ c j E N hE hy hlog (by
    intro a ha
    have ham := mem_filter.mp ha
    exact le_antisymm (hband a ham.1).2 (not_lt.mp ham.2))
  have hs : (∑ a ∈ A, ‖lemma84Section8Weight χ c j a.1 a.2‖) +
      (∑ a ∈ E, ‖lemma84Section8Weight χ c j a.1 a.2‖) =
      ∑ a ∈ S, ‖lemma84Section8Weight χ c j a.1 a.2‖ := by
    exact sum_filter_add_sum_filter_not S _ _
  nlinarith

end ZhangLS.Spec
