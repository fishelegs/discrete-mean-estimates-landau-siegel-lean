import ZhangLS.Spec.Proposition71ConductorAggregateAlgebra

/-! # Finite order and covering operations for the genuine conductor majorant -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_conductor_aggregate_mono (X Q : ℕ)
    (A B : ℕ → ℕ → ℕ → Prop)
    (F G : (d h r : ℕ) → DirichletCharacter ℂ r → ℂ)
    (hFG : ∀d∈Icc 1 X, ∀h∈Icc 1 X, ∀r∈Icc 2 Q, A d h r →
      B d h r ∧ ∀ θ : DirichletCharacter ℂ r, θ.IsPrimitive → ‖F d h r θ‖≤‖G d h r θ‖) :
    proposition71ConductorNormAggregate X Q A F≤proposition71ConductorNormAggregate X Q B G := by
  unfold proposition71ConductorNormAggregate
  apply sum_le_sum; intro d hd
  apply sum_le_sum; intro h hh
  apply sum_le_sum; intro r hr
  by_cases hA : A d h r
  · have he := hFG d hd h hh r hr hA
    rw [if_pos hA,if_pos he.1]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sum_le_sum (fun θ hθ => he.2 θ (mem_filter.mp hθ).2)
  · rw [if_neg hA]
    split <;> positivity

lemma proposition71_conductor_aggregate_le_add (X Q : ℕ)
    (A : ℕ → ℕ → ℕ → Prop)
    (F G H : (d h r : ℕ) → DirichletCharacter ℂ r → ℂ)
    (hFGH : ∀d∈Icc 1 X, ∀h∈Icc 1 X, ∀r∈Icc 2 Q, A d h r →
      ∀ θ : DirichletCharacter ℂ r, θ.IsPrimitive → ‖F d h r θ‖≤‖G d h r θ‖+‖H d h r θ‖) :
    proposition71ConductorNormAggregate X Q A F≤
      proposition71ConductorNormAggregate X Q A G+proposition71ConductorNormAggregate X Q A H := by
  unfold proposition71ConductorNormAggregate
  simp only [←sum_add_distrib]
  apply sum_le_sum; intro d hd
  apply sum_le_sum; intro h hh
  apply sum_le_sum; intro r hr
  split_ifs with hA
  · rw [←mul_add,←sum_add_distrib]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact sum_le_sum (fun θ hθ => hFGH d hd h hh r hr hA θ (mem_filter.mp hθ).2)
  · simp

lemma proposition71_conductor_aggregate_predicate_split (X Q : ℕ)
    (A B : ℕ → ℕ → ℕ → Prop)
    (F : (d h r : ℕ) → DirichletCharacter ℂ r → ℂ) :
    proposition71ConductorNormAggregate X Q A F=
      proposition71ConductorNormAggregate X Q (fun d h r => A d h r ∧ B d h r) F+
        proposition71ConductorNormAggregate X Q (fun d h r => A d h r ∧ ¬B d h r) F := by
  unfold proposition71ConductorNormAggregate
  simp only [←sum_add_distrib]
  apply sum_congr rfl; intro d hd
  apply sum_congr rfl; intro h hh
  apply sum_congr rfl; intro r hr
  by_cases ha : A d h r <;> by_cases hb : B d h r <;> simp [ha,hb]

/-- A genuine finite cover costs at most the sum of its actual filtered
majorants. Disjointness is not needed for this nonnegative upper bound. -/
theorem proposition71_conductor_aggregate_cover {ι : Type*} (S : Finset ι) (X Q : ℕ)
    (A : ℕ → ℕ → ℕ → Prop) (B : ι → ℕ → ℕ → ℕ → Prop)
    (F : (d h r : ℕ) → DirichletCharacter ℂ r → ℂ)
    (hcover : ∀d∈Icc 1 X, ∀h∈Icc 1 X, ∀r∈Icc 2 Q, A d h r → ∃i∈S, B i d h r) :
    proposition71ConductorNormAggregate X Q A F≤
      ∑ i∈S, proposition71ConductorNormAggregate X Q (B i) F := by
  let G := fun (i : ι) (d h r : ℕ) =>
    if B i d h r then
      ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹*
        ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), ‖F d h r θ‖
    else 0
  have hG (i : ι) (d h r : ℕ) : 0≤G i d h r := by dsimp [G]; split <;> positivity
  calc
    _≤∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 2 Q, ∑ i∈S, G i d h r := by
      unfold proposition71ConductorNormAggregate
      apply sum_le_sum; intro d hd
      apply sum_le_sum; intro h hh
      apply sum_le_sum; intro r hr
      split_ifs with hA
      · obtain ⟨i,hi,hBi⟩ := hcover d hd h hh r hr hA
        have he := single_le_sum (fun j hj => hG j d h r) hi
        simpa only [G,if_pos hBi] using he
      · exact sum_nonneg (fun i hi => hG i d h r)
    _=∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ i∈S, ∑ r∈Icc 2 Q, G i d h r := by
      apply sum_congr rfl; intro d hd
      apply sum_congr rfl; intro h hh
      exact sum_comm
    _=∑ d∈Icc 1 X, ∑ i∈S, ∑ h∈Icc 1 X, ∑ r∈Icc 2 Q, G i d h r := by
      apply sum_congr rfl; intro d hd
      exact sum_comm
    _=∑ i∈S, ∑ d∈Icc 1 X, ∑ h∈Icc 1 X, ∑ r∈Icc 2 Q, G i d h r := sum_comm
    _=_ := rfl

end ZhangLS.Spec
