import ZhangLS.Spec.Proposition71ConductorAggregateOrder

/-! # Exact upper-conductor restriction in the finite original majorant -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

lemma proposition71_conductor_aggregate_upper_restrict (X Q H : ℕ)
    (A : ℕ → ℕ → ℕ → Prop)
    (F : (d h r : ℕ) → DirichletCharacter ℂ r → ℂ) :
    proposition71ConductorNormAggregate X Q (fun d h r => A d h r ∧ r≤H) F≤
      proposition71ConductorNormAggregate X H A F := by
  unfold proposition71ConductorNormAggregate
  apply sum_le_sum; intro d hd
  apply sum_le_sum; intro h hh
  let W := fun r : ℕ => if A d h r then
    ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹*
      ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive), ‖F d h r θ‖ else 0
  have hW (r : ℕ) : 0≤W r := by dsimp [W]; split <;> positivity
  calc
    _≤∑ r∈(Icc 2 Q).filter (fun r => r≤H), W r := by
      rw [sum_filter]
      apply sum_le_sum; intro r hr
      by_cases ha : A d h r <;> by_cases hb : r≤H <;> simp [ha,hb,W]
    _≤∑ r∈Icc 2 H, W r := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro r hr
        have hh := mem_filter.mp hr
        exact mem_Icc.mpr ⟨(mem_Icc.mp hh.1).1,hh.2⟩
      · intro r hr hnot; exact hW r
    _=_ := rfl

end ZhangLS.Spec
