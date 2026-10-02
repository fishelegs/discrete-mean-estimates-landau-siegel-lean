import ZhangLS.Spec.Proposition71ConductorAggregateOrder
import ZhangLS.Spec.Proposition71OffLocalAggregate
import ZhangLS.Spec.Proposition71LargeConductorAggregate

/-! # Rejoining the actual infinite σ to its genuine localized dyadic mean -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Finset
open scoped Classical
set_option maxHeartbeats 2500000

noncomputable def proposition71FullSigmaConductorBlock (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (X : ℕ) : ℝ :=
  proposition71ConductorNormAggregate X X
    (fun d h r => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D ∧ r∈primitiveDyadicModuli R)
    (fun d h _ θ => proposition71SigmaSeries D c b a h d θ)

lemma proposition71_dhR_le_cutoff {D d h r : ℕ} {R : ℝ}
    (hcut : ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D) (hr : r∈primitiveDyadicModuli R) :
    ((d*h : ℕ) : ℝ)*R≤lemma81Cutoff D := by
  have hRr := (mem_primitiveDyadicModuli.mp hr).2.1
  have hh := mul_le_mul_of_nonneg_left hRr (Nat.cast_nonneg (d*h))
  have he : ((d*h : ℕ) : ℝ)*R≤((d*h*r : ℕ) : ℝ) := by simpa only [Nat.cast_mul] using hh
  exact he.trans hcut.le

/-- The actual strict d h r cutoff and finite conductor range are majorized
by the previously proved complete localized block, with no lost norm terms. -/
lemma proposition71_strict_localized_aggregate_le (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (X : ℕ) :
    proposition71ConductorNormAggregate X X
      (fun d h r => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D ∧ r∈primitiveDyadicModuli R)
      (fun d h _ θ => proposition71SigmaStar D c b a R h d θ)≤
        proposition71LocalizedDyadicAggregate D c b a R X := by
  unfold proposition71ConductorNormAggregate proposition71LocalizedDyadicAggregate
  apply sum_le_sum; intro d hd
  apply sum_le_sum; intro h hh
  let W := fun r : ℕ =>
    ((d : ℝ)*(h : ℝ)*(Nat.totient (h*r) : ℝ)*Real.sqrt (r : ℝ))⁻¹*
      ∑ θ∈(univ : Finset (DirichletCharacter ℂ r)).filter (fun θ => θ.IsPrimitive),
        ‖proposition71SigmaStar D c b a R h d θ‖
  have hW (r : ℕ) : 0≤W r := by dsimp [W]; positivity
  by_cases hcut : ((d*h : ℕ) : ℝ)*R≤lemma81Cutoff D
  · rw [if_pos hcut]
    calc
      _≤∑ r∈(Icc 2 X).filter (fun r => r∈primitiveDyadicModuli R), W r := by
        rw [sum_filter]
        apply sum_le_sum; intro r hr
        by_cases hc : (d : ℝ)*(h : ℝ)*(r : ℝ)<lemma81Cutoff D <;>
          by_cases hm : r∈primitiveDyadicModuli R <;> simp [hc,hm,W] <;> try positivity
      _≤∑ r∈primitiveDyadicModuli R, W r := sum_le_sum_of_subset_of_nonneg
        (fun r hr => (mem_filter.mp hr).2) (fun r hr hnot => hW r)
      _=_ := rfl
  · rw [if_neg hcut]
    apply le_of_eq
    apply sum_eq_zero
    intro r hr
    apply if_neg
    intro hA
    exact hcut (proposition71_dhR_le_cutoff hA.1 hA.2)

/-- The nonlocalized block is controlled by the actual localized block plus
its literal omitted-index aggregate. Absolute convergence is proved inside. -/
theorem proposition71_full_sigma_block_le_local_and_tail :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → 1<D → 2000≤lemma23PaperL D →
      ∀ c b B : ℝ, 0≤B → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) → ∀ R : ℝ, ∀ X : ℕ,
        proposition71FullSigmaConductorBlock D c b a R X≤
          proposition71LocalizedDyadicAggregate D c b a R X+
            proposition71OffLocalConductorAggregate D c b a R X X := by
  obtain ⟨D₀,hD₀,hsum⟩ := proposition71_sigma_series_summable
  refine ⟨D₀,hD₀,?_⟩
  intro D hDN hD hL c b B hB a ha R X
  have hh : proposition71FullSigmaConductorBlock D c b a R X≤
      proposition71ConductorNormAggregate X X
        (fun d h r => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D ∧ r∈primitiveDyadicModuli R)
        (fun d h _ θ => proposition71SigmaStar D c b a R h d θ)+
      proposition71OffLocalConductorAggregate D c b a R X X := by
    apply proposition71_conductor_aggregate_le_add X X _ _ _ _
    intro d hd h hh r hr hA θ hθ
    have hs := hsum θ hDN hD hL c b B hB a ha h d (mem_Icc.mp hh).1
      (by have := (mem_Icc.mp hr).1; omega) (proposition71_hr_le_cutoff_of_dhr (mem_Icc.mp hd).1 hA.1)
    rw [proposition71_sigma_exact_localization c b a R h d θ hs]
    exact norm_add_le _ _
  exact hh.trans (add_le_add (proposition71_strict_localized_aggregate_le D c b a R X) le_rfl)

end ZhangLS.Spec
