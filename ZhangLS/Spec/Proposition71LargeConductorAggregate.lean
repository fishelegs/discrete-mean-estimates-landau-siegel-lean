import ZhangLS.Spec.Proposition71LargeConductorWeights

/-! # The genuine outer d,h sums of the localized large-conductor component

Only pairs capable of meeting the original strict coefficient cutoff occur.
The harmless closed cutoff here majorizes the original strict cutoff. All
actual σ*, primitive characters, and φ(hr) weights are present in the sum.
-/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 500000

noncomputable def proposition71LocalizedDyadicAggregate (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (X : ℕ) : ℝ :=
  ∑ d∈Icc 1 X, ∑ h∈Icc 1 X,
    if ((d*h : ℕ) : ℝ)*R≤lemma81Cutoff D then
      proposition71LocalizedConductorBlock D c b a R h d else 0

lemma proposition71_localized_dyadic_aggregate_nonneg (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (R : ℝ) (X : ℕ) :
    0≤proposition71LocalizedDyadicAggregate D c b a R X := by
  unfold proposition71LocalizedDyadicAggregate
  apply sum_nonneg; intro d hd
  apply sum_nonneg; intro h hh
  split
  · exact proposition71_localized_conductor_block_nonneg D c b a R h d
  · exact le_rfl

/-- The remaining outer arithmetic weights cost precisely a proved seventh
power of a harmonic logarithm. No τ or prime-product factor is suppressed. -/
theorem proposition71_localized_dyadic_aggregate_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D →
      ∀ c b B : ℝ, 0≤B → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
        ∀ R : ℝ, (D : ℝ)^(1/4 : ℝ)≤R → ∀ X : ℕ, 1≤X →
          proposition71LocalizedDyadicAggregate D c b a R X≤
            C*B*lemma23PaperP D^2*(D : ℝ)^(-1/16 : ℝ)*(1+Real.log (X : ℝ))^7 := by
  obtain ⟨C,hC,D₀,hD₀,hblock⟩ := proposition71_localized_conductor_block_bound
  refine ⟨C,hC,D₀,hD₀,?_⟩
  intro D hD c b B hB a ha R hR X hX
  let K := C*B*lemma23PaperP D^2*(D : ℝ)^(-1/16 : ℝ)
  have hK : 0≤K := by dsimp [K]; positivity
  have hterm {d h : ℕ} (hd : d∈Icc 1 X) (hh : h∈Icc 1 X) :
      (if ((d*h : ℕ) : ℝ)*R≤lemma81Cutoff D then
        proposition71LocalizedConductorBlock D c b a R h d else 0)≤
      K*((lemma34Tau 5 d : ℝ)/(d : ℝ))*((lemma34Tau 2 h : ℝ)/(h : ℝ)) := by
    split_ifs with hcut
    · exact (hblock D hD c b B hB a ha R hR d h (mem_Icc.mp hd).1
        (mem_Icc.mp hh).1 hcut).trans
        (mul_le_mul_of_nonneg_left (proposition71_reciprocal_totient_le_tau (mem_Icc.mp hh).1)
          (by positivity))
    · positivity
  unfold proposition71LocalizedDyadicAggregate
  calc
    _≤∑ d∈Icc 1 X, ∑ h∈Icc 1 X,
        K*((lemma34Tau 5 d : ℝ)/(d : ℝ))*((lemma34Tau 2 h : ℝ)/(h : ℝ)) := by
      apply sum_le_sum; intro d hd
      exact sum_le_sum (fun h hh => hterm hd hh)
    _=K*(∑ d∈Icc 1 X, (lemma34Tau 5 d : ℝ)/(d : ℝ))*
        (∑ h∈Icc 1 X, (lemma34Tau 2 h : ℝ)/(h : ℝ)) := by
      simp only [←mul_sum,←sum_mul]
    _≤K*(1+Real.log (X : ℝ))^5*(1+Real.log (X : ℝ))^2 := by
      have h5 := proposition71_tau_harmonic_bound 5 X hX
      have h2 := proposition71_tau_harmonic_bound 2 X hX
      have h50 : 0≤∑ d∈Icc 1 X, (lemma34Tau 5 d : ℝ)/(d : ℝ) := sum_nonneg (fun _ _ => by positivity)
      have h20 : 0≤∑ h∈Icc 1 X, (lemma34Tau 2 h : ℝ)/(h : ℝ) := sum_nonneg (fun _ _ => by positivity)
      gcongr
    _=_ := by dsimp [K]; ring

end ZhangLS.Spec
