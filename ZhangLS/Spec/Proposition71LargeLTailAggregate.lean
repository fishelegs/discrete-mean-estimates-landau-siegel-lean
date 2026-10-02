import ZhangLS.Spec.Proposition71OuterTailBudget

/-! # Actual infinite-l truncation error after every conductor weight -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Finset
open scoped Classical
set_option maxHeartbeats 2000000

noncomputable def proposition71LargeLTailAggregate (D : ℕ) (c b : ℝ)
    (a : ℕ → ℂ) (X Q : ℕ) : ℝ :=
  proposition71ConductorNormAggregate X Q
    (fun d h r => ((d*h*r : ℕ) : ℝ)<lemma81Cutoff D)
    (fun d h _ θ => proposition71SigmaLargeLTail D c b a h d θ)

theorem proposition71_large_l_tail_aggregate_bound :
    ∃ C : ℝ, 0<C ∧ ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ D : ℕ, D₀≤D → 1<D →
      2000≤lemma23PaperL D → ∀ c b B : ℝ, 0≤B → ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) →
        ∀ X Q : ℕ, 1≤X → (X : ℝ)≤lemma23PaperP D → (Q : ℝ)≤lemma23PaperP D →
          proposition71LargeLTailAggregate D c b a X Q≤C*B*lemma56PrimeMass D/(D : ℝ) := by
  obtain ⟨D₀,hD₀,htail⟩ := proposition71_large_l_tail_bound
  let C := 2*proposition71LargeDeltaTailConstant*proposition71TauFiveQuadraticMass
  have hC : 0<C := by
    have h1 := proposition71_large_delta_tail_constant_pos
    have h2 := proposition71_tau_five_quadratic_mass_pos
    dsimp [C]; positivity
  refine ⟨C*2^7,by positivity,D₀,hD₀,?_⟩
  intro D hDN hD hL c b B hB a ha X Q hX hXP hQP
  have hM := lemma56_prime_mass_nonneg D
  let K := C*B*lemma56PrimeMass D*lemma23PaperP D^2*Real.exp (-lemma23PaperL D^10/2)
  have hK : 0≤K := by dsimp [K]; positivity
  have hh : proposition71LargeLTailAggregate D c b a X Q≤K*(Q : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7 := by
    apply proposition71_conductor_norm_aggregate_bound X Q hX _ _ hK
    intro d hd h hh r hr hA θ hθ
    have hs := (htail θ hDN hD hL c b B hB a ha h d (mem_Icc.mp hh).1
      (by have := (mem_Icc.mp hr).1; omega) (proposition71_hr_le_cutoff_of_dhr (mem_Icc.mp hd).1 hA)).2
    convert hs using 1 <;> dsimp [C,K] <;> ring
  apply hh.trans
  calc
    _=(C*B*lemma56PrimeMass D)*(lemma23PaperP D^2*Real.exp (-lemma23PaperL D^10/2)*
      (Q : ℝ)^(3/2 : ℝ)*(1+Real.log (X : ℝ))^7) := by dsimp [K]; ring
    _≤(C*B*lemma56PrimeMass D)*(2^7*(D : ℝ)⁻¹) :=
      mul_le_mul_of_nonneg_left (proposition71_outer_tail_budget hD hL hX hXP hQP) (by positivity)
    _=_ := by ring

end ZhangLS.Spec
