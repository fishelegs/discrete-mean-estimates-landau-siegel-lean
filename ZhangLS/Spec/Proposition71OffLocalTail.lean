import ZhangLS.Spec.Proposition71OffLocalMajorant

/-! # Absolute convergence and norm of the literal off-localization subseries -/
set_option autoImplicit false
namespace ZhangLS.Spec
open Complex
set_option maxHeartbeats 2000000

noncomputable def proposition71OffLocalTailConstant : ℝ :=
  (proposition71OffCenterDeltaConstant+2*proposition71LargeDeltaTailConstant)*
    proposition71TauFiveQuadraticMass

lemma proposition71_offlocal_tail_constant_pos : 0<proposition71OffLocalTailConstant := by
  have hC := proposition71_offcenter_delta_constant_pos
  have hC' := proposition71_large_delta_tail_constant_pos
  have hτ := proposition71_tau_five_quadratic_mass_pos
  unfold proposition71OffLocalTailConstant
  positivity

theorem proposition71_actual_offlocal_tail_bound :
    ∃ D₀ : ℕ, 2≤D₀ ∧ ∀ {D r : ℕ} (θ : DirichletCharacter ℂ r),
      D₀≤D → 1<D → 2000≤lemma23PaperL D → ∀ c b B : ℝ, 0≤B →
        ∀ a : ℕ → ℂ, (∀n, ‖a n‖≤B) → ∀ R : ℝ, 1≤R →
          ∀ h d : ℕ, 0<h → r∈primitiveDyadicModuli R →
            ((h*r : ℕ) : ℝ)≤lemma81Cutoff D →
              Summable (proposition71SigmaOffLocalTerm D c b a R h d θ) ∧
                ‖proposition71SigmaOffLocalTail D c b a R h d θ‖≤
                  proposition71OffLocalTailConstant*B*(lemma34Tau 5 d : ℝ)*(h : ℝ)*(r : ℝ)*
                    lemma56PrimeMass D*lemma23PaperP D^4*Real.exp (-lemma23PaperL D^10/2) := by
  obtain ⟨D₀,hD₀,hterm⟩ := proposition71_offlocal_term_majorant
  refine ⟨D₀,hD₀,?_⟩
  intro D r θ hDN hD hL c b B hB a ha R hR h d hh hr hcut
  let K := (proposition71OffCenterDeltaConstant+2*proposition71LargeDeltaTailConstant)*
    B*(lemma34Tau 5 d : ℝ)*((h : ℝ)*(r : ℝ))*lemma56PrimeMass D*
      lemma23PaperP D^4*Real.exp (-lemma23PaperL D^10/2)
  have hC := proposition71_offcenter_delta_constant_pos
  have hC' := proposition71_large_delta_tail_constant_pos
  have hM := lemma56_prime_mass_nonneg D
  have hK : 0≤K := by dsimp [K]; positivity
  have hf := hterm θ hDN hD hL c b B hB a ha R hR h d hh hr hcut
  refine ⟨proposition71_tau_dominated_series_summable hK hf,?_⟩
  have hs := proposition71_tau_dominated_tsum_bound hK hf
  change ‖proposition71SigmaOffLocalTail D c b a R h d θ‖≤K*proposition71TauFiveQuadraticMass at hs
  apply hs.trans_eq
  dsimp [K,proposition71OffLocalTailConstant]
  ring

end ZhangLS.Spec
