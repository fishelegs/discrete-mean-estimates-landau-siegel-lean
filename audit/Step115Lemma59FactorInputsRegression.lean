import ZhangLS.Spec.Lemma59ZeroRemovedShift

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set Filter MeromorphicOn Finset
open scoped Topology Real
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

example : ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 0 < c → ∃ D₀ : ℕ,
    ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D) (ψ : DirichletCharacter ℂ p),
    D₀ ≤ D → Lemma23InPsi1 χ ψ → ∀ {s : ℂ},
      |s.re - 1 / 2| ≤ lemma44PaperAlpha D →
      |s.im - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 10 →
      ‖toMeromorphicNFOn (DirichletCharacter.LFunction ψ / lemma59LocalZeroFactor ψ s.im)
          Set.univ (s + I * (lemma23PaperOffsetOne D c : ℂ)) /
        toMeromorphicNFOn (DirichletCharacter.LFunction ψ / lemma59LocalZeroFactor ψ s.im)
          Set.univ s‖ ≤ C := by
  obtain ⟨C,hC,h⟩ := lemma59_uniform_actual_zero_removed_first_shift
  refine ⟨C,hC,?_⟩
  intro c hc
  obtain ⟨D₀,hD₀⟩ := h c hc
  refine ⟨D₀,?_⟩
  intro D p _ χ ψ hD hψ s hre him
  simpa only [lemma59ZeroRemovedL] using hD₀ χ ψ hD hψ ⟨hre,him⟩

example {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {ρ : ℂ} (hρ : ρ ∈ lemma59LocalZeroFinset θ t) :
    lemma59ZeroRemovedL θ t ρ ≠ 0 ∧
      DirichletCharacter.LFunction θ ρ = lemma59LocalZeroFactor θ t ρ * lemma59ZeroRemovedL θ t ρ := by
  have hm := (lemma59_mem_actual_local_zero_finset θ hθ t ρ).mp hρ
  exact ⟨lemma59_actual_zero_removed_ne_zero θ hθ hm.1, lemma59_actual_zero_factorization θ hθ t ρ⟩

example {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (s w : ℂ) :
    DirichletCharacter.LFunction θ (s + w) / DirichletCharacter.LFunction θ s =
      (∏ ρ ∈ lemma59LocalZeroFinset θ t,
        ((s + w - ρ) / (s - ρ)) ^ analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ) *
      (lemma59ZeroRemovedL θ t (s + w) / lemma59ZeroRemovedL θ t s) := by
  rw [lemma59_actual_L_quotient_factorization θ hθ t s w,
    lemma59_actual_zero_factor_ratio_eq_product θ hθ t s w]

example {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {ℓ : ℂ → ℂ} (hℓ : Lemma59ZeroRemovedLogData θ t ℓ) {z : ℂ}
    (hz : ‖z‖ ≤ (13 / 8 : ℝ)) : ‖ℓ z‖ ≤ 5200 * Real.log (32 * (r : ℝ) * (4 + |t|)) := by
  exact lemma59_actual_zero_removed_log_closed_bound θ hθ hℓ
    (mem_closedBall_zero_iff.mpr hz)

example {D r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1)
    {t : ℝ} {ρ : ℂ} (ht : |t - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 10)
    (hρ : ρ ∈ lemma59LocalZeroFinset θ t) :
    (1 / 4 : ℝ) ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.re - 1 / 2| < 1 / 2 ∧
      |ρ.im - (lemma23PaperCenter D).im| < lemma23PaperL D ^ 405 + 13 := by
  have hr := lemma59_actual_local_zero_re_bounds θ hθ hρ
  have hx := lemma59_actual_local_zeros_in_extended_region θ hθ ht hρ
  exact ⟨hr.1,hr.2,hx.1,hx.2⟩


#print axioms lemma59_actual_meromorphic_order_eq_nat
#print axioms lemma59_actual_zero_factor_analytic
#print axioms lemma59_actual_zero_factor_order
#print axioms lemma59_actual_zero_removed_order
#print axioms lemma59_actual_zero_removed_analytic
#print axioms lemma59_actual_zero_removed_ne_zero
#print axioms lemma59_actual_zero_removed_eq_quotient
#print axioms lemma59_actual_zero_factorization
#print axioms lemma59_actual_zero_factor_eq_product
#print axioms lemma59_actual_local_multiplicity_eq_count
#print axioms lemma59_actual_zero_factor_center_bound
#print axioms lemma59_actual_zero_factor_outer_lower_bound
#print axioms lemma59_actual_zero_factor_outer_ne_zero
#print axioms lemma59_actual_local_multiplicity_bound
#print axioms lemma59_actual_zero_removed_outer_bound
#print axioms lemma59_actual_zero_removed_closed_disk_bound
#print axioms lemma59_actual_zero_removed_center_lower_bound
#print axioms lemma59_jensen_log_size_pos
#print axioms lemma59_zero_removed_ratio_bound_gt_one
#print axioms lemma59_actual_zero_removed_ratio_bound
#print axioms lemma59_actual_zero_removed_log_ratio_bound
#print axioms lemma59_actual_zero_removed_log_exists
#print axioms lemma59_actual_zero_removed_log_hasDerivAt
#print axioms lemma59_actual_zero_removed_log_closed_bound
#print axioms lemma59_actual_zero_removed_log_cauchy_bound
#print axioms lemma59_actual_zero_removed_logDeriv_near_center_bound
#print axioms lemma59_actual_zero_removed_shift_norm_bound
#print axioms lemma59_original_shift_path_near_center
#print axioms lemma59_uniform_actual_zero_removed_first_shift
#print axioms lemma59_actual_L_quotient_factorization
#print axioms lemma59_actual_zero_factor_ratio_eq_product
#print axioms lemma59_actual_local_zero_re_bounds
#print axioms lemma59_actual_local_zeros_in_extended_region

end ZhangLS.Spec
