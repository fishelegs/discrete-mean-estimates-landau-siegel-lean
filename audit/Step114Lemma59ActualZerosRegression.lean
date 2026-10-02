import ZhangLS.Spec.Lemma59LocalZeroBudgets

set_option autoImplicit false
namespace ZhangLS.Spec
open Complex Metric Set MeromorphicOn Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

example : ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p), D₀ ≤ D → Lemma23InPsi1 χ ψ →
    ∀ {t : ℝ}, |t - (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 20 →
      ((∑ᶠ ρ : ℂ, divisor (DirichletCharacter.LFunction ψ)
        (Metric.closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)) ρ : ℤ) : ℝ) ≤
          30 * lemma23PaperL D ^ 9 ∧
      ((lemma59LocalZeroFinset ψ t).card : ℝ) ≤ 30 * lemma23PaperL D ^ 9 := by
  simpa only [lemma59JensenMultiplicityCount] using lemma59_uniform_actual_local_zero_bound

example {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) (ρ : ℂ) :
    ρ ∈ ((divisor (DirichletCharacter.LFunction θ)
      (Metric.closedBall (lemma55JensenCenter t) (7 / 4 : ℝ))).finiteSupport
        (isCompact_closedBall _ _)).toFinset ↔
      ‖ρ - lemma55JensenCenter t‖ ≤ (7 / 4 : ℝ) ∧ DirichletCharacter.LFunction θ ρ = 0 := by
  simpa only [lemma59LocalZeroFinset, mem_closedBall_iff_norm] using
    lemma59_mem_actual_local_zero_finset θ hθ t ρ

example {r : ℕ} [NeZero r] (θ : DirichletCharacter ℂ r) (hθ : θ ≠ 1) (t : ℝ) :
    (∑ᶠ ρ : ℂ, divisor (DirichletCharacter.LFunction θ)
      (Metric.closedBall (lemma55JensenCenter t) (7 / 4 : ℝ)) ρ) =
      ∑ ρ ∈ lemma59LocalZeroFinset θ t,
        (analyticOrderNatAt (DirichletCharacter.LFunction θ) ρ : ℤ) := by
  exact lemma59_actual_multiplicity_count_eq_sum_orders θ hθ t

example : ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p), D₀ ≤ D → Lemma23InPsi1 χ ψ →
      ((lemma59LocalZeroFinset ψ ((lemma23PaperCenter D).im + (lemma23PaperL D ^ 405 + 20))).card : ℝ) ≤
        30 * lemma23PaperL D ^ 9 := by
  obtain ⟨D₀, h⟩ := lemma59_uniform_actual_local_zero_bound
  refine ⟨max D₀ lemma23SectionFourModulusThreshold, ?_⟩
  intro D p _ χ ψ hD hψ
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold (le_trans (le_max_right _ _) hD)
  have hLp : 0 < lemma23PaperL D := by linarith only [hp.1]
  have hx : |((lemma23PaperCenter D).im + (lemma23PaperL D ^ 405 + 20)) -
      (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 20 := by
    rw [add_sub_cancel_left, abs_of_nonneg (by positivity)]
  exact (h χ ψ (le_trans (le_max_left _ _) hD) hψ hx).2

example : ∃ D₀ : ℕ, ∀ {D p : ℕ} [NeZero p] (χ : RealPrimitiveCharacter D)
    (ψ : DirichletCharacter ℂ p), D₀ ≤ D → Lemma23InPsi1 χ ψ →
      ((lemma59LocalZeroFinset ψ ((lemma23PaperCenter D).im - (lemma23PaperL D ^ 405 + 20))).card : ℝ) ≤
        30 * lemma23PaperL D ^ 9 := by
  obtain ⟨D₀, h⟩ := lemma59_uniform_actual_local_zero_bound
  refine ⟨max D₀ lemma23SectionFourModulusThreshold, ?_⟩
  intro D p _ χ ψ hD hψ
  have hp := lemma23_sectionFour_parameters_at_explicit_threshold (le_trans (le_max_right _ _) hD)
  have hLp : 0 < lemma23PaperL D := by linarith only [hp.1]
  have hx : |((lemma23PaperCenter D).im - (lemma23PaperL D ^ 405 + 20)) -
      (lemma23PaperCenter D).im| ≤ lemma23PaperL D ^ 405 + 20 := by
    rw [sub_sub_cancel_left, abs_neg, abs_of_nonneg (by positivity)]
  exact (h χ ψ (le_trans (le_max_left _ _) hD) hψ hx).2


#print axioms lemma59_actual_L_large_disk_bound
#print axioms lemma59_actual_large_disk_multiplicity_bound
#print axioms lemma59_actual_local_divisor_eq_order
#print axioms lemma59_mem_actual_local_zero_finset
#print axioms lemma59_actual_local_zero_order_pos
#print axioms lemma59_actual_multiplicity_count_eq_sum_orders
#print axioms lemma59_actual_local_zero_card_bound
#print axioms lemma59_large_height_bound
#print axioms lemma59_family_modulus_le_two_P
#print axioms lemma59_family_large_disk_log_budget
#print axioms lemma59_family_character_nonprincipal
#print axioms lemma59_uniform_actual_local_zero_bound

end ZhangLS.Spec
