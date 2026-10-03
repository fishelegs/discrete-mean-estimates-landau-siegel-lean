import ZhangLS.Spec.ShortUpsilonFamilyError

/-! Regressions at the actual closed cutoff, zero endpoint, ramification and original shifts. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace ZhangLS.Spec
open Finset
open scoped Classical

theorem shortUpsilon_regression_closed_cutoff {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (n : ℕ) (hn : n ≤ D^4) :
    lemma83Kappa β n - shortUpsilonKappa χ β n = 0 := by
  rw [shortUpsilon_kappa_residual_formula]
  apply Finset.sum_eq_zero
  intro q hq
  obtain ⟨hq, hlarge⟩ := Finset.mem_filter.mp hq
  have hprod := (Nat.mem_divisorsAntidiagonal.mp hq).1
  have hq2 := Nat.pos_of_ne_zero (Nat.right_ne_zero_of_mem_divisorsAntidiagonal hq)
  have hq1le : q.1 ≤ n := by
    simpa only [hprod] using Nat.le_mul_of_pos_right q.1 hq2
  omega

theorem shortUpsilon_regression_empty_energy {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) : shortUpsilonErrorEnergy χ β 0 = 0 := by
  simp [shortUpsilonErrorEnergy]

theorem shortUpsilon_regression_cutoff_energy {D : ℕ} (χ : RealPrimitiveCharacter D)
    (β : Fin 3 → ℂ) (N : ℕ) (hN : N ≤ D^4) :
    shortUpsilonErrorEnergy χ β N = 0 := by
  unfold shortUpsilonErrorEnergy
  apply Finset.sum_eq_zero
  intro n hn
  rw [shortUpsilon_regression_closed_cutoff χ β n ((Finset.mem_Icc.mp hn).2.trans hN)]
  simp

theorem shortUpsilon_regression_ramified_local {D p : ℕ} (χ : RealPrimitiveCharacter D)
    (hp : p.Prime) (hχ : χ.evalNat p = 0) :
    lemma23UpsilonArithmeticFunction χ p = -1 ∧
    lemma23UpsilonArithmeticFunction χ (p^2) = 0 ∧
    (∀ k : ℕ, lemma23UpsilonArithmeticFunction χ (p^(k+3)) = 0) ∧
    (∀ k : ℕ, lemma23NuArithmeticFunction χ (p^k) = 1) := by
  refine ⟨?_, ?_, lemma36_upsilon_prime_power_ge_three χ hp, ?_⟩
  · simp [lemma36_upsilon_prime χ hp, hχ]
  · simp [lemma36_upsilon_prime_square χ hp, hχ]
  · intro k
    rw [lemma31_actual_nu_prime_power χ hp, hχ]
    simp [zero_pow_eq]

/-- Original paper shifts are accepted without an extra relation hypothesis. -/
theorem shortUpsilon_regression_original_shifts_full_endpoint :
    ∃ D₀ : ℕ, ∀ D : ℕ, D₀ ≤ D → ∀ χ : RealPrimitiveCharacter D,
      NormalizedAssumptionA χ → ∀ c : ℝ,
        shortUpsilonErrorEnergy χ (lemma83PaperBeta D c) ⌊lemma23PaperP D^2⌋₊ ≤
          36*3^40*lemma23PaperL D^(-640 : ℤ) := by
  obtain ⟨D₀, hD₀⟩ := shortUpsilon_uniform_actual_error_energy
  refine ⟨D₀, ?_⟩
  intro D hD χ hA c
  exact (hD₀ D hD χ hA (lemma83PaperBeta D c) (lemma83_beta_re D c) _ le_rfl).2

end ZhangLS.Spec
