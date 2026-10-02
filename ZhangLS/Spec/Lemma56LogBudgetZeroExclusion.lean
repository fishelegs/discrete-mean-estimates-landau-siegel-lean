import ZhangLS.Spec.Lemma56GeneralRepulsionBudget

/-! # Actual zero exclusion from proved logarithmic budgets

Actual L-functions and their actual zeros and analytic orders are retained.
The original finite prime-window target remains a separate unproved obligation.
-/

namespace ZhangLS.Spec
open Complex Metric Set Finset Filter
open scoped Real Topology
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096

lemma lemma56_actual_log_budget_zero_exclusion {D q : ℕ} [NeZero q]
    (χ : RealPrimitiveCharacter D) (θ : DirichletCharacter ℂ q)
    (hD : 1 < D) (hL : 2000 ≤ lemma23PaperL D)
    (hC : lemma56RepulsionErrorConstant ≤ lemma23PaperL D)
    (hθ : θ ≠ 1) (htwist : lemma44CharacterTwist χ θ ≠ 1)
    {U : ℝ} (hU : 2000 ≤ U) (hLU : lemma23PaperL D ≤ U)
    (hUL : U ≤ (lemma23PaperL D) ^ 5) {β : ℝ}
    (hβ : 0 < 1 - β) (hclose : 1 - β ≤ 64 * lemma23PaperL D ^ (-2022 : ℤ))
    (hzero : dirichletLFunction χ (β : ℂ) = 0)
    (hderiv : deriv (dirichletLFunction χ) (β : ℂ) ≠ 0)
    (hmem : (β : ℂ) ∈ lemma55LocalZeroFinset χ 0) {ρ : ℂ}
    (hre : 1 - 2 / U < ρ.re)
    (hBθ : lemma56JensenLogSize θ ρ.im ≤ 4 * U)
    (hBtw : letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
      lemma56JensenLogSize (lemma44CharacterTwist χ θ) ρ.im ≤ 4 * U) :
    DirichletCharacter.LFunction θ ρ ≠ 0 := by
  classical
  letI : NeZero (D * q) := ⟨Nat.mul_ne_zero χ.modulus_ne_zero (NeZero.ne q)⟩
  intro hρzero
  have hLp : 0 < lemma23PaperL D := by linarith
  have hUp : 0 < U := by linarith
  have hε : 0 ≤ 2 / U := by positivity
  have hεupper : 2 / U ≤ (1 : ℝ) / 4 := by
    apply (div_le_iff₀ hUp).mpr
    linarith
  have hρ : (⟨2, ρ⟩ : Lemma56TaggedZero) ∈ lemma56FourZeroFinset χ θ ρ.im (β : ℂ) := by
    apply (lemma56_mem_four_zero_finset χ θ ρ.im (β : ℂ) ⟨2, ρ⟩).mpr
    simpa [lemma56ZeroFamily] using lemma56_near_one_zero_in_own_local_disk θ hθ hεupper hre hρzero
  obtain ⟨a₀, ha₀, hmax⟩ := (lemma56FourZeroFinset χ θ ρ.im (β : ℂ)).exists_max_image
    (fun a => ‖lemma56TaggedInverseSquare ρ.im a‖) ⟨⟨2, ρ⟩, hρ⟩
  have hr := (lemma56_actual_tagged_inverse_square_bounds χ θ hD hθ htwist ha₀).1
  have hUlower := (lemma56_near_one_zero_inverse_square_lower_bound θ hθ hε hre hρzero).trans
    (by simpa [lemma56TaggedInverseSquare, lemma55FamilyHeight] using hmax ⟨2, ρ⟩ hρ)
  have hdiv : 2 / U ≤ 2 / lemma23PaperL D := div_le_div_of_nonneg_left (by norm_num) hLp hLU
  have hi : (1 + 2 / lemma23PaperL D)⁻¹ ≤ (1 + 2 / U)⁻¹ :=
    (inv_le_inv₀ (by positivity) (by positivity)).mpr (by linarith)
  have hlower := (pow_le_pow_left₀ (by positivity) hi 2).trans hUlower
  let R := ‖lemma56TaggedInverseSquare ρ.im a₀‖
  let v := (lemma56TaggedInverseSquare ρ.im a₀ / (R : ℂ))⁻¹
  have hv : ‖v‖ ≤ 1 := by
    dsimp [v, R]
    rw [norm_inv, norm_div, norm_real, Real.norm_eq_abs, abs_of_pos hr, div_self hr.ne']
    norm_num
  let J := lemma56GeneralRepulsionDegree U
  have hlo := lemma56_actual_common_maximum_log_detection χ θ hD hL hθ htwist
    hLU hBθ hBtw ha₀ hmax J
  have hupr := lemma56_actual_mixed_remaining_real_upper_bound χ θ hθ htwist hD hL ρ.im
    (by linarith only [hβ] : β ≤ 1) hzero hderiv hmem hr hlower hUp hUlower hv J
  have hup : (lemma56MixedRemainingPower χ θ ρ.im R (β : ℂ) v J).re ≤
      475200 * U + 2 * (1 - β) * (J : ℝ) * ((J : ℝ) + 1) * Real.exp (4 * (J : ℝ) / U) := by
    dsimp only [lemma23PaperL] at hLU
    linarith only [hupr, hLU, hBθ, hBtw]
  have hbudget := lemma56_general_repulsion_strict_budget hL hC hU hUL hβ.le hclose
  exact (not_lt_of_ge hlo) (hup.trans_lt hbudget)

end ZhangLS.Spec
